/** *************************************************************************************
 * Copyright (c) 2020-2021 Institute of Computing Technology, Chinese Academy of Sciences
 * Copyright (c) 2020-2021 Peng Cheng Laboratory
 *
 * XiangShan is licensed under Mulan PSL v2.
 * You can use this software according to the terms and conditions of the Mulan PSL v2.
 * You may obtain a copy of Mulan PSL v2 at:
 * http://license.coscl.org.cn/MulanPSL2
 *
 * THIS SOFTWARE IS PROVIDED ON AN "AS IS" BASIS, WITHOUT WARRANTIES OF ANY KIND,
 * EITHER EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO NON-INFRINGEMENT,
 * MERCHANTABILITY OR FIT FOR A PARTICULAR PURPOSE.
 *
 * See the Mulan PSL v2 for more details.
 * *************************************************************************************
 */

package coupledL2

import chisel3._
import chisel3.util._
import xs.utils._
import org.chipsalliance.cde.config.Parameters
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tilelink.TLMessages._
import coupledL2.prefetch.PrefetchResp
import xs.utils.perf.HasPerfLogging

// record info of those with Grant sent, yet GrantAck not received
// used to block Probe upwards
class InflightGrantEntry(implicit p: Parameters) extends L2Bundle {
  val set   = UInt(setBits.W)
  val tag   = UInt(tagBits.W)
}

class TaskWithData(implicit p: Parameters) extends L2Bundle {
  val task = new TaskBundle()
  val data = new DSBlock()
}

 class TLBundleDwithBeat1(implicit p: Parameters) extends L2Bundle {
   val d = new TLBundleD(edgeIn.bundle)
   val beat1 = new DSBeat()
 }

// 1. Communicate with L1
//   1.1 Send Grant/GrantData/ReleaseAck/AccessAckData from d and
//   1.2 Receive GrantAck through e
// 2. Send response to Prefetcher
// 3. Block MainPipe enterance when there is not enough space
// 4. Generate Hint signal for L1 early wake-up
class GrantBuffer(parentName: String = "Unknown")(implicit p: Parameters) extends L2Module with HasPerfLogging{
  val io = IO(new Bundle() {
    // receive task from MainPipe
    val d_task = Flipped(DecoupledIO(new TaskWithData()))

    // interact with channels to L1
    val d = DecoupledIO(new TLBundleD(edgeIn.bundle))
    val e = Flipped(DecoupledIO(new TLBundleE(edgeIn.bundle)))

    // for MainPipe entrance blocking
    val fromReqArb = Input(new Bundle() {
      val status_s1 = new PipeEntranceStatus
    })
    val pipeStatusVec = Flipped(Vec(5, ValidIO(new PipeStatus)))
    val toReqArb = Output(new Bundle() {
      val blockSinkReqEntrance = new BlockInfo()
      val blockMSHRReqEntrance = Bool()
    })

    // response to prefetcher
    val prefetchResp = prefetchOpt.map(_ => DecoupledIO(new PrefetchResp))

    // to block sourceB from sending same-addr probe until GrantAck received
    val grantStatus = Output(Vec(grantBufInflightSize, new GrantStatus))

    // generate hint signal for L1
    val l1Hint = ValidIO(new L2ToL1Hint())
    val globalCounter = Output(UInt((log2Ceil(mshrsAll) + 1).W))
  })

  // =========== functions ===========
   def toTLBundleDwithBeat1(td: TaskWithData, grant_id: UInt = 0.U) = {
     val data = td.data.asTypeOf(Vec(beatSize, new DSBeat))
     val d = Wire(new TLBundleD(edgeIn.bundle))
     val beat1 = Wire(new DSBeat())
     d.opcode := td.task.opcode
     d.param := td.task.param
     d.size := offsetBits.U
     d.source := td.task.sourceId
     d.sink := grant_id
     d.denied := false.B
     d.data := data(0).asUInt
     d.corrupt := false.B
     d.echo.lift(DirtyKey).foreach(_ := td.task.dirty)
     beat1 := data(1)

     val output = Wire(new TLBundleDwithBeat1())
     output.d := d
     output.beat1 := beat1
     output
   }

//  def getBeat(data: UInt, beatsOH: UInt): (UInt, UInt) = {
//    // get one beat from data according to beatsOH
//    require(data.getWidth == (blockBytes * 8))
//    require(beatsOH.getWidth == beatSize)
//    // next beat
//    val next_beat = ParallelPriorityMux(beatsOH, data.asTypeOf(Vec(beatSize, UInt((beatBytes * 8).W))))
//    val selOH = PriorityEncoderOH(beatsOH)
//    // remaining beats that haven't been sent out
//    val next_beatsOH = beatsOH & ~selOH
//    (next_beat, next_beatsOH)
//  }

  val grantQueue = Module(new SRAMQueue(new TLBundleDwithBeat1(), entries = mshrsAll, flow = true,
     hasMbist = cacheParams.hasMbist, hasShareBus = cacheParams.hasShareBus,
     hasClkGate = enableClockGate, parentName = parentName))
  val inflightGrant = RegInit(VecInit(Seq.fill(grantBufInflightSize){
    0.U.asTypeOf(Valid(new InflightGrantEntry))
  }))

  val dtaskOpcode = io.d_task.bits.task.opcode

  val mergeAtask = Wire(new TaskBundle())
  mergeAtask.channel := io.d_task.bits.task.channel
  mergeAtask.off := io.d_task.bits.task.aMergeTask.off
  mergeAtask.alias.foreach(_ := io.d_task.bits.task.aMergeTask.alias.getOrElse(0.U))
  mergeAtask.opcode := io.d_task.bits.task.aMergeTask.opcode
  mergeAtask.param := io.d_task.bits.task.aMergeTask.param
  mergeAtask.sourceId := io.d_task.bits.task.aMergeTask.sourceId
  mergeAtask.meta := io.d_task.bits.task.aMergeTask.meta
  mergeAtask.set := io.d_task.bits.task.set
  mergeAtask.tag := io.d_task.bits.task.tag
  mergeAtask.vaddr.foreach(_ := io.d_task.bits.task.vaddr.getOrElse(0.U))
  mergeAtask.size := io.d_task.bits.task.size
  mergeAtask.bufIdx := io.d_task.bits.task.bufIdx
  mergeAtask.needProbeAckData := io.d_task.bits.task.needProbeAckData
  mergeAtask.mshrTask := io.d_task.bits.task.mshrTask
  mergeAtask.mshrId := io.d_task.bits.task.mshrId
  mergeAtask.aliasTask.foreach(_ := io.d_task.bits.task.aliasTask.getOrElse(0.U))
  mergeAtask.useProbeData := false.B
  mergeAtask.fromL2pft.foreach(_ := false.B)
  mergeAtask.needHint.foreach(_ := false.B)
  mergeAtask.dirty := io.d_task.bits.task.dirty
  mergeAtask.way := io.d_task.bits.task.way
  mergeAtask.metaWen := io.d_task.bits.task.metaWen
  mergeAtask.tagWen := io.d_task.bits.task.tagWen
  mergeAtask.dsWen := io.d_task.bits.task.dsWen
  mergeAtask.wayMask := io.d_task.bits.task.wayMask
  mergeAtask.replTask := io.d_task.bits.task.replTask
  mergeAtask.reqSource := io.d_task.bits.task.reqSource
  mergeAtask.mergeTask := false.B
  mergeAtask.mergeA := false.B
  mergeAtask.aMergeTask := 0.U.asTypeOf(new MergeTaskBundle)

  val mergeAtaskWithData = Wire(new TaskWithData())
  mergeAtaskWithData.task := mergeAtask
  mergeAtaskWithData.data := io.d_task.bits.data

  val inflight_insertIdx = PriorityEncoder(inflightGrant.map(!_.valid))

  // The following is organized in the order of data flow
  // =========== save d_task in queue[FIFO] ===========
  grantQueue.io.enq.valid := io.d_task.valid && (dtaskOpcode =/= HintAck || io.d_task.bits.task.mergeA)
  grantQueue.io.enq.bits := toTLBundleDwithBeat1(Mux(io.d_task.bits.task.mergeA, mergeAtaskWithData, io.d_task.bits), inflight_insertIdx)
  io.d_task.ready := true.B // GrantBuf should always be ready

  val grantQueueCnt = grantQueue.io.count
  val full = !grantQueue.io.enq.ready
  assert(!(full && io.d_task.valid), "GrantBuf full and RECEIVE new task, back pressure failed")

  // =========== dequeue entry and fire ===========
  require(beatSize == 2)
  val deqValid = grantQueue.io.deq.valid
  val deq = grantQueue.io.deq.bits

  // grantBuf: to keep the remaining unsent beat of GrantData
  val grantBufValid = RegInit(false.B)
  val grantBuf =  RegInit(0.U.asTypeOf(new TLBundleD(edgeIn.bundle)))

  grantQueue.io.deq.ready := io.d.ready && !grantBufValid

  // if deqTask has data, send the first beat directly and save the remaining beat in grantBuf
  when(deqValid && io.d.ready && !grantBufValid && deq.d.opcode(0)) {
    grantBufValid := true.B
    grantBuf := deq.d
    grantBuf.data := deq.beat1.asUInt
  }
  when(grantBufValid && io.d.ready) {
    grantBufValid := false.B
  }

  io.d.valid := grantBufValid || deqValid
  io.d.bits := Mux(
    grantBufValid,
    grantBuf,
    deq.d
  )

  // =========== send response to prefetcher ===========
  // WARNING: this should never overflow (extremely rare though)
  // but a second thought, pftQueue overflow results in no functional correctness bug
  prefetchOpt.map { _ =>
    val pftRespQueue = Module(new Queue(new Bundle(){
        val tag = UInt(tagBits.W)
        val set = UInt(setBits.W)
      },
      entries = 4,
      flow = true))

    pftRespQueue.io.enq.valid := io.d_task.valid && dtaskOpcode === HintAck &&
      io.d_task.bits.task.fromL2pft.getOrElse(false.B)
    pftRespQueue.io.enq.bits.tag := io.d_task.bits.task.tag
    pftRespQueue.io.enq.bits.set := io.d_task.bits.task.set

    val resp = io.prefetchResp.get
    resp.valid := pftRespQueue.io.deq.valid
    resp.bits.tag := pftRespQueue.io.deq.bits.tag
    resp.bits.set := pftRespQueue.io.deq.bits.set
    pftRespQueue.io.deq.ready := resp.ready

    // assert(pftRespQueue.io.enq.ready, "pftRespQueue should never be full, no back pressure logic") // TODO: has bug here
  }
  // If no prefetch, there never should be HintAck
  assert(prefetchOpt.nonEmpty.B || !io.d_task.valid || dtaskOpcode =/= HintAck)

  // =========== record unreceived GrantAck ===========
  // Addrs with Grant sent and GrantAck not received
  when (io.d_task.fire && (dtaskOpcode(2, 1) === Grant(2, 1) || io.d_task.bits.task.mergeA)) {
    // choose an empty entry
    val entry = inflightGrant(inflight_insertIdx)
    entry.valid := true.B
    entry.bits.set    := io.d_task.bits.task.set
    entry.bits.tag    := io.d_task.bits.task.tag
  }
  val inflight_full = Cat(inflightGrant.map(_.valid)).andR
  assert(!inflight_full, "inflightGrant entries should not be full")

  // report status to SourceB to block same-addr Probe
  io.grantStatus zip inflightGrant foreach {
    case (g, i) =>
      g.valid := i.valid
      g.tag   := i.bits.tag
      g.set   := i.bits.set
  }

  when (io.e.fire) {
    assert(io.e.bits.sink < grantBufInflightSize.U, "GrantBuf: e.sink overflow inflightGrant size")
    inflightGrant(io.e.bits.sink).valid := false.B
  }

  io.e.ready := true.B
 
  // =========== handle blocking - capacity conflict ===========
  // count the number of valid blocks + those in pipe that might use GrantBuf
  // so that GrantBuffer will not exceed capacity
  // TODO: we can still allow pft_resps (HintAck) to enter mainpipe
  val noSpaceForSinkReq = PopCount(VecInit(io.pipeStatusVec.tail.map { case s =>
    s.valid && (s.bits.fromA || s.bits.fromC)
  }).asUInt) + grantQueueCnt >= mshrsAll.U
  val noSpaceForMSHRReq = PopCount(VecInit(io.pipeStatusVec.map { case s =>
    s.valid && s.bits.fromA
  }).asUInt) + grantQueueCnt >= mshrsAll.U
  // TODO: only block mp_grant and acuqire
  val noSpaceForWaitSinkE = PopCount(Cat(VecInit(io.pipeStatusVec.tail.map { case s =>
    s.valid && s.bits.fromA
  }).asUInt, Cat(inflightGrant.map(_.valid)).asUInt)) >= (grantBufInflightSize-1).U

  io.toReqArb.blockSinkReqEntrance.blockA_s1 := noSpaceForSinkReq || noSpaceForWaitSinkE // TODO: noSpaceForSinkPft.getOrElse(false.B)
  io.toReqArb.blockSinkReqEntrance.blockB_s1 := Cat(inflightGrant.map(g => g.valid &&
    g.bits.set === io.fromReqArb.status_s1.b_set && g.bits.tag === io.fromReqArb.status_s1.b_tag)).orR
  //TODO: or should we still Stall B req?
  // A-replace related rprobe is handled in SourceB
  io.toReqArb.blockSinkReqEntrance.blockC_s1 := noSpaceForSinkReq
  io.toReqArb.blockSinkReqEntrance.blockG_s1 := false.B
  io.toReqArb.blockMSHRReqEntrance := noSpaceForMSHRReq || noSpaceForWaitSinkE

  // =========== generating Hint to L1 ===========
  // TODO: the following keeps the exact same logic as before, but it needs serious optimization
  val hintQueue = Module(new Queue(UInt(sourceIdBits.W), entries = mshrsAll))
  // Total number of beats left to send in GrantBuf
  // [This is better]
  // val globalCounter = (grantQueue.io.count << 1.U).asUInt + grantBufValid.asUInt // entries * 2 + grantBufValid
  val globalCounter = RegInit(0.U((log2Ceil(grantBufSize) + 1).W))
  when(io.d_task.fire) {
    val hasData = io.d_task.bits.task.opcode(0)
    when(hasData) {
      globalCounter := globalCounter + 1.U // counter = counter + 2 - 1
    }.otherwise {
      globalCounter := globalCounter // counter = counter + 1 - 1
    }
  }.otherwise {
    globalCounter := Mux(globalCounter === 0.U, 0.U, globalCounter - 1.U) // counter = counter - 1
  }

  // if globalCounter >= 3, it means the hint that should be sent is in GrantBuf
  when(globalCounter >= 3.U) {
    hintQueue.io.enq.valid := true.B
    hintQueue.io.enq.bits := io.d_task.bits.task.sourceId
  }.otherwise {
    hintQueue.io.enq.valid := false.B
    hintQueue.io.enq.bits := 0.U(sourceIdBits.W)
  }
  hintQueue.io.deq.ready := true.B

  // tell CustomL1Hint about the delay in GrantBuf
  io.globalCounter := globalCounter

  io.l1Hint.valid := hintQueue.io.deq.valid
  io.l1Hint.bits.sourceId := hintQueue.io.deq.bits

  // =========== XSPerf ===========
  if (cacheParams.enablePerf) {
    val timers = RegInit(VecInit(Seq.fill(grantBufInflightSize){0.U(64.W)}))
    inflightGrant zip timers map {
      case (e, t) =>
        when(e.valid) { t := t + 1.U }
        when(RegNext(e.valid) && !e.valid) { t := 0.U }
        assert(t < 10000.U, "Inflight Grant Leak")

        val enable = RegNext(e.valid) && !e.valid
        XSPerfHistogram("grant_grantack_period", t, enable, 0, 12, 1)
        XSPerfMax("max_grant_grantack_period", t, enable)
    }
  }
}
