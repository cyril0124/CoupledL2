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
  val sink  = UInt(mshrBits.W)
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

    // response to MSHR
    val e_resp = Output(new RespBundle)

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

    val hintDup = Flipped(ValidIO(new Bundle() {
      val tag = Input(UInt(tagBits.W))
      val set = Input(UInt(setBits.W))
    }))
  })

  // =========== functions ===========
   def toTLBundleDwithBeat1(td: TaskWithData) = {
     val data = td.data.asTypeOf(Vec(beatSize, new DSBeat))
     val d = Wire(new TLBundleD(edgeIn.bundle))
     val beat1 = Wire(new DSBeat())
     d.opcode := td.task.opcode
     d.param := td.task.param
     d.size := offsetBits.U
     d.source := td.task.sourceId
     d.sink := td.task.mshrId
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

  val dtaskOpcode = io.d_task.bits.task.opcode
  // The following is organized in the order of data flow
  // =========== save d_task in queue[FIFO] ===========
  val grantQueue = Module(new SRAMQueue(new TLBundleDwithBeat1(), entries = mshrsAll, flow = true,
     hasMbist = cacheParams.hasMbist, hasShareBus = cacheParams.hasShareBus,
     hasClkGate = enableClockGate, parentName = parentName))
  grantQueue.io.enq.valid := io.d_task.valid && dtaskOpcode =/= HintAck
  grantQueue.io.enq.bits := toTLBundleDwithBeat1(io.d_task.bits)
  io.d_task.ready := true.B // GrantBuf should always be ready

  val grantQueueCnt = grantQueue.io.count
  val full = !grantQueue.io.enq.ready
  if(cacheParams.enableAssert) assert(!(full && io.d_task.valid), "GrantBuf full and RECEIVE new task, back pressure failed")

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
      entries = 32,
      flow = true))

    // val latePftRespQueue = Module(new Queue(new Bundle() {
    //     val tag = UInt(tagBits.W)
    //     val set = UInt(setBits.W)
    //   },
    //   entries = 32,
    //   flow = true))

    // latePftRespQueue.io.enq.valid := io.hintDup.valid
    // latePftRespQueue.io.enq.bits.tag := io.hintDup.bits.tag
    // latePftRespQueue.io.enq.bits.set := io.hintDup.bits.set

    pftRespQueue.io.enq.valid := io.d_task.valid && dtaskOpcode === HintAck &&
      io.d_task.bits.task.fromL2pft.getOrElse(false.B)
    pftRespQueue.io.enq.bits.tag := io.d_task.bits.task.tag
    pftRespQueue.io.enq.bits.set := io.d_task.bits.task.set

    // val toPftArb = Module(new RRArbiterInit(new Bundle() {
    //   val tag = UInt(tagBits.W)
    //   val set = UInt(setBits.W)
    // }, 2))
    // toPftArb.io.in(0) <> pftRespQueue.io.deq
    // toPftArb.io.in(1) <> latePftRespQueue.io.deq

    val resp = io.prefetchResp.get
    // resp <> toPftArb.io.out
    resp <> pftRespQueue.io.deq

//    assert(latePftRespQueue.io.enq.ready, "latePftRespQueue should never be full, no back pressure logic") // TODO: has bug here
//    assert(pftRespQueue.io.enq.ready, "pftRespQueue should never be full, no back pressure logic") // TODO: has bug here
    // if (cacheParams.enablePerf) {
    //   XSPerfAccumulate("GrantBuf_late_prefetchResp_drop", latePftRespQueue.io.enq.valid && !latePftRespQueue.io.enq.ready)
    //   XSPerfAccumulate("GrantBuf_prefetchResp_drop", pftRespQueue.io.enq.valid && !pftRespQueue.io.enq.ready)
    // }
  }
  // If no prefetch, there never should be HintAck
  if(cacheParams.enableAssert) assert(prefetchOpt.nonEmpty.B || !io.d_task.valid || dtaskOpcode =/= HintAck)

  // =========== record unreceived GrantAck ===========
  // Addrs with Grant sent and GrantAck not received
  val inflight_grant = RegInit(VecInit(Seq.fill(grantBufInflightSize){
    0.U.asTypeOf(Valid(new InflightGrantEntry))
  }))
  when (io.d_task.fire && dtaskOpcode(2, 1) === Grant(2, 1)) {
    // choose an empty entry
    val insertIdx = PriorityEncoder(inflight_grant.map(!_.valid))
    val entry = inflight_grant(insertIdx)
    entry.valid := true.B
    entry.bits.set    := io.d_task.bits.task.set
    entry.bits.tag    := io.d_task.bits.task.tag
    entry.bits.sink   := io.d_task.bits.task.mshrId
  }
  val inflight_full = Cat(inflight_grant.map(_.valid)).andR
  if(cacheParams.enableAssert) assert(!inflight_full, "inflight_grant entries should not be full")

  // report status to SourceB to block same-addr Probe
  io.grantStatus zip inflight_grant foreach {
    case (g, i) =>
      g.valid := i.valid
      g.tag   := i.bits.tag
      g.set   := i.bits.set
  }

  when (io.e.fire) {
    // compare sink to clear buffer
    val sinkMatchVec = inflight_grant.map(g => g.valid && g.bits.sink === io.e.bits.sink)
    if(cacheParams.enableAssert) assert(PopCount(sinkMatchVec) === 1.U, "GrantBuf: there must be one and only one match")
    val bufIdx = OHToUInt(sinkMatchVec)
    inflight_grant(bufIdx).valid := false.B
  }

  // =========== send e resp to MSHRs ===========
  io.e.ready := true.B
  io.e_resp.valid := io.e.valid
  io.e_resp.mshrId := io.e.bits.sink
  io.e_resp.set := 0.U(setBits.W)
  io.e_resp.tag := 0.U(tagBits.W)
  io.e_resp.respInfo.opcode := GrantAck
  io.e_resp.respInfo.param := 0.U(3.W)
  io.e_resp.respInfo.last := true.B
  io.e_resp.respInfo.dirty := false.B
  io.e_resp.respInfo.isHit := false.B

  // =========== handle blocking - capacity conflict ===========
  // count the number of valid blocks + those in pipe that might use GrantBuf
  // so that GrantBuffer will not exceed capacity
  // TODO: we can still allow pft_resps (HintAck) to enter mainpipe
  val toReqArb = WireInit(0.U.asTypeOf((io.toReqArb)))
  val latency = 1.U

  val noSpaceForSinkReq = PopCount(VecInit(io.pipeStatusVec.tail.map { case s =>
    s.valid && (s.bits.fromA || s.bits.fromC)
  }).asUInt) + grantQueueCnt >= mshrsAll.U - latency
  val noSpaceForMSHRReq = PopCount(VecInit(io.pipeStatusVec.map { case s =>
    s.valid && s.bits.fromA
  }).asUInt) + grantQueueCnt >= mshrsAll.U - latency
  // TODO: only block mp_grant and acuqire
  val noSpaceForWaitSinkE = PopCount(Cat(VecInit(io.pipeStatusVec.tail.map { case s =>
    s.valid && s.bits.fromA
  }).asUInt, Cat(inflight_grant.map(_.valid)).asUInt)) >= (grantBufInflightSize-1).U - latency

  toReqArb.blockSinkReqEntrance.blockA_s1 := noSpaceForSinkReq || noSpaceForWaitSinkE
  toReqArb.blockSinkReqEntrance.blockB_s1 := Cat(inflight_grant.map(g => g.valid &&
    g.bits.set === io.fromReqArb.status_s1.b_set && g.bits.tag === io.fromReqArb.status_s1.b_tag)).orR
  //TODO: or should we still Stall B req?
  // A-replace related rprobe is handled in SourceB
  toReqArb.blockSinkReqEntrance.blockC_s1 := noSpaceForSinkReq
  toReqArb.blockSinkReqEntrance.blockG_s1 := false.B
  toReqArb.blockMSHRReqEntrance := noSpaceForMSHRReq || noSpaceForWaitSinkE

  io.toReqArb := RegNext(toReqArb)

  // =========== XSPerf ===========
  if (cacheParams.enablePerf) {
    val timers = RegInit(VecInit(Seq.fill(grantBufInflightSize){0.U(64.W)}))
    inflight_grant zip timers map {
      case (e, t) =>
        when(e.valid) { t := t + 1.U }
        when(RegNext(e.valid) && !e.valid) { t := 0.U }
        if(cacheParams.enableAssert) assert(t < 10000.U, "Inflight Grant Leak")

        val enable = RegNext(e.valid) && !e.valid
        XSPerfHistogram("grant_grantack_period", t, enable, 0, 12, 1)
        XSPerfMax("max_grant_grantack_period", t, enable)
    }
  }
}
