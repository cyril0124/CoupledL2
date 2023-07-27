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

package coupledL3

import chisel3._
import chisel3.util._
import chipsalliance.rocketchip.config.Parameters
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tilelink.TLMessages._
import freechips.rocketchip.tilelink.TLHints._
import coupledL3.prefetch.PrefetchReq
import coupledL3.utils.XSPerfAccumulate

class SinkA(implicit p: Parameters) extends L3Module {
  val io = IO(new Bundle() {
    val a = Flipped(DecoupledIO(new TLBundleA(edgeIn.bundle)))
    val prefetchReq = prefetchOpt.map(_ => Flipped(DecoupledIO(new PrefetchReq)))
    val toReqArb = DecoupledIO(new TaskBundle)

    val pbRead = Flipped(ValidIO(new PutBufferRead))
    val pbResp = Output(Vec(beatSize, new PutBufferEntry))

    val fromMainPipe = Input(new Bundle{
      val putReqGood_s3 = Bool() // PutFullData / PutPartialData hit and do not need to allcate a MSHR
    })

    val fromPutDataBuf = Input(new Bundle{
      val full = Bool()
    })
  })

  val putBuffer = Reg(Vec(mshrsAll, Vec(beatSize, new PutBufferEntry)))
  val beatValids = RegInit(VecInit(Seq.fill(mshrsAll)(VecInit(Seq.fill(beatSize)(false.B)))))
  val valids = VecInit(beatValids.map(_.asUInt.orR())).asUInt
  
  val (first, last, done, count) = edgeIn.count(io.a)
  val hasData = edgeIn.hasData(io.a.bits)
  dontTouch(hasData)

  val count_1 = RegInit(0.U(beatSize.W))
  val first_1 = count_1 === 0.U
  when(io.a.fire() && count_1 === (beatSize - 1).U) {
    count_1 := 0.U
  }.elsewhen(io.a.fire() && hasData){
      count_1 := count_1 + 1.U
  }


  val full = valids.andR()
  val noSpace = full && hasData
  val insertIdx = PriorityEncoder(~valids)
  val insertIdxReg = RegEnable(insertIdx, 0.U.asTypeOf(insertIdx), io.a.fire() && first_1)

  when (io.a.fire() && hasData) {
    when (first_1) {
      putBuffer(insertIdx)(count_1).data.data := io.a.bits.data
      putBuffer(insertIdx)(count_1).mask := io.a.bits.mask
      beatValids(insertIdx)(count_1) := true.B
    }.otherwise {
      putBuffer(insertIdxReg)(count_1).data.data := io.a.bits.data
      putBuffer(insertIdxReg)(count_1).mask := io.a.bits.mask
      beatValids(insertIdxReg)(count_1) := true.B
    }
  }

  //  Store put data / mask
  when (RegNext(io.pbRead.fire() && !io.pbRead.bits.isMSHRTask)) {
    when(io.fromMainPipe.putReqGood_s3) {
      beatValids(RegNext(io.pbRead.bits.idx)).foreach(_ := false.B)
    }
  }
  // Release buffer
  when (io.pbRead.fire() && io.pbRead.bits.isMSHRTask) {
    beatValids(io.pbRead.bits.idx).foreach(_ := false.B)
  }

  def fromTLAtoTaskBundle(a: TLBundleA): TaskBundle = {
    val task = Wire(new TaskBundle)
    task := DontCare
    task.channel := "b001".U
    task.tag := parseAddress(a.address)._1
    task.set := parseAddress(a.address)._2
    task.off := parseAddress(a.address)._3
    task.alias.foreach(_ := a.user.lift(AliasKey).getOrElse(0.U))
    task.opcode := a.opcode
    task.param := a.param
    task.size := a.size
    task.sourceId := a.source
    task.mshrTask := false.B
    task.pbIdx := insertIdx
    task.fromL3pft.foreach(_ := false.B)
    task.needHint.foreach(_ := a.user.lift(PrefetchKey).getOrElse(false.B))
    task.reqSource := a.user.lift(utility.ReqSourceKey).getOrElse(MemReqSource.NoWhere.id.U)
    task
  }

  def fromPrefetchReqtoTaskBundle(req: PrefetchReq): TaskBundle = {
    val task = Wire(new TaskBundle)
    val fullAddr = Cat(req.tag, req.set, 0.U(offsetBits.W))
    task := DontCare
    task.channel := "b001".U
    task.tag := parseAddress(fullAddr)._1
    task.set := parseAddress(fullAddr)._2
    task.off := 0.U
    task.alias.foreach(_ := 0.U)
    task.opcode := Hint
    task.param := Mux(req.needT, PREFETCH_WRITE, PREFETCH_READ)
    task.size := offsetBits.U
    task.sourceId := req.source
    task.needProbeAckData := false.B
    task.mshrTask := false.B
    task.aliasTask.foreach(_ := false.B)
    task.fromL3pft.foreach(_ := req.isBOP)
    task.needHint.foreach(_ := false.B)
    task.reqSource := MemReqSource.L3Prefetch.id.U
    task
  }


  // Put Stage: put data should be bufferd one cycle(beat == 2) to make sure we accept all of the put data
  // TODO: Parameterize it according to number of beat
  val s0_valid = Wire(Bool())
  val s0_ready, s1_ready = Wire(Bool())

  val s0_full = RegInit(false.B)
  val s0_latch = io.a.valid & s0_ready & first_1 & hasData
  val s0_fire = s0_valid & s1_ready
  val s0_req = RegEnable(fromTLAtoTaskBundle(io.a.bits), s0_latch)
  val s0_hasData = RegEnable(hasData, s0_latch)

  s0_ready := (s0_fire || !s0_full) && !noSpace
  when(s0_latch) { s0_full := true.B }
    .elsewhen(s0_full && s0_fire) { s0_full := false.B }

  s0_valid := s0_full


  // TODO: How about put with only one beat?
  val commonReq = Wire(io.toReqArb.cloneType)
  val prefetchReq = prefetchOpt.map(_ => Wire(io.toReqArb.cloneType))

  s1_ready := commonReq.ready
  io.a.ready := !first_1 || s0_ready && hasData && !io.fromPutDataBuf.full || commonReq.ready && !hasData && !s0_full


  val putValid = s0_valid && s0_hasData && s0_full
  val otherValid = !hasData && io.a.valid && first_1 && !s0_full
  commonReq.valid := putValid || otherValid

  val req = Mux(putValid, s0_req, fromTLAtoTaskBundle(io.a.bits))
  commonReq.bits := req

  if (prefetchOpt.nonEmpty) {
    prefetchReq.get.valid := io.prefetchReq.get.valid
    prefetchReq.get.bits := fromPrefetchReqtoTaskBundle(io.prefetchReq.get.bits)
    io.prefetchReq.get.ready := prefetchReq.get.ready
    fastArb(Seq(commonReq, prefetchReq.get), io.toReqArb)
  } else {
    io.toReqArb <> commonReq
  }


  io.pbResp.zipWithIndex.foreach{
    case (resp, i) => resp := putBuffer(io.pbRead.bits.idx)(i)
  }

  // Performance counters
  // num of reqs
  XSPerfAccumulate(cacheParams, "sinkA_req", io.toReqArb.fire())
  XSPerfAccumulate(cacheParams, "sinkA_acquire_req", io.a.fire() && io.a.bits.opcode(2, 1) === AcquireBlock(2, 1))
  XSPerfAccumulate(cacheParams, "sinkA_acquireblock_req", io.a.fire() && io.a.bits.opcode === AcquireBlock)
  XSPerfAccumulate(cacheParams, "sinkA_acquireperm_req", io.a.fire() && io.a.bits.opcode === AcquirePerm)
  XSPerfAccumulate(cacheParams, "sinkA_get_req", io.a.fire() && io.a.bits.opcode === Get)
  XSPerfAccumulate(cacheParams, "sinkA_put_req", io.toReqArb.fire() &&
    (io.toReqArb.bits.opcode === PutFullData || io.toReqArb.bits.opcode === PutPartialData))
  XSPerfAccumulate(cacheParams, "sinkA_put_beat", io.a.fire() &&
    (io.a.bits.opcode === PutFullData || io.a.bits.opcode === PutPartialData))
  prefetchOpt.foreach { _ => XSPerfAccumulate(cacheParams, "sinkA_prefetch_req", io.prefetchReq.get.fire()) }

  // cycels stalled by mainpipe
  val stall = io.toReqArb.valid && !io.toReqArb.ready
  XSPerfAccumulate(cacheParams, "sinkA_stall_by_mainpipe", stall)
  XSPerfAccumulate(cacheParams, "sinkA_acquire_stall_by_mainpipe", stall &&
    (io.toReqArb.bits.opcode === AcquireBlock || io.toReqArb.bits.opcode === AcquirePerm))
  XSPerfAccumulate(cacheParams, "sinkA_get_stall_by_mainpipe", stall && io.toReqArb.bits.opcode === Get)
  XSPerfAccumulate(cacheParams, "sinkA_put_stall_by_mainpipe", stall &&
    (io.toReqArb.bits.opcode === PutFullData || io.toReqArb.bits.opcode === PutPartialData))
  prefetchOpt.foreach { _ => XSPerfAccumulate(cacheParams, "sinkA_prefetch_stall_by_mainpipe", stall && io.toReqArb.bits.opcode === Hint) }

  // cycles stalled for no space
  XSPerfAccumulate(cacheParams, "sinkA_put_stall_for_noSpace", io.a.valid && first_1 && noSpace)
  XSPerfAccumulate(cacheParams, "putbuffer_full", full)
}