/** *************************************************************************************
 * Copyright (c) 2020-2021 Institute of Computing Technology, Chinese Academy of Sciences
 * Copyright (c) 2020-2021 Peng Cheng Laboratory
 *
 * XiangShan is licensed under Mulan PSL v2.
 * You can use this software according to the terms and conditions of the Mulan PSL v2.
 * You may obtain a copy of Mulan PSL v2 at:
 *          http://license.coscl.org.cn/MulanPSL2
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
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tilelink.TLMessages._
import chipsalliance.rocketchip.config.Parameters
import coupledL3.utils.XSPerfAccumulate

class PipeBufferRead(implicit p: Parameters) extends L3Bundle {
  val bufIdx = UInt(bufIdxBits.W)
}

class PipeBufferResp(implicit p: Parameters) extends L3Bundle {
  val data = Vec(beatSize, UInt((beatBytes * 8).W))
}

// SinkC receives upwards Release or ProbeAck:
// (1) For Release/ReleaseData, send it to RequestArb directly
// (2) For ProbeAck/ProbeAckData, wakeup w_probeack in MSHR
//     For ProbeAckData, save data into ReleaseBuffer
class SinkC(implicit p: Parameters) extends L3Module {
  val io = IO(new Bundle() {
    val c = Flipped(DecoupledIO(new TLBundleC(edgeIn.bundle)))
    val toReqArb = DecoupledIO(new TaskBundle) // Release/ReleaseData
    val resp = Output(new RespBundle)
    val releaseBufWrite = Flipped(new MSHRBufWrite)
    val bufRead = Input(ValidIO(new PipeBufferRead))
    val bufResp = Output(new PipeBufferResp)
    val mshrStatus  = Vec(mshrsAll, Flipped(ValidIO(new MSHRBlockAInfo)))
    val mshrFull = Input(Bool())
  })
  
  val (first, last, _, beat) = edgeIn.count(io.c)
  val isRelease = io.c.bits.opcode(1)
  val hasData = io.c.bits.opcode(0)

  // dataBuf entry is valid when Release has data
  // taskBuf entry is valid when ReqArb is not ready to receive C tasks
  val dataBuf = Reg(Vec(bufBlocks, Vec(beatSize, UInt((beatBytes * 8).W))))
  val beatValids = RegInit(VecInit(Seq.fill(bufBlocks)(VecInit(Seq.fill(beatSize)(false.B)))))
  val dataValids = VecInit(beatValids.map(_.asUInt.orR)).asUInt
  val taskBuf = Reg(Vec(bufBlocks, new TaskBundle))
  val taskValids = RegInit(VecInit(Seq.fill(bufBlocks)(false.B)))
  // val taskArb = Module(new RRArbiter(new TaskBundle, bufBlocks))
  val taskArb = Module(new Arbiter(new TaskBundle, bufBlocks))
  val bufValids = taskValids.asUInt | dataValids

  val full = bufValids.andR
  val noSpace = full && hasData
  val nextPtr = PriorityEncoder(~bufValids)
  val nextPtrReg = RegEnable(nextPtr, 0.U.asTypeOf(nextPtr), io.c.fire() && isRelease && first && hasData)

  def toTaskBundle(c: TLBundleC): TaskBundle = {
    val task = Wire(new TaskBundle)
    task := DontCare
    task.channel := "b100".U
    task.tag := parseAddress(c.address)._1
    task.set := parseAddress(c.address)._2
    task.off := parseAddress(c.address)._3
    task.alias.foreach(_ := 0.U)
    task.opcode := c.opcode
    task.param := c.param
    task.size := c.size
    task.sourceId := c.source
    task.mshrTask := false.B
    task.wayMask := Fill(cacheParams.ways, "b1".U)
    task.reqSource := MemReqSource.NoWhere.id.U // Ignore
    task
  }

  def getMSHRSameSetVec(valid: Bool, set: UInt) = {
    val mshrSameSetVec = VecInit(io.mshrStatus.map { status =>
      status.valid && valid && status.bits.set === set
    })
    mshrSameSetVec
  }

  def getMSHRSameSetChannelCVec(valid: Bool, set: UInt) = {
    val mshrSameSetVec = getMSHRSameSetVec(valid, set)
    val mshrSameSetChannelCVec = VecInit(mshrSameSetVec.zip(io.mshrStatus).map{
      case (sameSet, mshrStatus) =>
        sameSet && mshrStatus.bits.isChannelC
    })
    mshrSameSetChannelCVec
  }

  when (io.c.fire() && isRelease) {
    when (hasData) {
      when (first) {
        dataBuf(nextPtr)(beat) := io.c.bits.data
        beatValids(nextPtr)(beat) := true.B
      }.otherwise {
        assert(last)
        dataBuf(nextPtrReg)(beat) := io.c.bits.data
        beatValids(nextPtrReg)(beat) := true.B
      }
    }
  }

  when (io.c.fire() && isRelease && last && (!io.toReqArb.ready || taskArb.io.out.valid)) {
    when (hasData) { // ReleaseData
      taskValids(nextPtrReg) := true.B
      taskBuf(nextPtrReg) := toTaskBundle(io.c.bits)
      taskBuf(nextPtrReg).bufIdx := nextPtrReg
    }.otherwise { // Release
      taskValids(nextPtr) := true.B
      taskBuf(nextPtr) := toTaskBundle(io.c.bits)
      taskBuf(nextPtr).bufIdx := nextPtr
    }
  }

  taskArb.io.in.zipWithIndex.foreach {
    case (in, i) =>
      in.valid := taskValids(i) && !(getMSHRSameSetChannelCVec(taskValids(i), taskBuf(i).set).asUInt).orR
      in.bits := taskBuf(i)
      when (in.fire()) {
        taskValids(i) := false.B
      }
  }

  when (io.bufRead.valid) {
    beatValids(io.bufRead.bits.bufIdx).foreach(_ := false.B)
  }

  val cValid = io.c.valid && isRelease && last // Release flow
  val cValid_mshrSameSetVec = getMSHRSameSetVec(cValid, parseAddress(io.c.bits.address)._2)
  val cValid_sameSetChannelCVec = VecInit(cValid_mshrSameSetVec.zip(io.mshrStatus).map{
    case (sameSet, mshrStatus) =>
      sameSet && mshrStatus.bits.isChannelC
  })
  val cValid_sameSetConflict = cValid_sameSetChannelCVec.asUInt.orR

  io.toReqArb.valid := (cValid && !cValid_sameSetConflict || taskArb.io.out.valid) && !io.mshrFull
  taskArb.io.out.ready := io.toReqArb.ready

  io.toReqArb.bits := Mux(taskArb.io.out.valid, taskArb.io.out.bits, toTaskBundle(io.c.bits))
  io.toReqArb.bits.bufIdx := Mux(taskArb.io.out.valid, taskArb.io.out.bits.bufIdx, nextPtrReg)

  io.resp.valid := io.c.valid && (first || last) && !isRelease
  io.resp.mshrId := 0.U // DontCare
  io.resp.tag := parseAddress(io.c.bits.address)._1
  io.resp.set := parseAddress(io.c.bits.address)._2
  io.resp.respInfo := DontCare
  io.resp.respInfo.opcode := io.c.bits.opcode
  io.resp.respInfo.param := io.c.bits.param
  io.resp.respInfo.last := last
  io.resp.respInfo.dirty := io.c.bits.opcode(0)
  if(cacheParams.name == "l3") {
    io.resp.respInfo.source := io.c.bits.source
  }

  io.releaseBufWrite.valid := io.c.valid && io.c.bits.opcode === ProbeAckData
  io.releaseBufWrite.beat_sel := UIntToOH(beat)
  io.releaseBufWrite.data.data := Fill(beatSize, io.c.bits.data)
  io.releaseBufWrite.id := DontCare // id is given by MSHRCtl by comparing address to the MSHRs (only for ProbeAckData)
  io.releaseBufWrite.corrupt := false.B

  // io.c.ready := !first || !noSpace && !(isRelease && !io.toReqArb.ready)
  // io.c.ready := !isRelease || !first || !full || !hasData && io.toReqArb.ready
  io.c.ready := (!isRelease || !first || !full || !hasData && io.toReqArb.ready) && !io.mshrFull


  io.bufResp.data := dataBuf(io.bufRead.bits.bufIdx)

  // Performance counters
  val stall = io.c.valid && isRelease && !io.c.ready
  XSPerfAccumulate(cacheParams, "sinkC_c_stall", stall)
  XSPerfAccumulate(cacheParams, "sinkC_c_stall_for_noSpace", stall && hasData && first && full)
  XSPerfAccumulate(cacheParams, "sinkC_toReqArb_stall", io.toReqArb.valid && !io.toReqArb.ready)
  XSPerfAccumulate(cacheParams, "sinkC_buf_full", full)
}

class SinkC_1(implicit p: Parameters) extends L3Module {
  val io = IO(new Bundle() {
    val c = Flipped(DecoupledIO(new TLBundleC(edgeIn.bundle)))
    val toReqArb = DecoupledIO(new TaskBundle) // Release/ReleaseData
    val resp = Output(new RespBundle)
    val releaseBufWrite = Flipped(new MSHRBufWrite)
    val bufRead = Input(ValidIO(new PipeBufferRead))
    val bufResp = Output(new PipeBufferResp)
    val mshrStatus  = Vec(mshrsAll, Flipped(ValidIO(new MSHRBlockAInfo)))
    val mshrFull = Input(Bool())
  })

  val (first, last, _, beat) = edgeIn.count(io.c)
  val isRelease = io.c.bits.opcode(1)
  val hasData = io.c.bits.opcode(0)

  // dataBuf entry is valid when Release has data
  val dataBuf = Reg(Vec(bufBlocks, Vec(beatSize, UInt((beatBytes * 8).W))))
  val beatValids = RegInit(VecInit(Seq.fill(bufBlocks)(VecInit(Seq.fill(beatSize)(false.B)))))
  val dataValids = VecInit(beatValids.map(_.asUInt.orR)).asUInt
  val bufValids = dataValids

  val full = bufValids.andR
  val noSpace = full && hasData
  val nextPtr = PriorityEncoder(~bufValids)
  val nextPtrReg = RegEnable(nextPtr, 0.U.asTypeOf(nextPtr), io.c.fire() && isRelease && first && hasData)
  val tag = parseAddress(io.c.bits.address)._1
  val set = parseAddress(io.c.bits.address)._2

  def toTaskBundle(c: TLBundleC): TaskBundle = {
    val task = Wire(new TaskBundle)
    task := DontCare
    task.channel := "b100".U
    task.tag := parseAddress(c.address)._1
    task.set := parseAddress(c.address)._2
    task.off := parseAddress(c.address)._3
    task.alias.foreach(_ := 0.U)
    task.opcode := c.opcode
    task.param := c.param
    task.size := c.size
    task.sourceId := c.source
    task.mshrTask := false.B
    task.wayMask := Fill(cacheParams.ways, "b1".U)
    task.reqSource := MemReqSource.NoWhere.id.U // Ignore
    task
  }

  when (io.c.fire() && isRelease) {
    when (hasData) {
      when (first) {
        dataBuf(nextPtr)(beat) := io.c.bits.data
        beatValids(nextPtr)(beat) := true.B
      }.otherwise {
        assert(last)
        dataBuf(nextPtrReg)(beat) := io.c.bits.data
        beatValids(nextPtrReg)(beat) := true.B
      }
    }
  }

  when (io.bufRead.valid) {
    beatValids(io.bufRead.bits.bufIdx).foreach(_ := false.B)
  }


  io.toReqArb.valid := io.c.valid && first && isRelease && !noSpace
  io.toReqArb.bits := toTaskBundle(io.c.bits)
  io.toReqArb.bits.bufIdx := nextPtr

  io.resp.valid := io.c.valid && (first || last) && !isRelease
  io.resp.mshrId := 0.U // DontCare
  io.resp.tag := tag
  io.resp.set := set
  io.resp.respInfo := DontCare
  io.resp.respInfo.opcode := io.c.bits.opcode
  io.resp.respInfo.param := io.c.bits.param
  io.resp.respInfo.last := last
  io.resp.respInfo.dirty := io.c.bits.opcode(0)
  io.resp.respInfo.source := io.c.bits.source

  io.releaseBufWrite.valid := io.c.valid && io.c.bits.opcode === ProbeAckData
  io.releaseBufWrite.beat_sel := UIntToOH(beat)
  io.releaseBufWrite.data.data := Fill(beatSize, io.c.bits.data)
  io.releaseBufWrite.id := DontCare // id is given by MSHRCtl by comparing address to the MSHRs (only for ProbeAckData)
  io.releaseBufWrite.corrupt := false.B

//  io.c.ready := !isRelease || // ProbeAck / ProbeAckData
//                isRelease && first && !io.mshrFull || // Release / ReleaseData
//                !hasData && io.toReqArb.ready || // TODO: why?
//                !first

  io.c.ready := Mux(first, !noSpace && !(isRelease && !io.toReqArb.ready), true.B)


  io.bufResp.data := dataBuf(io.bufRead.bits.bufIdx)

  // Performance counters
  val stall = io.c.valid && isRelease && !io.c.ready
  XSPerfAccumulate(cacheParams, "sinkC_c_stall", stall)
  XSPerfAccumulate(cacheParams, "sinkC_c_stall_for_noSpace", stall && hasData && first && full)
  XSPerfAccumulate(cacheParams, "sinkC_toReqArb_stall", io.toReqArb.valid && !io.toReqArb.ready)
  XSPerfAccumulate(cacheParams, "sinkC_buf_full", full)
}