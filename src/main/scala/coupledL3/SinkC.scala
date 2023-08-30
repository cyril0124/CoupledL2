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
import utility.FastArbiter

class PipeBufferRead(implicit p: Parameters) extends L3Bundle {
  val bufIdx = UInt(bufIdxBits.W)
  val bufInvalid = Bool()
}

class PipeBufferResp(implicit p: Parameters) extends L3Bundle {
  val data = Vec(beatSize, UInt((beatBytes * 8).W))
}

class TaskStatusSinkC(implicit p: Parameters) extends L3Bundle {
  val valid = Bool()
  val sourceId = UInt(sourceIdBits.W)
}

// SinkC receives upwards Release or ProbeAck:
// (1) For Release/ReleaseData, send it to RequestArb directly
// (2) For ProbeAck/ProbeAckData, wakeup w_probeack in MSHR
//     For ProbeAckData, save data into ReleaseBuffer
class SinkC(implicit p: Parameters) extends L3Module with noninclusive.HasClientInfo{
  val io = IO(new Bundle() {
    val c = Flipped(DecoupledIO(new TLBundleC(edgeIn.bundle)))
    val toReqArb = DecoupledIO(new TaskBundle) // Release/ReleaseData
    val resp = Output(new RespBundle)
    val releaseBufWrite = DecoupledIO(new MSHRBufWrite)
    val bufRead = Input(ValidIO(new PipeBufferRead))
    val bufResp = Output(new PipeBufferResp)
    val mshrStatus  = Vec(mshrsAll, Flipped(ValidIO(new MSHRBlockAInfo)))
    val taskStatus = Output(Vec(bufBlocks, new TaskStatusSinkC))
  })
  
  val (first, last, _, beat) = edgeIn.count(io.c)
  val isRelease = io.c.bits.opcode(1)
  val isProbeAck = !isRelease
  val hasData = io.c.bits.opcode(0)

  // dataBuf entry is valid when Release has data
  // taskBuf entry is valid when ReqArb is not ready to receive C tasks
  val dataBuf = RegInit(VecInit(Seq.fill(bufBlocks)(0.U.asTypeOf(Vec(beatSize, UInt((beatBytes * 8).W))))))
  val beatValids = RegInit(VecInit(Seq.fill(bufBlocks)(VecInit(Seq.fill(beatSize)(false.B)))))
  val dataValids = VecInit(beatValids.map(_.asUInt.orR)).asUInt
  val taskBuf = RegInit(VecInit(Seq.fill(bufBlocks)(0.U.asTypeOf(new TaskBundle))))
  val taskValids = RegInit(VecInit(Seq.fill(bufBlocks)(false.B)))
  val taskArb = Module(new FastArbiter(new TaskBundle, bufBlocks))
  val bufValids = taskValids.asUInt | dataValids


  io.taskStatus.zipWithIndex.foreach{
    case(status, i) =>
      status.valid := taskValids(i)
      status.sourceId := taskBuf(i).sourceId
  }

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
    task.bufIdx := 0.U(bufIdxBits.W)
    task.needProbeAckData := false.B
    task.mshrTask := false.B
    task.mshrId := 0.U(mshrBits.W)
    task.aliasTask.foreach(_ := false.B)
    task.useProbeData := false.B
    task.pbIdx := 0.U(mshrBits.W)
    task.dirty := false.B
    task.way := 0.U(wayBits.W)
    task.meta := 0.U.asTypeOf(new MetaEntry)
    task.metaWen := false.B
    task.tagWen := false.B
    task.dsWen := false.B
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

  when (io.c.fire() && isRelease && last && (!io.toReqArb.ready || taskArb.io.out.valid)) {
    when (hasData) {
      taskValids(nextPtrReg) := true.B
      taskBuf(nextPtrReg) := toTaskBundle(io.c.bits)
      taskBuf(nextPtrReg).bufIdx := nextPtrReg
    }.otherwise {
      taskValids(nextPtr) := true.B
      taskBuf(nextPtr) := toTaskBundle(io.c.bits)
      taskBuf(nextPtr).bufIdx := nextPtr
    }
  }

  taskArb.io.out.ready := io.toReqArb.ready
  taskArb.io.in.zipWithIndex.foreach {
    case (in, i) =>
      in.valid := taskValids(i)
      in.bits := taskBuf(i)
      when (in.fire()) {
        taskValids(i) := false.B
      }
  }

  when (io.bufRead.valid) {
    // beatValids(io.bufRead.bits.bufIdx).foreach(_ := false.B)
    beatValids(io.bufRead.bits.bufIdx).foreach(_ := !io.bufRead.bits.bufInvalid)
  }

  val cValid = io.c.valid && isRelease && last

  def getMSHRSameSetVec(valid: Bool, set: UInt) = {
    val mshrSameSetVec = VecInit(io.mshrStatus.map { status =>
      status.valid && valid && status.bits.set === set
    })
    mshrSameSetVec
  }
  def getOccWayVec(valid: Bool, set: UInt) = {
    val mshrSameSetVec = getMSHRSameSetVec(valid, set)
    val occWay = mshrSameSetVec.zip(io.mshrStatus).map{
      case(sameSet, status) => 
        Mux(sameSet, UIntToOH(status.bits.way), 0.U(cacheParams.ways.W))
    }.reduce(_|_)
    occWay
  }
  val occWay = Mux(taskArb.io.out.valid, getOccWayVec(true.B, taskArb.io.out.bits.set), getOccWayVec(true.B, parseAddress(io.c.bits.address)._2))


  io.toReqArb.valid := cValid || taskArb.io.out.valid
  io.toReqArb.bits := Mux(taskArb.io.out.valid, taskArb.io.out.bits, toTaskBundle(io.c.bits))
  io.toReqArb.bits.bufIdx := Mux(taskArb.io.out.valid, taskArb.io.out.bits.bufIdx, nextPtrReg)
  io.toReqArb.bits.wayMask := ~occWay
  io.toReqArb.bits.clientWayMask := Fill(clientWays, 1.U)

  io.resp := DontCare
  io.resp.valid := io.c.fire && (first || last) && !isRelease
  io.resp.mshrId := 0.U // DontCare
  io.resp.tag := parseAddress(io.c.bits.address)._1
  io.resp.set := parseAddress(io.c.bits.address)._2
  io.resp.respInfo.opcode := io.c.bits.opcode
  io.resp.respInfo.param := io.c.bits.param
  io.resp.respInfo.last := last
  io.resp.respInfo.dirty := io.c.bits.opcode(0)
  io.resp.respInfo.source := io.c.bits.source

  io.releaseBufWrite := DontCare
  io.releaseBufWrite.valid := io.c.valid && io.c.bits.opcode === ProbeAckData
  io.releaseBufWrite.bits.beat_sel := UIntToOH(beat)
  io.releaseBufWrite.bits.data.data := Fill(beatSize, io.c.bits.data)
  io.releaseBufWrite.bits.id := 0.U(mshrBits.W) // id is given by MSHRCtl by comparing address to the MSHRs

  // io.c.ready := !isRelease || !first || !full || !hasData && io.toReqArb.ready
  io.c.ready := !(isRelease && first && full && (hasData || !io.toReqArb.ready)) && !(isProbeAck && hasData && !io.releaseBufWrite.ready)

  // when(RegNext(io.c.valid && isProbeAck && hasData && !io.releaseBufWrite.ready)) {
  //   printf(p"ProbeAckData want to write releaseBuf and releaseBuf is not ready! address: ${io.c.bits.address} source: ${io.c.bits.source}")
  // }

  io.bufResp.data := dataBuf(io.bufRead.bits.bufIdx)

  // Performance counters
  val stall = io.c.valid && isRelease && !io.c.ready
  XSPerfAccumulate(cacheParams, "sinkC_c_stall", stall)
  XSPerfAccumulate(cacheParams, "sinkC_c_stall_for_noSpace", stall && hasData && first && full)
  XSPerfAccumulate(cacheParams, "sinkC_toReqArb_stall", io.toReqArb.valid && !io.toReqArb.ready)
  XSPerfAccumulate(cacheParams, "sinkC_buf_full", full)
}