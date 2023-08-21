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
import utility._
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tilelink.TLMessages._
import chipsalliance.rocketchip.config.Parameters
import coupledL2.utils.XSPerfAccumulate

class RequestArb(implicit p: Parameters) extends L2Module {
  val io = IO(new Bundle() {
    /* receive incoming tasks */
    val sinkA    = Flipped(DecoupledIO(new TaskBundle))
    val ATag     = Input(UInt(tagBits.W)) // !TODO: very dirty, consider optimize structure
    val ASet     = Input(UInt(setBits.W)) // To pass A entrance status to MP for blockA-info of ReqBuf
    val sinkEntrance = ValidIO(new L2Bundle {
      val tag = UInt(tagBits.W)
      val set = UInt(setBits.W)
    })

    val sinkB    = Flipped(DecoupledIO(new TLBundleB(edgeOut.bundle)))
    val sinkC    = Flipped(DecoupledIO(new TaskBundle))
    val mshrTask = Flipped(DecoupledIO(new TaskBundle))

    /* read/write directory */
    val dirRead_s1 = DecoupledIO(new DirRead())  // To directory, read meta/tag

    /* send task to mainpipe */
    val taskToPipe_s2 = ValidIO(new TaskBundle())
    /* send s1 task info to mainpipe to help hint */
    val taskInfo_s1 = ValidIO(new TaskBundle())

    /* send mshrBuf read request */
    val refillBufRead_s2 = Flipped(new MSHRBufRead)
    val releaseBufRead_s2 = Flipped(new MSHRBufRead)

    /* status of each pipeline stage */
    val status_s1 = Output(new PipeEntranceStatus) // set & tag of entrance status
    val status_vec = Vec(2, ValidIO(new PipeStatus)) // whether this stage will flow into SourceD

    /* handle set conflict, capacity conflict and nestB */
    val fromMSHRCtl = Input(new BlockInfo())
    val fromMainPipe = Input(new BlockInfo())
    val fromGrantBuffer = Input(new Bundle() {
      val blockSinkReqEntrance = new BlockInfo()
      val blockMSHRReqEntrance = Bool()
    })
  })

  /* ======== Reset ======== */
  val resetFinish = RegInit(false.B)
  val resetIdx = RegInit((cacheParams.sets - 1).U)
  /* block reqs when reset */
  when(!resetFinish) {
    resetIdx := resetIdx - 1.U
  }
  when(resetIdx === 0.U) {
    resetFinish := true.B
  }
  // val valids = RegInit(0.U(8.W))  // 7 stages

  /* ======== Stage 0 ======== */
  io.mshrTask.ready := !io.fromGrantBuffer.blockMSHRReqEntrance
  val mshr_task_s0 = Wire(Valid(new TaskBundle()))
  mshr_task_s0.valid := io.mshrTask.fire()
  mshr_task_s0.bits := io.mshrTask.bits

  /* ======== Stage 1 ======== */
  /* Task generation and pipelining */
  def fromTLBtoTaskBundle(b: TLBundleB): TaskBundle = {
    val task = Wire(new TaskBundle)
    task.channel := "b010".U
    task.tag := parseAddress(b.address)._1
    task.set := parseAddress(b.address)._2
    task.off := parseAddress(b.address)._3
    task.alias.foreach(_ := 0.U)
    task.opcode := b.opcode
    task.param := b.param
    task.size := b.size
    task.sourceId := 0.U(sourceIdBits.W)
    task.bufIdx := 0.U(bufIdxBits.W)
    task.needProbeAckData := b.data(0) // TODO: parameterize this
    task.mshrTask := false.B
    task.mshrId := 0.U(mshrBits.W)
    task.aliasTask.foreach(_ := false.B)
    task.useProbeData := false.B
    task.pbIdx := 0.U(mshrBits.W)
    task.fromL2pft.foreach(_ := false.B)
    task.needHint.foreach(_ := false.B)
    task.needHint2llc.foreach(_ := false.B)
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

  /* latch mshr_task from s0 to s1 */
  val mshr_task_s1 = RegInit(0.U.asTypeOf(Valid(new TaskBundle())))
  mshr_task_s1.valid := mshr_task_s0.valid
  when(mshr_task_s0.valid) {
    mshr_task_s1.bits := mshr_task_s0.bits
  }

  /* Channel interaction from s1 */
  val A_task = io.sinkA.bits
  val B_task = fromTLBtoTaskBundle(io.sinkB.bits)
  val C_task = io.sinkC.bits
  val block_A = io.fromMSHRCtl.blockA_s1 || io.fromMainPipe.blockA_s1 || io.fromGrantBuffer.blockSinkReqEntrance.blockA_s1
  val block_B = io.fromMSHRCtl.blockB_s1 || io.fromMainPipe.blockB_s1 || io.fromGrantBuffer.blockSinkReqEntrance.blockB_s1
  val block_C = io.fromMSHRCtl.blockC_s1 || io.fromMainPipe.blockC_s1 || io.fromGrantBuffer.blockSinkReqEntrance.blockC_s1

  val sinkValids = VecInit(Seq(
    io.sinkC.valid && !block_C,
    io.sinkB.valid && !block_B,
    io.sinkA.valid && !block_A
  )).asUInt

  val sink_ready_basic = io.dirRead_s1.ready && resetFinish && !mshr_task_s1.valid
  io.sinkA.ready := sink_ready_basic && !block_A && !sinkValids(1) && !sinkValids(0) // SinkC prior to SinkA & SinkB
  io.sinkB.ready := sink_ready_basic && !block_B && !sinkValids(0) // SinkB prior to SinkA
  io.sinkC.ready := sink_ready_basic && !block_C

  val chnl_task_s1 = Wire(Valid(new TaskBundle()))
  chnl_task_s1.valid := io.dirRead_s1.ready && sinkValids.orR && resetFinish
  chnl_task_s1.bits := ParallelPriorityMux(sinkValids, Seq(C_task, B_task, A_task))

  // mshr_task_s1 is s1_[reg]
  // task_s1 is [wire] to s2_reg
  val task_s1 = Mux(mshr_task_s1.valid, mshr_task_s1, chnl_task_s1)

  io.taskInfo_s1 := mshr_task_s1

  /* Meta read request */
  // ^ only sinkA/B/C tasks need to read directory
  io.dirRead_s1.valid := chnl_task_s1.valid && !mshr_task_s1.valid
  io.dirRead_s1.bits.set := task_s1.bits.set
  io.dirRead_s1.bits.tag := task_s1.bits.tag
  io.dirRead_s1.bits.wayMask := task_s1.bits.wayMask
  io.dirRead_s1.bits.replacerInfo.opcode := task_s1.bits.opcode
  io.dirRead_s1.bits.replacerInfo.channel := task_s1.bits.channel
  io.dirRead_s1.bits.replacerInfo.reqSource := task_s1.bits.reqSource

  // probe block same-set A req for s2/s3
  io.sinkEntrance.valid := io.sinkB.fire || io.sinkC.fire
  io.sinkEntrance.bits.tag  := Mux(io.sinkC.fire, C_task.tag, B_task.tag)
  io.sinkEntrance.bits.set  := Mux(io.sinkC.fire, C_task.set, B_task.set)

  /* ========  Stage 2 ======== */
  val task_s2 = RegInit(0.U.asTypeOf(task_s1))
  task_s2.valid := task_s1.valid
  when(task_s1.valid) { task_s2.bits := task_s1.bits }
  
  io.taskToPipe_s2 := task_s2

  // MSHR task
  val mshrTask_s2 = task_s2.valid && task_s2.bits.mshrTask
  val mshrTask_s2_a_upwards = task_s2.bits.fromA &&
    (task_s2.bits.opcode === GrantData || task_s2.bits.opcode === Grant ||
      task_s2.bits.opcode === AccessAckData || task_s2.bits.opcode === HintAck && task_s2.bits.dsWen)
  // For GrantData, read refillBuffer
  // Caution: GrantData-alias may read DataStorage or ReleaseBuf instead
  io.refillBufRead_s2.valid := mshrTask_s2 && !task_s2.bits.useProbeData && mshrTask_s2_a_upwards
  io.refillBufRead_s2.id := task_s2.bits.mshrId
  // For ReleaseData or ProbeAckData, read releaseBuffer
  // channel is used to differentiate GrantData and ProbeAckData
  io.releaseBufRead_s2.valid := mshrTask_s2 && (
    task_s2.bits.opcode === ReleaseData ||
    task_s2.bits.fromB && task_s2.bits.opcode === ProbeAckData ||
    task_s2.bits.fromA && task_s2.bits.useProbeData && mshrTask_s2_a_upwards)
  io.releaseBufRead_s2.id := task_s2.bits.mshrId
  assert(!io.refillBufRead_s2.valid || io.refillBufRead_s2.ready)
  assert(!io.releaseBufRead_s2.valid || io.releaseBufRead_s2.ready)

  require(beatSize == 2)

  /* status of each pipeline stage */
  io.status_s1.sets := VecInit(Seq(C_task.set, B_task.set, io.ASet))
  io.status_s1.tags := VecInit(Seq(C_task.tag, B_task.tag, io.ATag))
  require(io.status_vec.size == 2)
  io.status_vec.zip(Seq(task_s1, task_s2)).foreach {
    case (status, task) =>
      status.valid := task.valid
      status.bits.channel := task.bits.channel
  }

  dontTouch(io)

  // Performance counters
  XSPerfAccumulate(cacheParams, "mshr_req", mshr_task_s0.valid)
  XSPerfAccumulate(cacheParams, "mshr_req_stall", io.mshrTask.valid && !io.mshrTask.ready)

  XSPerfAccumulate(cacheParams, "sinkA_req", io.sinkA.fire())
  XSPerfAccumulate(cacheParams, "sinkB_req", io.sinkB.fire())
  XSPerfAccumulate(cacheParams, "sinkC_req", io.sinkC.fire())
  
  XSPerfAccumulate(cacheParams, "sinkA_stall", io.sinkA.valid && !io.sinkA.ready)
  XSPerfAccumulate(cacheParams, "sinkB_stall", io.sinkB.valid && !io.sinkB.ready)
  XSPerfAccumulate(cacheParams, "sinkC_stall", io.sinkC.valid && !io.sinkC.ready)

  XSPerfAccumulate(cacheParams, "sinkA_stall_by_mshr", io.sinkA.valid && io.fromMSHRCtl.blockA_s1)
  XSPerfAccumulate(cacheParams, "sinkB_stall_by_mshr", io.sinkB.valid && io.fromMSHRCtl.blockB_s1)

  XSPerfAccumulate(cacheParams, "sinkA_stall_by_mainpipe", io.sinkA.valid && io.fromMainPipe.blockA_s1)
  XSPerfAccumulate(cacheParams, "sinkB_stall_by_mainpipe", io.sinkB.valid && io.fromMainPipe.blockB_s1)
  XSPerfAccumulate(cacheParams, "sinkC_stall_by_mainpipe", io.sinkC.valid && io.fromMainPipe.blockC_s1)

  XSPerfAccumulate(cacheParams, "sinkA_stall_by_grantbuf", io.sinkA.valid && io.fromGrantBuffer.blockSinkReqEntrance.blockA_s1)
  XSPerfAccumulate(cacheParams, "sinkB_stall_by_grantbuf", io.sinkB.valid && io.fromGrantBuffer.blockSinkReqEntrance.blockB_s1)
  XSPerfAccumulate(cacheParams, "sinkC_stall_by_grantbuf", io.sinkC.valid && io.fromGrantBuffer.blockSinkReqEntrance.blockC_s1)

  XSPerfAccumulate(cacheParams, "sinkA_stall_by_dir", io.sinkA.valid && !block_A && !io.dirRead_s1.ready)
  XSPerfAccumulate(cacheParams, "sinkB_stall_by_dir", io.sinkB.valid && !block_B && !io.dirRead_s1.ready)
  XSPerfAccumulate(cacheParams, "sinkC_stall_by_dir", io.sinkC.valid && !block_C && !io.dirRead_s1.ready)

  XSPerfAccumulate(cacheParams, "sinkA_stall_by_sinkB", io.sinkA.valid && sink_ready_basic && !block_A && sinkValids(1) && !sinkValids(0))
  XSPerfAccumulate(cacheParams, "sinkA_stall_by_sinkC", io.sinkA.valid && sink_ready_basic && !block_A && sinkValids(0))
  XSPerfAccumulate(cacheParams, "sinkB_stall_by_sinkC", io.sinkB.valid && sink_ready_basic && !block_B && sinkValids(0))

  XSPerfAccumulate(cacheParams, "sinkA_stall_by_mshrTask", io.sinkA.valid && mshr_task_s1.valid)
  XSPerfAccumulate(cacheParams, "sinkB_stall_by_mshrTask", io.sinkB.valid && mshr_task_s1.valid)
  XSPerfAccumulate(cacheParams, "sinkC_stall_by_mshrTask", io.sinkC.valid && mshr_task_s1.valid)

  XSPerfAccumulate(cacheParams, "sinkA_req_hint_to_LLC", io.sinkA.fire()&&io.sinkA.bits.needHint2llc.getOrElse(false.B))
}
