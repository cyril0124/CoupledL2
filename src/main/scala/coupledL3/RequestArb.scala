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
import utility._
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tilelink.TLMessages._
import chipsalliance.rocketchip.config.Parameters
import coupledL3.utils.XSPerfAccumulate
import coupledL3.noninclusive.ClientDirRead
import chisel3.util.experimental.BoringUtils


class RequestArb(implicit p: Parameters) extends L3Module {
  val io = IO(new Bundle() {
    // receive incoming tasks
    val sinkA    = Flipped(DecoupledIO(new TaskBundle))
    val ATag     = Input(UInt(tagBits.W)) // !TODO: very dirty, consider optimize structure
    val ASet     = Input(UInt(setBits.W)) // To pass A entrance status to MP for blockA-info of ReqBuf
    val sinkEntrance = ValidIO(new L3Bundle {
      val tag = UInt(tagBits.W)
      val set = UInt(setBits.W)
    })

    val sinkB    = Flipped(DecoupledIO(new TLBundleB(edgeOut.bundle)))
    val sinkC    = Flipped(DecoupledIO(new TaskBundle))
    val mshrTask = Flipped(DecoupledIO(new TaskBundle))
    val probeHelperTask = Flipped(DecoupledIO(new TaskBundle))

    // read/write directory
    val dirRead_s1 = DecoupledIO(new DirRead())
    val clientDirRead_s1 = DecoupledIO(new ClientDirRead())

    // send task to mainpipe
    val taskToPipe_s2 = DecoupledIO(new TaskBundle())

    // send mshrBuf read request
    val mshrBufRead_s2 = DecoupledIO(new MSHRBufReadReq)

    // send lookupBuf read request for PutPartialData
    val putDataBufRead_s2 = Flipped(new LookupBufRead)

    // status of each pipeline stage
    val status_s1 = Output(new PipeEntranceStatus)   // set & tag of entrance status
    val status_vec = Vec(2, ValidIO(new PipeStatus)) // whether this stage will flow into SourceD

    // handle set conflict, capacity conflict and nestB
    val fromMSHRCtl = Input(new BlockInfo())
    val fromMainPipe = Input(new BlockInfo())
    val fromGrantBuffer = Input(new Bundle() {
      val blockSinkReqEntrance = new BlockInfo()
      val blockMSHRReqEntrance = Bool()
    })
    val fromProbeHelper = Input(new Bundle{
      val blockSinkA = Bool()
    })

    val mshrTaskInfo = Output(new MSHRTaskInfo)
    val pipeFlow_s1 = Output(Bool())
  })

  // --------------------------------------------------------------------------
  //  Pipeline handshake signals
  // --------------------------------------------------------------------------
  val s0_valid, s0_ready, s0_fire = Wire(Bool())
  val s1_valid, s1_ready, s1_fire = Wire(Bool())
  val s2_valid, s2_ready, s2_fire = Wire(Bool())

  val s1_full = RegInit(false.B)
  val s2_full = RegInit(false.B)


  // --------------------------------------------------------------------------
  //  Reset
  // --------------------------------------------------------------------------
  val resetFinish = RegInit(false.B)
  val resetIdx = RegInit((cacheParams.sets - 1).U)

  // block reqs when reset
  when(!resetFinish) {
    resetIdx := resetIdx - 1.U
  }
  when(resetIdx === 0.U) {
    resetFinish := true.B
  }


  // --------------------------------------------------------------------------
  //  Stage0: 
  // --------------------------------------------------------------------------
  io.mshrTask.ready  := s0_ready
  val mshr_task_s0    = Wire(Valid(new TaskBundle()))
  mshr_task_s0.valid := io.mshrTask.fire()
  mshr_task_s0.bits  := io.mshrTask.bits

  s0_valid := io.mshrTask.valid
  s0_ready := s1_ready
  s0_fire := s0_valid && s1_ready

  // --------------------------------------------------------------------------
  //  Stage1: 
  // --------------------------------------------------------------------------
  // Task generation and pipelining
  def fromTLBtoTaskBundle(b: TLBundleB): TaskBundle = {
    val task = Wire(new TaskBundle)
    task := DontCare
    task.channel := "b010".U
    task.tag := parseAddress(b.address)._1
    task.set := parseAddress(b.address)._2
    task.off := parseAddress(b.address)._3
    task.alias.foreach(_ := 0.U)
    task.opcode := b.opcode
    task.param := b.param
    task.size := b.size
    task.needProbeAckData := b.data(0) // TODO: parameterize this
    task.mshrTask := false.B
    task.wayMask := Fill(cacheParams.ways, "b1".U)
    task.reqSource := MemReqSource.NoWhere.id.U // Ignore
    task
  }

  // latch mshr_task from s0 to s1
  val mshrTask_s1 = RegInit(0.U.asTypeOf(Valid(new TaskBundle())))

  // Channel interaction from s1
  val taskSinkA           = io.sinkA.bits
  val taskSinkB           = fromTLBtoTaskBundle(io.sinkB.bits)
  val taskSinkC           = io.sinkC.bits
  val taskProbeHelper     = io.probeHelperTask.bits
  val blockA = io.fromMSHRCtl.blockA_s1 || io.fromMainPipe.blockA_s1 || io.fromGrantBuffer.blockSinkReqEntrance.blockA_s1 || io.fromProbeHelper.blockSinkA
  val blockB = io.fromMSHRCtl.blockB_s1 || io.fromMainPipe.blockB_s1 || io.fromGrantBuffer.blockSinkReqEntrance.blockB_s1
  val blockC = io.fromMSHRCtl.blockC_s1 || io.fromMainPipe.blockC_s1 || io.fromGrantBuffer.blockSinkReqEntrance.blockC_s1


  val sinkA_valid      = io.sinkA.valid && !blockA
  val sinkB_valid      = io.sinkB.valid && !blockB
  val sinkC_valid      = io.sinkC.valid && !blockC
  val probeHelperValid = io.probeHelperTask.valid && !blockB
  val sinkValids       = VecInit(Seq(sinkC_valid, probeHelperValid, sinkB_valid, sinkA_valid)).asUInt


  val sinkReadyBasic        = io.dirRead_s1.ready && io.clientDirRead_s1.ready && resetFinish && !mshrTask_s1.valid && s2_ready
  val sinkB_ready           = sinkReadyBasic && !blockB && !sinkC_valid
  val probeHelperFire       = probeHelperValid & sinkB_ready
  io.sinkA.ready           := sinkReadyBasic && !blockA && !sinkB_valid && !sinkC_valid && !probeHelperValid // SinkC prior to SinkA & SinkB
  io.sinkB.ready           := sinkB_ready && !probeHelperValid // SinkB prior to SinkA
  io.sinkC.ready           := sinkReadyBasic && !blockC
  io.probeHelperTask.ready := sinkB_ready

  val chnlTask_s1    = Wire(Valid(new TaskBundle()))
  val taskVec         = Seq(taskSinkC, taskProbeHelper, taskSinkB, taskSinkA)
  chnlTask_s1.valid := io.dirRead_s1.ready && io.clientDirRead_s1.ready && sinkValids.orR && resetFinish
  chnlTask_s1.bits  := ParallelPriorityMux(sinkValids, taskVec)

  // mshrTask_s1 is s1_[reg]
  // task_s1 is [wire] to s2_reg
  val task_s1 = Mux(mshrTask_s1.valid, mshrTask_s1, chnlTask_s1)
  dontTouch(task_s1)
  dontTouch(chnlTask_s1)

  // Meta read request
  // only sinkA/B/C tasks need to read directory
  // io.dirRead_s1.valid                       := chnlTask_s1.valid && !mshrTask_s1.valid
  io.dirRead_s1.valid                       := s1_fire && !mshrTask_s1.valid
  io.dirRead_s1.bits.set                    := task_s1.bits.set
  io.dirRead_s1.bits.tag                    := task_s1.bits.tag
  io.dirRead_s1.bits.wayMask                := task_s1.bits.wayMask
  io.dirRead_s1.bits.replacerInfo.opcode    := task_s1.bits.opcode
  io.dirRead_s1.bits.replacerInfo.channel   := task_s1.bits.channel
  io.dirRead_s1.bits.replacerInfo.reqSource := task_s1.bits.reqSource

  // io.clientDirRead_s1.valid                       := chnlTask_s1.valid && !mshrTask_s1.valid
  io.clientDirRead_s1.valid                       := s1_fire && !mshrTask_s1.valid
  io.clientDirRead_s1.bits.set                    := task_s1.bits.set
  io.clientDirRead_s1.bits.tag                    := task_s1.bits.tag
  io.clientDirRead_s1.bits.wayMask                := task_s1.bits.clientWayMask
  io.clientDirRead_s1.bits.replacerInfo.opcode    := task_s1.bits.opcode
  io.clientDirRead_s1.bits.replacerInfo.channel   := task_s1.bits.channel
  io.clientDirRead_s1.bits.replacerInfo.reqSource := task_s1.bits.reqSource

  // probe block same-set A req for s2/s3
  val sink_tag = PriorityMux(Seq(
                  io.sinkC.fire           -> taskSinkC.tag,
                  io.probeHelperTask.fire -> taskProbeHelper.tag,
                  io.sinkB.fire           -> taskSinkB.tag
                ))
  val sink_set = PriorityMux(Seq(
                  io.sinkC.fire           -> taskSinkC.set,
                  io.probeHelperTask.fire -> taskProbeHelper.set,
                  io.sinkB.fire           -> taskSinkB.set
                ))
  io.sinkEntrance.valid     := io.sinkB.fire || io.sinkC.fire || io.probeHelperTask.fire
  io.sinkEntrance.bits.tag  := sink_tag
  io.sinkEntrance.bits.set  := sink_set

  val dirReady = io.dirRead_s1.ready && io.clientDirRead_s1.ready
  s1_valid := mshrTask_s1.valid || chnlTask_s1.valid && dirReady
  s1_ready := (!s1_full || s1_fire) && !io.fromGrantBuffer.blockMSHRReqEntrance
  s1_fire := s1_valid && s2_ready 

  when(s0_fire) {
    s1_full := true.B
  }.elsewhen(s1_fire && task_s1.bits.mshrTask) {
    s1_full := false.B
  }

  when(s0_fire) {
    mshrTask_s1.valid := true.B
    mshrTask_s1.bits := mshr_task_s0.bits
  }.elsewhen(s1_fire && task_s1.bits.mshrTask) {
    mshrTask_s1.valid := false.B
  }

  // --------------------------------------------------------------------------
  //  Stage2: 
  // --------------------------------------------------------------------------
  val task_s2 = RegInit(0.U.asTypeOf(task_s1))
  
  io.taskToPipe_s2.valid := task_s2.valid
  io.taskToPipe_s2.bits := task_s2.bits

  val willReadRefillBuf = WireInit(false.B)
  val willReadReleaseBuf = WireInit(false.B)
  val willReadMSHRBuf = WireInit(false.B)
  s2_valid := s2_full && (
    !(willReadMSHRBuf && !io.mshrBufRead_s2.ready)
  )
  s2_ready := !s2_full || s2_fire
  when(s1_fire) {
    s2_full := true.B
  }.elsewhen(s2_fire) {
    s2_full := false.B
  }

  io.taskToPipe_s2.valid := s2_valid
  when(s1_fire) {
    task_s2.valid := true.B
    task_s2.bits := task_s1.bits
  }.elsewhen(s2_fire) {
    task_s2.valid := false.B
  } 

  s2_fire := s2_valid && io.taskToPipe_s2.ready

  io.mshrTaskInfo.valid := s2_fire && task_s2.valid && task_s2.bits.mshrTask
  io.mshrTaskInfo.mshrId := task_s2.bits.mshrId

  io.pipeFlow_s1 := s1_fire

  // MSHR task
  val mshrTask_s2 = task_s2.valid && task_s2.bits.mshrTask
  val mshrTask_s2_a_upwards = task_s2.bits.fromA && (
      task_s2.bits.opcode === GrantData || task_s2.bits.opcode === Grant ||
      task_s2.bits.opcode === AccessAckData || 
      task_s2.bits.opcode === PutPartialData && !task_s2.bits.putHit && task_s2.bits.opcodeIsReq
  )
  // For GrantData, read refillBuffer
  // Caution: GrantData-alias may read DataStorage or ReleaseBuf instead
  val selfHasData = task_s2.bits.selfHasData
  
  willReadMSHRBuf := !selfHasData && mshrTask_s2 && (
    mshrTask_s2_a_upwards ||  
    (
      task_s2.bits.opcode === ReleaseData ||
      task_s2.bits.fromB && task_s2.bits.opcode === ProbeAckData || 
      task_s2.bits.fromA && task_s2.bits.useProbeData && mshrTask_s2_a_upwards && !selfHasData
    )
  )
  io.mshrBufRead_s2.valid := willReadMSHRBuf
  io.mshrBufRead_s2.bits.id := task_s2.bits.mshrId

  // For PutPartialData, read putDataBuffer
  io.putDataBufRead_s2.valid := mshrTask_s2 && task_s2.bits.opcode === PutPartialData && task_s2.bits.fromA && task_s2.bits.putHit && task_s2.bits.opcodeIsReq && s2_fire
  io.putDataBufRead_s2.id    := task_s2.bits.reqSource

  require(beatSize == 2)

  // status of each pipeline stage
  val b_set = Mux(io.probeHelperTask.valid, taskProbeHelper.set, taskSinkB.set)
  val b_tag = Mux(io.probeHelperTask.valid, taskProbeHelper.tag, taskSinkB.tag)
  io.status_s1.sets            := VecInit(Seq(taskSinkC.set, b_set, io.ASet))
  io.status_s1.tags            := VecInit(Seq(taskSinkC.tag, b_tag, io.ATag))
  io.status_s1.fromProbeHelper := io.probeHelperTask.valid

  require(io.status_vec.size == 2)
  io.status_vec.zip(Seq(task_s1, task_s2)).foreach {
    case (status, task) =>
      status.valid := task.valid
      status.bits.channel := task.bits.channel
      status.bits.set := task.bits.set
      status.bits.mshrTask := task.bits.mshrTask
  }

  dontTouch(io)


  // --------------------------------------------------------------------------
  //  Performance counters 
  // --------------------------------------------------------------------------
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

  XSPerfAccumulate(cacheParams, "sinkA_stall_by_dir", io.sinkA.valid && !blockA && !io.dirRead_s1.ready)
  XSPerfAccumulate(cacheParams, "sinkB_stall_by_dir", io.sinkB.valid && !blockB && !io.dirRead_s1.ready)
  XSPerfAccumulate(cacheParams, "sinkC_stall_by_dir", io.sinkC.valid && !blockC && !io.dirRead_s1.ready)

  XSPerfAccumulate(cacheParams, "sinkA_stall_by_sinkB", io.sinkA.valid && sinkReadyBasic && !blockA && sinkValids(1) && !sinkValids(0))
  XSPerfAccumulate(cacheParams, "sinkA_stall_by_sinkC", io.sinkA.valid && sinkReadyBasic && !blockA && sinkValids(0))
  XSPerfAccumulate(cacheParams, "sinkB_stall_by_sinkC", io.sinkB.valid && sinkReadyBasic && !blockB && sinkValids(0))

  XSPerfAccumulate(cacheParams, "sinkA_stall_by_mshrTask", io.sinkA.valid && mshrTask_s1.valid)
  XSPerfAccumulate(cacheParams, "sinkB_stall_by_mshrTask", io.sinkB.valid && mshrTask_s1.valid)
  XSPerfAccumulate(cacheParams, "sinkC_stall_by_mshrTask", io.sinkC.valid && mshrTask_s1.valid)
}
