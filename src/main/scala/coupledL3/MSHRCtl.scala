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
import chipsalliance.rocketchip.config.Parameters
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tilelink.TLMessages._
import coupledL3.prefetch.PrefetchTrain
import coupledL3.utils.{XSPerfAccumulate, XSPerfHistogram, XSPerfMax}

class MSHRSelector(implicit p: Parameters) extends L3Module {
  val io = IO(new Bundle() {
    val idle = Input(Vec(mshrsAll, Bool()))
    val out = ValidIO(UInt(mshrsAll.W))
  })
  io.out.valid := ParallelOR(io.idle)
  io.out.bits := ParallelPriorityMux(io.idle.zipWithIndex.map {
    case (b, i) => (b, (1 << i).U)
  })
}

class MSHRTaskInfo(implicit p: Parameters) extends L3Bundle {
  val valid = Bool()
  val mshrId = UInt(mshrBits.W)
}

class MSHRCtl(implicit p: Parameters) extends L3Module with noninclusive.HasClientInfo{
  val io = IO(new Bundle() {
    /* interact with req arb */
    val fromReqArb = Input(new Bundle() {
      val status_s1 = new PipeEntranceStatus
      val mshrTaskInfo = new MSHRTaskInfo
    })
    val toReqArb = Output(new BlockInfo())

    /* interact with mainpipe */
    val fromMainPipe = new Bundle() {
      val mshr_alloc_s3 = Flipped(ValidIO(new MSHRRequest))
    }
    val toMainPipe = new Bundle() {
      val mshr_alloc_ptr = Output(UInt(mshrBits.W))
    }

    /* to request arbiter */
    // val mshrFull = Output(Bool())
    val mshrTask = DecoupledIO(new TaskBundle())

    /* send reqs */
    val sourceA = DecoupledIO(new TLBundleA(edgeOut.bundle))
    val sourceB = DecoupledIO(new TLBundleB(edgeIn.bundle))
    val grantStatus = Input(Vec(grantQueueEntries, new GrantStatus))


    /* receive resps */
    val resps = Input(new Bundle() {
      val sinkC = new RespBundle
      val sinkD = new RespBundle
      val sinkE = new RespBundle
      val sourceC = new RespBundle
    })
    
    val releaseBufWriteId = Output(UInt(mshrBits.W))

    /* nested writeback */
    val nestedwb = Input(new NestedWriteback)
    val nestedwbDataId = Output(ValidIO(UInt(mshrBits.W)))

    val probeHelperWakeup = Input(new ProbeHelperWakeupInfo) // Only for NINE

    /* read putBuffer */
//    val pbRead = DecoupledIO(new PutBufferRead)
//    val pbResp = Flipped(ValidIO(new PutBufferEntry))

    /* status of s2 and s3 */
    // val pipeStatusVec = Flipped(Vec(2, ValidIO(new PipeStatus)))
    val pipeStatusVec = Flipped(Vec(3, ValidIO(new PipeStatus)))


    /* to ReqBuffer / SinkC, to solve conflict */
    val toReqBuf = Vec(mshrsAll, ValidIO(new MSHRBlockAInfo))
    val toSinkC = Output(new Bundle{
      val mshrFull = Bool()
    })

    val fromReqBufSinkA = Input(new Bundle{
      val valid = Bool()
      val set = UInt(setBits.W)
    })

    /* for TopDown Monitor */
    val msStatus = topDownOpt.map(_ => Vec(mshrsAll, ValidIO(new MSHRStatus)))
  })

  val mshrs = Seq.fill(mshrsAll) { Module(new MSHR()) }
  val mshrValids = VecInit(mshrs.map(m => m.io.status.valid))

  val s2s3PipeStatusVec = VecInit(Seq(io.pipeStatusVec(1), io.pipeStatusVec(2)))
  // val pipeReqCount = PopCount(Cat(io.pipeStatusVec.map(_.valid))) // TODO: consider add !mshrTask to optimize
  val pipeReqCount = PopCount(Cat(s2s3PipeStatusVec.map(status => status.valid && !status.bits.mshrTask))) // TODO: consider add !mshrTask to optimize
  // val pipeReqCount = PopCount(Cat(s2s3PipeStatusVec.map(status => status.valid))) // TODO: consider add !mshrTask to optimize
  val mshrCount = PopCount(Cat(mshrs.map(_.io.status.valid)))
  val mshrFull = pipeReqCount + mshrCount >= mshrsAll.U
  val b_mshrFull = pipeReqCount + mshrCount >= (mshrsAll-1).U
  val a_mshrFull = pipeReqCount + mshrCount >= (mshrsAll-2).U // the last idle mshr should not be allocated for channel A req
  val mshrSelector = Module(new MSHRSelector())
  mshrSelector.io.idle := mshrs.map(m => !m.io.status.valid)
  val selectedMSHROH = mshrSelector.io.out.bits
  io.toMainPipe.mshr_alloc_ptr := OHToUInt(selectedMSHROH)

  val resp_sinkC_match_vec = mshrs.map { mshr =>
    val mshr_valid = mshr.io.status.valid && mshr.io.status.bits.w_c_resp

    mshr_valid &&
      io.resps.sinkC.set === mshr.io.status.bits.set &&
      io.resps.sinkC.tag === mshr.io.status.bits.tag
  }

  val blockMatchVec = mshrs.map{ mshr => 
    val pipeSetMatch = Cat(io.pipeStatusVec.map{ pipeStatus => 
        pipeStatus.valid && !pipeStatus.bits.mshrTask && pipeStatus.bits.set === mshr.io.status.bits.set && pipeStatus.bits.fromC
    }).orR
    mshr.io.status.valid && pipeSetMatch
  }

  val mshrTaskInfoMatchVec = mshrs.map{ mshr =>
    mshr.io.status.valid && mshr.io.id === io.fromReqArb.mshrTaskInfo.mshrId && io.fromReqArb.mshrTaskInfo.valid
  }

  mshrs.zipWithIndex.foreach {
    case (m, i) =>
      m.io.id := i.U
      m.io.alloc.valid := selectedMSHROH(i) && io.fromMainPipe.mshr_alloc_s3.valid
      m.io.alloc.bits := io.fromMainPipe.mshr_alloc_s3.bits

      m.io.resps.sink_c.valid := io.resps.sinkC.valid && resp_sinkC_match_vec(i)
      m.io.resps.sink_c.bits := io.resps.sinkC.respInfo
      m.io.resps.sink_d.valid := m.io.status.valid && io.resps.sinkD.valid && io.resps.sinkD.mshrId === i.U
      m.io.resps.sink_d.bits := io.resps.sinkD.respInfo
      m.io.resps.sink_e.valid := m.io.status.valid && io.resps.sinkE.valid && io.resps.sinkE.mshrId === i.U
      m.io.resps.sink_e.bits := io.resps.sinkE.respInfo
      m.io.resps.source_c.valid := m.io.status.valid && io.resps.sourceC.valid && io.resps.sourceC.mshrId === i.U
      m.io.resps.source_c.bits := io.resps.sourceC.respInfo
      
      m.io.nestedwb := io.nestedwb
      m.io.probeHelperWakeup := io.probeHelperWakeup

      m.io.block := blockMatchVec(i)
      m.io.mshrTaskIsFire := mshrTaskInfoMatchVec(i)

      io.toReqBuf(i) := m.io.toReqBuf
  }

  val setMatchVec_b = mshrs.map(m => m.io.status.valid && m.io.status.bits.set === io.fromReqArb.status_s1.b_set)
  // val setConflictVec_b = (setMatchVec_b zip mshrs.map(_.io.status.bits.nestB)).map(x => x._1 && !x._2)
  val setConflictVec_b = (setMatchVec_b zip mshrs.map(_.io.status.bits.nestB)).map(x => x._1 && !x._2)
  val setConflictVec_b_1 = setConflictVec_b.zip(mshrs.map(_.io.status.bits)).map{
    case(conflict, channel) => conflict && (io.fromReqArb.status_s1.fromProbeHelper && channel.fromC || !io.fromReqArb.status_s1.fromProbeHelper)
  } 

  def getMSHRSameSetVec(valid: Bool, set: UInt) = {
    val mshrSameSetVec = VecInit(io.toReqBuf.map { status =>
      status.valid && valid && status.bits.set === set
    })
    mshrSameSetVec
  }
  def getOccWayVec(valid: Bool, set: UInt) = {
    val mshrSameSetVec = getMSHRSameSetVec(valid, set)
    val occWay = mshrSameSetVec.zip(io.toReqBuf).map{
      case(sameSet, status) => 
        Mux(sameSet, UIntToOH(status.bits.way), 0.U(cacheParams.ways.W))
    }.reduce(_|_)
    occWay
  }
  val occWay = getOccWayVec(true.B, io.fromReqArb.status_s1.c_set)
  val hasEmptyWay = ~occWay.andR
  
  val setMatchVec_c = mshrs.map(m => m.io.status.valid && m.io.status.bits.set === io.fromReqArb.status_s1.c_set)
  val setConflictVec_c = (setMatchVec_c zip mshrs.map(_.io.status.bits.nestC)).map(x => x._1 && !x._2)
  
  // val clientSetMatch_a = mshrs.map(m => m.io.status.valid && m.io.status.bits.fromC && io.fromReqBufSinkA.valid && m.io.status.bits.set(clientSetBits - 1, 0) === io.fromReqBufSinkA.set(clientSetBits - 1, 0))
  io.toReqArb.blockC_s1 := mshrFull || Cat(setConflictVec_c).orR //|| !hasEmptyWay
  io.toReqArb.blockB_s1 := b_mshrFull || Cat(setConflictVec_b).orR
  io.toReqArb.blockA_s1 := a_mshrFull //|| Cat(clientSetMatch_a).orR // conflict logic moved to ReqBuf

  /* Acquire downwards */
  val acquireUnit = Module(new AcquireUnit())
  fastArb(mshrs.map(_.io.tasks.source_a), acquireUnit.io.task, Some("source_a"))
  io.sourceA <> acquireUnit.io.sourceA
//  io.pbRead <> acquireUnit.io.pbRead
//  io.pbResp <> acquireUnit.io.pbResp

  /* Probe upwards */
  val sourceB = Module(new SourceB())
  fastArb(mshrs.map(_.io.tasks.source_b), sourceB.io.task, Some("source_b"))
  sourceB.io.grantStatus := io.grantStatus
  io.sourceB <> sourceB.io.sourceB

  /* Arbitrate MSHR task to RequestArbiter */
  fastArb(mshrs.map(_.io.tasks.mainpipe), io.mshrTask, Some("mshr_task"))

  io.toSinkC.mshrFull := mshrFull

  io.releaseBufWriteId := ParallelPriorityMux(resp_sinkC_match_vec, (0 until mshrsAll).map(i => i.U))

  io.nestedwbDataId.valid := Cat(mshrs.map(_.io.nestedwbData)).orR
  io.nestedwbDataId.bits := ParallelPriorityMux(mshrs.zipWithIndex.map {
    case (mshr, i) => (mshr.io.nestedwbData, i.U)
  })

  dontTouch(io.sourceA)

  topDownOpt.foreach (_ =>
    io.msStatus.get.zip(mshrs).foreach {
      case (in, s) => in := s.io.status
    }
  )
  // Performance counters
  XSPerfAccumulate(cacheParams, "capacity_conflict_to_sinkA", a_mshrFull)
  XSPerfAccumulate(cacheParams, "capacity_conflict_to_sinkB", mshrFull)
  //  XSPerfAccumulate(cacheParams, "set_conflict_to_sinkA", Cat(setMatchVec_a).orR) //TODO: move this to ReqBuf
  XSPerfAccumulate(cacheParams, "set_conflict_to_sinkB", Cat(setConflictVec_b).orR)
  XSPerfHistogram(cacheParams, "mshr_alloc", io.toMainPipe.mshr_alloc_ptr,
    enable = io.fromMainPipe.mshr_alloc_s3.valid,
    start = 0, stop = mshrsAll, step = 1)
  
  if (cacheParams.enablePerf) {
    val start = 0
    val stop = 100
    val step = 5
    val acquire_period = ParallelMux(mshrs.map { case m => m.io.resps.sink_d.valid -> m.acquire_period })
    val release_period = ParallelMux(mshrs.map { case m => m.io.resps.sink_d.valid -> m.release_period })
    val probe_period = ParallelMux(mshrs.map { case m => m.io.resps.sink_c.valid -> m.probe_period })
    val acquire_period_en = io.resps.sinkD.valid &&
      (io.resps.sinkD.respInfo.opcode === Grant || io.resps.sinkD.respInfo.opcode === GrantData)
    val release_period_en = io.resps.sinkD.valid && io.resps.sinkD.respInfo.opcode === ReleaseAck
    val probe_period_en = io.resps.sinkC.valid &&
      (io.resps.sinkC.respInfo.opcode === ProbeAck || io.resps.sinkC.respInfo.opcode === ProbeAckData)
    XSPerfHistogram(cacheParams, "acquire_period", acquire_period, acquire_period_en, start, stop, step)
    XSPerfHistogram(cacheParams, "release_period", release_period, release_period_en, start, stop, step)
    XSPerfHistogram(cacheParams, "probe_period", probe_period, probe_period_en, start, stop, step)

    val timers = RegInit(VecInit(Seq.fill(mshrsAll)(0.U(64.W))))
    for (((timer, m), i) <- timers.zip(mshrs).zipWithIndex) {
      when (m.io.alloc.valid) {
        timer := 1.U
      }.otherwise {
        timer := timer + 1.U
      }
      val enable = m.io.status.valid && m.io.status.bits.will_free
      XSPerfHistogram(cacheParams, "mshr_latency_" + Integer.toString(i, 10),
        timer, enable, 0, 300, 10)
      XSPerfMax(cacheParams, "mshr_latency", timer, enable)
    }
  }
}
