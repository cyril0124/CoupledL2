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
import chisel3.util.{DecoupledIO, _}
import org.chipsalliance.cde.config.Parameters
import freechips.rocketchip.tilelink._
import xs.utils.perf.HasPerfLogging
import xs.utils.tl.MemReqSource

class BMergeTask(implicit p: Parameters) extends L2Bundle {
  val id = UInt(mshrBits.W)
  val task = new TaskBundle()
}

class SinkB(implicit p: Parameters) extends L2Module with HasPerfLogging{
  val io = IO(new Bundle() {
    val b = Flipped(DecoupledIO(new TLBundleB(edgeIn.bundle)))
    val task = DecoupledIO(new TaskBundle)
    val msInfo = Vec(mshrsAll, Flipped(ValidIO(new MSHRInfo)))
    val s3Info = Flipped(ValidIO(new Bundle() {
      val tag = UInt(tagBits.W)
      val set = UInt(setBits.W)
      val willAllocMshr = Bool()
    }))
    val bMergeTask = ValidIO(new BMergeTask)
  })

  def fromTLBtoTaskBundle(b: TLBundleB): TaskBundle = {
    val task = Wire(new TaskBundle)
    task.channel := "b010".U
    task.tag := parseAddress(b.address)._1
    task.set := parseAddress(b.address)._2
    task.off := parseAddress(b.address)._3
    task.alias.foreach(_ := 0.U)
    task.vaddr.foreach(_ := 0.U)
    task.opcode := b.opcode
    task.param := b.param
    task.size := b.size
    task.sourceId := 0.U(sourceIdBits.W)
    task.bufIdx := 0.U(bufIdxBits.W)
//    task.needProbeAckData := b.data(0) // TODO: parameterize this
    task.needProbeAckData := true.B // TODO: parameterize this
    task.mshrTask := false.B
    task.mshrId := 0.U(mshrBits.W)
    task.aliasTask.foreach(_ := false.B)
    task.useProbeData := false.B
    task.fromL2pft.foreach(_ := false.B)
    task.needHint.foreach(_ := false.B)
    task.dirty := false.B
    task.way := 0.U(wayBits.W)
    task.meta := 0.U.asTypeOf(new MetaEntry)
    task.metaWen := false.B
    task.tagWen := false.B
    task.dsWen := false.B
    task.wayMask := Fill(cacheParams.ways, "b1".U)
    task.reqSource := MemReqSource.NoWhere.id.U // Ignore
    task.replTask := false.B
    task.mergeTask := false.B
    task
  }
  val task = fromTLBtoTaskBundle(io.b.bits)

  /* ======== Merge Nested-B req ======== */
  def sameAddr(a: TaskBundle, s: MSHRInfo): Bool = {
    a.set === s.set && a.tag === s.reqTag
  }
  def sameAddrMeta(a: TaskBundle, s: MSHRInfo): Bool = {
    a.set === s.set && a.tag === s.metaTag
  }
  def addrConflictMask(a: TaskBundle): UInt = VecInit(io.msInfo.map(s =>
    s.valid && sameAddr(a, s.bits) && !s.bits.willFree && !s.bits.nestB)).asUInt
  def replaceConflictMask(a: TaskBundle): UInt = VecInit(io.msInfo.map(s =>
    s.valid && sameAddr(a, s.bits) && s.bits.releaseNotSent && !s.bits.mergeB)).asUInt
  def mergeBMask(a: TaskBundle): UInt = VecInit(io.msInfo.map(s =>
    s.valid && sameAddrMeta(a, s.bits) && s.bits.mergeB)).asUInt

  // unable to accept incoming B req because same-addr as some MSHR REQ
  def addrConflict(a: TaskBundle): Bool = addrConflictMask(a).orR

  // unable to accept incoming B req because same-addr as some MSHR replaced block and cannot nest
  def replaceConflict(a: TaskBundle): Bool = replaceConflictMask(a).orR

  // incoming B can be merged with some MSHR replaced block and able to be accepted
  def mergeB(a: TaskBundle) = mergeBMask(a).orR // TODO: && task.param === toN // only toN can merge with MSHR-Release
  def mergeBId(a: TaskBundle) = OHToUInt(mergeBMask(a))

  // unable to accept incoming B req because same-addr as mainpipe S3
  def s3AddrConflict(a: TaskBundle): Bool = io.s3Info.bits.set === a.set && io.s3Info.bits.tag === a.tag && io.s3Info.bits.willAllocMshr

  val task_temp = WireInit(0.U.asTypeOf(io.task))
  val task_retry = WireInit(0.U.asTypeOf(io.task))
  val taskOutPipe = Queue(task_temp, entries = 1, pipe = true, flow = false) // for timing: mshrCtl <> sinkB <> reqArb
  val taskRetryPipe = Queue(task_retry, entries = 1, pipe = true, flow = true)

  val task_be_sent = Mux(taskRetryPipe.valid, taskRetryPipe.bits, task)
  val task_addrConflict = addrConflict(task_be_sent)
  val task_replaceConflict = replaceConflict(task_be_sent)
  val task_mergeB = mergeB(task_be_sent)
  val task_mergeBId = mergeBId(task_be_sent)
  val task_s3AddrConflict = s3AddrConflict(task_be_sent)

  // when conflict, we block B req from entering SinkB
  // when !conflict and mergeB , we merge B req to MSHR
  task_temp.valid := (io.b.valid || taskRetryPipe.valid) && !task_addrConflict && !task_replaceConflict && !task_mergeB && !task_s3AddrConflict
  task_temp.bits := task_be_sent
  // task_out
  io.task.valid := taskOutPipe.valid
  io.task.bits := taskOutPipe.bits
  taskOutPipe.ready := true.B
  // retry
  task_retry.valid := io.task.valid && !io.task.ready
  task_retry.bits := taskOutPipe.bits
  // task can pass (retry override io.b)
  val task_out_ready = task_mergeB || (task_temp.ready && !task_addrConflict && !task_replaceConflict && !task_s3AddrConflict)
  io.b.ready :=  task_out_ready && !taskRetryPipe.valid
  taskRetryPipe.ready := task_out_ready

  dontTouch(task_temp)
  dontTouch(task_retry)

  val bMergeTask = Wire(Decoupled(new BMergeTask))
  bMergeTask.valid := io.b.valid && task_mergeB && !task_s3AddrConflict
  bMergeTask.bits.id := task_mergeBId
  bMergeTask.bits.task := task
  val bMergeTaskOutPipe = Queue(bMergeTask, entries = 1, pipe = true, flow = false) // for timing: mshrCtl <> sinkB <> mshrCtl
  io.bMergeTask.valid := bMergeTaskOutPipe.valid
  io.bMergeTask.bits := bMergeTaskOutPipe.bits
  bMergeTaskOutPipe.ready := true.B

  //--------------------------------- assert ----------------------------------------//
  val s_addrConflict = addrConflict(io.task.bits)
  val s_replaceConflict = replaceConflict(io.task.bits)

  val mergeB_mshr = WireInit(io.msInfo(io.bMergeTask.bits.id))
  val mergeB_task = WireInit(io.bMergeTask.bits.task)
  val s_mergeB = mergeB_mshr.valid && mergeB_mshr.bits.metaTag === mergeB_task.tag && mergeB_mshr.bits.set === mergeB_task.set && mergeB_mshr.bits.mergeB

  val io_task_can_valid = !s_addrConflict && !s_replaceConflict && !s_mergeB
  val io_bMergeTask_can_valid = s_mergeB
  if(cacheParams.enableAssert) {
    when(io.task.fire){
      assert(io_task_can_valid, "io_task cant valid")
    }
    when(io.bMergeTask.fire){
      assert(io_bMergeTask_can_valid, "io_bMergeTask cant valid")
    }
    dontTouch(s_addrConflict)
    dontTouch(s_replaceConflict)
    dontTouch(mergeB_mshr)
    dontTouch(mergeB_task)
    dontTouch(s_mergeB)
    dontTouch(io_task_can_valid)
    dontTouch(io_bMergeTask_can_valid)
  }

  if(cacheParams.enablePerf) {
    XSPerfAccumulate("io_task_retry", task_retry.valid)
    XSPerfAccumulate("mergeBTask", io.bMergeTask.valid)
    XSPerfAccumulate("mp_s3_block_sinkB", (io.b.valid || taskRetryPipe.valid) && !task_addrConflict && !task_replaceConflict && !task_mergeB && task_s3AddrConflict)
    //!!WARNING: TODO: if this is zero, that means fucntion [Probe merge into MSHR-Release] is never tested, and may have flaws
  }
}
