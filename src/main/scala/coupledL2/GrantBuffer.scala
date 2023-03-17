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
import chipsalliance.rocketchip.config.Parameters
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tilelink.TLMessages._
import coupledL2.prefetch.PrefetchResp
import coupledL2.utils.{XSPerfAccumulate, XSPerfHistogram}

// Communicate with L1
// Send out Grant/GrantData/ReleaseAck from d and
// receive GrantAck through e
class GrantBuffer(implicit p: Parameters) extends L2Module {
  val io = IO(new Bundle() {
    val d_task = Flipped(DecoupledIO(new Bundle() {
      val task = new TaskBundle()
      val data = new DSBlock()
    }))
    val d = DecoupledIO(new TLBundleD(edgeIn.bundle))
    val e = Flipped(DecoupledIO(new TLBundleE(edgeIn.bundle)))
    val e_resp = Output(new RespBundle)

    val fromReqArb = Input(new Bundle() {
      val status_s1 = new PipeEntranceStatus
    })
    val pipeStatusVec = Flipped(Vec(5, ValidIO(new PipeStatus)))
    val toReqArb = Output(new Bundle() {
      val blockSinkReqEntrance = new BlockInfo()
      val blockMSHRReqEntrance = Bool()
    })
    val prefetchResp = prefetchOpt.map(_ => DecoupledIO(new PrefetchResp))
  })

  val beat_valids = RegInit(VecInit(Seq.fill(mshrsAll) {
    VecInit(Seq.fill(beatSize)(false.B))
  }))
  val block_valids = VecInit(beat_valids.map(_.asUInt.orR)).asUInt
  val taskAll = Reg(Vec(mshrsAll, new TaskBundle))
  val dataAll = Reg(Vec(mshrsAll, new DSBlock))
  val full = block_valids.andR
  val selectOH = ParallelPriorityMux(~block_valids, (0 until mshrsAll).map(i => (1 << i).U))

  // used to block Probe upwards
  val inflight_grant_entry = new L2Bundle(){
    val valid = Bool()
    val set = UInt(setBits.W)
    val tag = UInt(tagBits.W)
    val sink = UInt(mshrBits.W)
  }
  // sourceIdAll (= L1 Ids) entries
  val inflight_grant = RegInit(VecInit(Seq.fill(sourceIdAll)(0.U.asTypeOf(inflight_grant_entry))))

  when (io.d_task.fire() && io.d_task.bits.task.opcode(2, 1) === Grant(2, 1)) {
    // choose an empty entry
    val valids = VecInit(inflight_grant.map(_.valid)).asUInt
    val insertIdx = PriorityEncoder(~valids)
    val entry = inflight_grant(insertIdx)
    entry.valid := true.B
    entry.set := io.d_task.bits.task.set
    entry.tag := io.d_task.bits.task.tag
    entry.sink := io.d_task.bits.task.mshrId
  }
  when (io.e.fire) {
    // compare sink to clear buffer
    val sinkMatchVec = inflight_grant.map(g => g.valid && g.sink === io.e.bits.sink)
    assert(PopCount(sinkMatchVec) === 1.U, "GrantBuf: there must be one and only one match")
    val bufIdx = OHToUInt(sinkMatchVec)
    inflight_grant(bufIdx).valid := false.B
  }

  // handle capacity conflict of GrantBuffer
  // count the number of valid blocks + those in pipe that might use GrantBuf
  // so that GrantBuffer will not exceed capacity
  val noSpaceForSinkReq = PopCount(Cat(VecInit(io.pipeStatusVec.tail.map { case s =>
    s.valid && (s.bits.fromA || s.bits.fromC)
  }).asUInt, block_valids)) >= mshrsAll.U
  val noSpaceForMSHRReq = PopCount(Cat(VecInit(io.pipeStatusVec.map { case s =>
    s.valid && s.bits.fromA
  }).asUInt, block_valids)) >= mshrsAll.U

  io.toReqArb.blockSinkReqEntrance.blockA_s1 := Cat(inflight_grant.map(g => g.valid &&
    g.set === io.fromReqArb.status_s1.a_set && g.tag === io.fromReqArb.status_s1.a_tag)).orR || noSpaceForSinkReq
  io.toReqArb.blockSinkReqEntrance.blockB_s1 := Cat(inflight_grant.map(g => g.valid &&
    g.set === io.fromReqArb.status_s1.b_set && g.tag === io.fromReqArb.status_s1.b_tag)).orR
  io.toReqArb.blockSinkReqEntrance.blockC_s1 := noSpaceForSinkReq
  io.toReqArb.blockMSHRReqEntrance := noSpaceForMSHRReq

  selectOH.asBools.zipWithIndex.foreach {
    case (sel, i) =>
      when (sel && io.d_task.fire() && !(io.d_task.bits.task.opcode === HintAck && !io.d_task.bits.task.fromL2pft.getOrElse(false.B))) {
        beat_valids(i).foreach(_ := true.B)
        taskAll(i) := io.d_task.bits.task
        dataAll(i) := io.d_task.bits.data
      }
  }
  // If no prefetch, there never should be HintAck
  assert(prefetchOpt.nonEmpty.B || !io.d_task.valid || io.d_task.bits.task.opcode =/= HintAck)

  def toTLBundleD(task: TaskBundle, data: UInt = 0.U) = {
    val d = Wire(new TLBundleD(edgeIn.bundle))
    d := DontCare
    d.opcode := task.opcode
    d.param := task.param
    d.size := offsetBits.U
    d.source := task.sourceId
    d.sink := task.mshrId
    d.denied := false.B
    d.data := data
    d.corrupt := false.B
    d
  }

  def getBeat(data: UInt, beatsOH: UInt): (UInt, UInt) = {
    // get one beat from data according to beatsOH
    require(data.getWidth == (blockBytes * 8))
    require(beatsOH.getWidth == beatSize)
    // next beat
    val next_beat = ParallelPriorityMux(beatsOH, data.asTypeOf(Vec(beatSize, UInt((beatBytes * 8).W))))
    val selOH = PriorityEncoderOH(beatsOH)
    // remaining beats that haven't been sent out
    val next_beatsOH = beatsOH & ~selOH
    (next_beat, next_beatsOH)
  }

  val out_bundles = Wire(Vec(mshrsAll, io.d.cloneType))
  out_bundles.zipWithIndex.foreach {
    case (out, i) =>
      out.valid := block_valids(i) && taskAll(i).opcode =/= HintAck // L1 does not need HintAck (for now)
      val data = dataAll(i).data
      val beatsOH = beat_valids(i).asUInt
      val (beat, next_beatsOH) = getBeat(data, beatsOH)
      out.bits := toTLBundleD(taskAll(i), beat)
      val hasData = out.bits.opcode(0)

      when (out.fire()) {
        when (hasData) {
          beat_valids(i) := VecInit(next_beatsOH.asBools)
        }.otherwise {
          beat_valids(i).foreach(_ := false.B)
        }
      }
  }

  val pft_resps = prefetchOpt.map(_ => Wire(Vec(mshrsAll, DecoupledIO(new PrefetchResp))))
  io.prefetchResp.zip(pft_resps).foreach {
    case (out, ins) =>
      ins.zipWithIndex.foreach {
        case (in, i) =>
          in.valid := block_valids(i) && taskAll(i).opcode === HintAck
          in.bits.tag := taskAll(i).tag
          in.bits.set := taskAll(i).set
          when (in.fire()) {
            beat_valids(i).foreach(_ := false.B)
          }
      }
      fastArb(ins, out, Some("pft_resp_arb"))
  }

  TLArbiter.robin(edgeIn, io.d, out_bundles:_*)

  io.d_task.ready := !full

  // GrantBuf should always be ready.
  // If not, block reqs at the entrance of the pipeline when GrantBuf is about to be full.
  assert(!io.d_task.valid || io.d_task.ready) 

  io.e.ready := true.B
  io.e_resp := DontCare
  io.e_resp.valid := io.e.valid
  io.e_resp.mshrId := io.e.bits.sink
  io.e_resp.respInfo := DontCare
  io.e_resp.respInfo.opcode := GrantAck
  io.e_resp.respInfo.last := true.B

  XSPerfAccumulate(cacheParams, "grant_buffer_full", full)

  if (cacheParams.enablePerf) {
    val timers = Reg(Vec(sourceIdAll, UInt(64.W)))
    when (io.d_task.fire() && io.d_task.bits.task.opcode(2, 1) === Grant(2, 1)) {
      val id = io.d_task.bits.task.mshrId(sourceIdBits-1, 0)
      timers(id) := 1.U
    }
    timers.zipWithIndex.foreach {
      case (timer, i) =>
        when (inflight_grant(i).valid) { timer := timer + 1.U }
    }
    val t = WireInit(0.U(64.W))
    when (io.e.fire()) {
      val id = io.e.bits.sink(sourceIdBits-1, 0)
      timers(id) := 0.U
      t := timers(id)
    }
    XSPerfHistogram(cacheParams, "grant_grantack_period", t, io.e.fire(),
      0, 10, 1)
  }
}