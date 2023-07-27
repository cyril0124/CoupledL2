
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
import coupledL3.utils._
import freechips.rocketchip.tilelink._
import chipsalliance.rocketchip.config.Parameters
import utility._

class GrantStatus(implicit p: Parameters) extends L3Bundle {
  val valid  = Bool()
  val set     = UInt(setBits.W)
  val tag     = UInt(tagBits.W)
}

class ProbeEntry(implicit p: Parameters) extends L3Bundle {
  val valid = Bool()
  val rdy   = Bool()
  val waitG = UInt(sourceIdBits.W) // grantEntry probe is waiting for, sourceId as Idx
  val task  = new SourceBReq()
}

// send B reqs to upper level cache
// Attention! We stall Probes if there is same-addr Grant not received GrantAck
class SourceB(implicit p: Parameters) extends L3Module {
  val io = IO(new Bundle() {
    val sourceB = DecoupledIO(new TLBundleB(edgeIn.bundle))
    val task = Flipped(DecoupledIO(new SourceBReq))
    val grantStatus = Input(Vec(sourceIdAll, new GrantStatus))
  })

  def toTLBundleB(task: SourceBReq) = {
    val b = Wire(new TLBundleB(edgeIn.bundle))
    b.opcode  := task.opcode
    b.param   := task.param
    b.size    := offsetBits.U
    if (cacheParams.name  == "l3") {
      println("Is L3")
      b.source  := getSourceId(task.clients)

      when(io.sourceB.valid) {
        assert(PopCount(task.clients) === 1.U)
      }
    } else { // L3
      println("Is L3")
      b.source  := 0.U // make sure there are only 1 client
    }
    b.address := Cat(task.tag, task.set, 0.U(offsetBits.W))
    b.mask    := Fill(beatBytes, 1.U(1.W))
    b.data := Cat(task.alias.getOrElse(0.U), task.needData) // this is the same as HuanCun // TODO: for L3
    b.corrupt := false.B
    b
  }

  /* ======== Data Structure ======== */
  // TODO: check XSPerf whether 4 entries is enough
  val entries = if(cacheParams.name == "l3") 8 else 4
  val probes  = RegInit(VecInit(
    Seq.fill(entries)(0.U.asTypeOf(new ProbeEntry))
  ))
//  val workVecs = RegInit(VecInit(
//    Seq.fill(entries)(0.U.asTypeOf(UInt(clientBits.W)))
//  ))

  /* ======== Enchantment ======== */
  val full  = Cat(probes.map(_.valid)).andR

  // comparing with #sourceIdAll entries might have timing issues
  // but worry not, we can delay cycles cuz not critical
  val conflictMask = io.grantStatus.map(s =>
    s.valid && s.set === io.task.bits.set && s.tag === io.task.bits.tag
  )
  val conflict     = Cat(conflictMask).orR

  val noReadyEntry = Wire(Bool())
  val canFlow      = noReadyEntry && !conflict && PopCount(io.task.bits.clients) === 1.U
  val flow         = canFlow && io.sourceB.ready

  /* ======== Alloc ======== */
  io.task.ready   := !full || flow

  val insertIdx = PriorityEncoder(probes.map(!_.valid))
  val alloc     = !full && io.task.valid && !flow
  when(alloc) {
    val p = probes(insertIdx)
    p.valid := true.B
    p.rdy   := !conflict
    p.waitG := OHToUInt(conflictMask)
    p.task  := io.task.bits
    assert(PopCount(conflictMask) <= 1.U)
    assert(PopCount(io.task.bits.clients) =/= 0.U, "Non-clients probe! set:0x%x tag:0x%x", io.task.bits.set, io.task.bits.tag)
//    val workVec = workVecs(insertIdx)
//    workVec := io.task.bits.clients
  }

  /* ======== Issue ======== */
  val issueArb = Module(new FastArbiter(new SourceBReq, entries))
  issueArb.io.in zip probes foreach{
    case (i, p) =>
      i.valid := p.valid && p.rdy
      i.bits  := p.task
      val pendingClient = p.task.clients
      val chosenClient = ParallelPriorityMux(pendingClient.asBools.zipWithIndex.map {
        case (sel, i) => sel -> UIntToOH(i.U, width = clientBits)
      })
      i.bits.clients := chosenClient

      val issueComplete = i.fire && PopCount(pendingClient) === 1.U
      dontTouch(issueComplete)
      
      when(issueComplete) {
        p.valid := false.B
      }.elsewhen(i.fire) {
        assert(PopCount(p.task.clients) =/= 1.U)
        pendingClient := pendingClient & ~chosenClient
      }
  }
  issueArb.io.out.ready := io.sourceB.ready
  noReadyEntry := !issueArb.io.out.valid

  /* ======== Update rdy ======== */
  probes foreach { p =>
    when(p.valid && !io.grantStatus(p.waitG).valid) {
      p.rdy := RegNext(true.B) // cuz GrantData has 2 beats, can move RegNext elsewhere
    }
  }

  /* ======== Output ======== */
  io.sourceB.valid := issueArb.io.out.valid || (io.task.valid && canFlow)
  io.sourceB.bits  := toTLBundleB(
    Mux(canFlow, io.task.bits, issueArb.io.out.bits)
  )

  /* ======== Perf ======== */
  for(i <- 0 until entries){
    val update = PopCount(probes.map(_.valid)) === i.U
    XSPerfAccumulate(cacheParams, s"probe_buffer_util_$i", update)
  }
}
