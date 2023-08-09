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

package coupledL2.prefetch

import chipsalliance.rocketchip.config.Parameters
import chisel3._
import chisel3.util._
import freechips.rocketchip.tilelink._
import freechips.rocketchip.diplomacy.{BundleBridgeSink,BundleBridgeSource, LazyModule, LazyModuleImp}
import coupledL2._
import utility.Pipeline
import huancun.PrefetchRecv

// TODO: PrefetchReceiver is temporarily used since L1&L2 do not support Hint.
// TODO: Delete this after Hint is accomplished.

case class PrefetchReceiverParams(n: Int = 32) extends PrefetchParameters {
  override val hasPrefetchBit: Boolean = true
  override val inflightEntries: Int = n
}

class PrefetchReceiver()(implicit p: Parameters) extends PrefetchModule {
  val io = IO(new PrefetchIO())
  // just ignore train reqs
  io.train.ready := true.B
  io.resp.ready := true.B
  io.hint2llc match{
    case Some(x) => x := DontCare
    case _ => None
  }
  io.req.bits.tag := parseFullAddress(io.recv_addr.bits)._1
  io.req.bits.set := parseFullAddress(io.recv_addr.bits)._2
  io.req.bits.needT := false.B
  io.req.bits.isBOP := false.B
  io.req.bits.source := 0.U // TODO: ensure source 0 is dcache
  io.req.valid := io.recv_addr.valid

}

// fake sms send node fo TL_Test / Cocotb
class PrefetchSmsOuterNode(val clientNum:Int=2)(implicit p: Parameters) extends LazyModule{
  val outNode = BundleBridgeSource(Some(() => new coupledL2.PrefetchRecv()))
  lazy val module = new LazyModuleImp(this){
    val prefetchRecv = outNode.out.head._1
    prefetchRecv.addr := 0.U
    prefetchRecv.addr_valid := false.B
    prefetchRecv.l2_pf_en := true.B
  }
}

// null node
class SppSenderNull(val clientNum:Int=2)(implicit p: Parameters) extends LazyModule{
  val outNode = Seq.fill(clientNum)(BundleBridgeSource(Some(() => new coupledL2.LlcPrefetchRecv())))
  lazy val module = new LazyModuleImp(this){
    for (i <- 0 until clientNum) {
      outNode(i).out.head._1.addr_valid := DontCare
      outNode(i).out.head._1.addr       := DontCare
      outNode(i).out.head._1.needT      := DontCare
      outNode(i).out.head._1.source     := DontCare
    }
  }
}

// spp sender/receiver xbar
class PrefetchReceiverXbar(val clientNum:Int=2)(implicit p: Parameters) extends LazyModule{
  val inNode = Seq.fill(clientNum)(BundleBridgeSink(Some(() => new coupledL2.LlcPrefetchRecv)))
  val outNode = Seq.fill(1)(BundleBridgeSource(Some(() => new huancun.LlcPrefetchRecv)))
  lazy val module = new LazyModuleImp(this){
    val arbiter = Module(new Arbiter(new LlcPrefetchRecv, clientNum))
    arbiter.suggestName(s"pf_l3recv_node_arb")
    for (i <- 0 until clientNum) {
      arbiter.io.in(i).valid := inNode(i).in.head._1.addr_valid
      arbiter.io.in(i).bits.addr_valid := inNode(i).in.head._1.addr_valid
      arbiter.io.in(i).bits.addr       := inNode(i).in.head._1.addr
      arbiter.io.in(i).bits.needT      := inNode(i).in.head._1.needT
      arbiter.io.in(i).bits.source      := inNode(i).in.head._1.source
      arbiter.io.in(i).ready := DontCare
    }
    arbiter.io.out.valid := DontCare
    outNode.head.out.head._1.addr_valid := arbiter.io.out.bits.addr_valid
    outNode.head.out.head._1.addr       := arbiter.io.out.bits.addr
    outNode.head.out.head._1.needT      := arbiter.io.out.bits.needT
    outNode.head.out.head._1.source     := arbiter.io.out.bits.source
    arbiter.io.out.ready := true.B
  }
}
