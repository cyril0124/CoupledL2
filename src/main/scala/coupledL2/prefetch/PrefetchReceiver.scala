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

import org.chipsalliance.cde.config.Parameters
import chisel3._
import chisel3.util._
import freechips.rocketchip.tilelink._
import freechips.rocketchip.diplomacy.{BundleBridgeSink,BundleBridgeSource, LazyModule, LazyModuleImp}
import coupledL2._
import xs.utils.Pipeline
import huancun.PrefetchRecv
import xs.utils.RegNextN
import xs.utils.ValidIODelay
import xs.utils.RRArbiterInit

// TODO: PrefetchReceiver is temporarily used since L1&L2 do not support Hint.
// TODO: Delete this after Hint is accomplished.

case class PrefetchReceiverParams(n: Int = 32) extends PrefetchParameters {
  override val hasPrefetchBit: Boolean = true
  override val inflightEntries: Int = n
}

class PrefetchReceiver()(implicit p: Parameters) extends PrefetchModule {
  val io = IO(new Bundle() {
    val req = DecoupledIO(new PrefetchReq)
    val recv_addr = Flipped(ValidIO(UInt(64.W)))
  })
  val recv_reg = RegEnable(io.recv_addr.bits,io.recv_addr.valid)
  io.req.valid := RegNext(io.recv_addr.valid,false.B)
  io.req.bits.tag := parseFullAddress(recv_reg)._1
  io.req.bits.set := parseFullAddress(recv_reg)._2
  io.req.bits.needT := false.B
  io.req.bits.isBOP := false.B
  io.req.bits.source := 0.U // TODO: ensure source 0 is dcache
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
     val arbiter = Module(new RRArbiterInit(new LlcPrefetchRecv, clientNum))
     arbiter.suggestName(s"pf_l3recv_node_arb")
     for (i <- 0 until clientNum) {
      val s0_valid = inNode(i).in.head._1.addr_valid
      val s0_req = inNode(i).in.head._1
      val s1_valid = RegNextN(s0_valid,1)
      val s1_req = RegEnable(s0_req,s0_valid)
       arbiter.io.in(i).valid           := s1_valid
       arbiter.io.in(i).bits.addr_valid := s1_req.addr_valid
       arbiter.io.in(i).bits.addr       := s1_req.addr
       arbiter.io.in(i).bits.needT      := s1_req.needT
       arbiter.io.in(i).bits.source     := s1_req.source
       arbiter.io.in(i).ready := DontCare
     }
     arbiter.io.out.valid := DontCare
     val delayPipe = Module(new Pipeline(new LlcPrefetchRecv, 1))
     delayPipe.io.in <> arbiter.io.out

     outNode.head.out.head._1.addr_valid := delayPipe.io.out.valid
     outNode.head.out.head._1.addr       := delayPipe.io.out.bits.addr
     outNode.head.out.head._1.needT      := delayPipe.io.out.bits.needT
     outNode.head.out.head._1.source     := delayPipe.io.out.bits.source
     arbiter.io.out.ready := true.B
     delayPipe.io.out.ready := true.B
   }
 }
