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

import chisel3._
import chisel3.util._
import xs.utils._
import org.chipsalliance.cde.config.Parameters
import freechips.rocketchip.tilelink._
import coupledL2._
import xs.utils.perf.HasPerfLogging
import intel_spp.{PrefetchBranchV2Params,PrefetchBranchV2}

object AccessState {
  val bits = 2

  def MISS          = 0.U(bits.W)
  def HIT           = 1.U(bits.W)
  def PREFETCH_HIT  = 2.U(bits.W)
  def LATE_HIT      = 3.U(bits.W)
}

class PrefetchReq(implicit p: Parameters) extends PrefetchBundle {
  val tag = UInt(fullTagBits.W)
  val set = UInt(setBits.W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
  val isBOP = Bool()
  def addr = Cat(tag, set, 0.U(offsetBits.W))
}

class PrefetchResp(implicit p: Parameters) extends PrefetchBundle {
  // val id = UInt(sourceIdBits.W)
  val tag = UInt(fullTagBits.W)
  val set = UInt(setBits.W)
  def addr = Cat(tag, set, 0.U(offsetBits.W))
}

class PrefetchTrain(implicit p: Parameters) extends PrefetchBundle {
  // val addr = UInt(addressBits.W)
  val tag = UInt(fullTagBits.W)
  val set = UInt(setBits.W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
  val vaddr = vaddrBitsOpt.map(_ => UInt(vaddrBitsOpt.get.W))
  // prefetch only when L2 receives a miss or prefetched hit req
  // val miss = Bool()
  // val prefetched = Bool()
  val state = UInt(AccessState.bits.W)
  def addr = Cat(tag, set, 0.U(offsetBits.W))
}

class PrefetchEvict(implicit p: Parameters) extends PrefetchBundle {
  // val id = UInt(sourceIdBits.W)
  val tag = UInt(fullTagBits.W)
  val set = UInt(setBits.W)
  val is_prefetch = Bool()
  def addr = Cat(tag, set, 0.U(offsetBits.W))
}

class PrefetchIO(implicit p: Parameters) extends PrefetchBundle {
  val train = Flipped(DecoupledIO(new PrefetchTrain))
  val req = DecoupledIO(new PrefetchReq)
  val resp = Flipped(DecoupledIO(new PrefetchResp))
  val recv_addr = Flipped(ValidIO(UInt(64.W)))
  val evict = Flipped(DecoupledIO(new PrefetchEvict))
  val hint2llc = if(sppMultiLevelRefillOpt.nonEmpty)  Some(ValidIO(new PrefetchReq)) else None
}

class PrefetchQueue(implicit p: Parameters) extends PrefetchModule with HasPerfLogging{
  val io = IO(new Bundle {
    val enq = Flipped(DecoupledIO(new PrefetchReq))
    val deq = DecoupledIO(new PrefetchReq)
    val used = Output(UInt(6.W))
  })
  /*  Here we implement a queue that
   *  1. is pipelined  2. flows
   *  3. always has the latest reqs, which means the queue is always ready for enq and deserting the eldest ones
   */
  val queue = RegInit(VecInit(Seq.fill(inflightEntries)(0.U.asTypeOf(new PrefetchReq))))
  val valids = RegInit(VecInit(Seq.fill(inflightEntries)(false.B)))
  val idxWidth = log2Up(inflightEntries)
  val head = RegInit(0.U(idxWidth.W))
  val tail = RegInit(0.U(idxWidth.W))
  val empty = head === tail && !valids.last
  val full = head === tail && valids.last

  when(!empty && io.deq.ready) {
    valids(head) := false.B
    head := head + 1.U
  }

  when(io.enq.valid) {
    val exist = queue.zipWithIndex.map{case (x, i) => Mux(valids(i) && x.addr === io.enq.bits.addr, true.B, false.B)}.reduce(_ || _)
    when(!exist) {
      queue(tail) := io.enq.bits
      valids(tail) := !empty || !io.deq.ready // true.B
      tail := tail + (!empty || !io.deq.ready).asUInt
      when(full && !io.deq.ready) {
        head := head + 1.U
      }
    }
  }

  io.enq.ready := true.B
  io.deq.valid := !empty || io.enq.valid
  io.deq.bits := Mux(empty, io.enq.bits, queue(head))

  io.used := PopCount(valids.asUInt)

  // The reqs that are discarded = enq - deq
  XSPerfAccumulate( "prefetch_queue_enq", io.enq.fire)
  XSPerfAccumulate( "prefetch_queue_fromL1_enq", io.enq.fire && !io.enq.bits.isBOP)
  XSPerfAccumulate( "prefetch_queue_fromL2_enq", io.enq.fire && io.enq.bits.isBOP)
  XSPerfAccumulate( "prefetch_queue_deq", io.deq.fire)
  XSPerfAccumulate( "prefetch_queue_fromL1_deq", io.deq.fire && !io.enq.bits.isBOP)
  XSPerfAccumulate( "prefetch_queue_fromL2_enq", io.deq.fire && io.enq.bits.isBOP)
  XSPerfHistogram( "prefetch_queue_entry", PopCount(valids.asUInt),
    true.B, 0, inflightEntries, 1)
}

class Prefetcher(parentName:String="Unkown")(implicit p: Parameters) extends PrefetchModule with HasPerfLogging {
  val io = IO(new PrefetchIO)
  val io_l2_pf_en = IO(Input(Bool()))
  val io_l2_pf_ctrl = IO(Input(UInt(2.W)))
  dontTouch(io_l2_pf_en)  
  dontTouch(io_l2_pf_ctrl)
  val (counterValue, counterWrap) = Counter(true.B, 1024)
  val deadPfEviction = RegInit(0.U(13.W))
  val issued = RegInit(0.U(16.W))
  val pf_state = WireInit(0.U(2.W))
  dontTouch(pf_state)
  when(io.evict.valid && io.evict.bits.is_prefetch) {
    deadPfEviction := deadPfEviction + 1.U
  }
  when(io.req.fire) {
    issued := issued + 1.U
  }
  when(counterWrap) {
    deadPfEviction := 0.U
    issued := 0.U
    // deadPfEviction/issued > 0.75, 
    when((deadPfEviction << 2) > issued + issued + issued) {
      pf_state := 3.U
    } .elsewhen((deadPfEviction << 1) > issued) {
      pf_state := 2.U
    } .elsewhen((deadPfEviction << 2) > issued) {
      pf_state := 1.U
    } .otherwise {
      pf_state := 0.U
    }
  }

  prefetchOpt.get match {
    case branch2: PrefetchBranchV2Params => 
      val hybrid_pfts = Module(new PrefetchBranchV2())
      val pftQueue = Module(new PrefetchQueue)
      val pipe = Module(new Pipeline(io.req.bits.cloneType, 1))
      hybrid_pfts.io.train <> io.train
      hybrid_pfts.io.resp <> io.resp
      hybrid_pfts.io.recv_addr := ValidIODelay(io.recv_addr, 2)
      hybrid_pfts.io.evict <> io.evict
      pftQueue.io.enq <> hybrid_pfts.io.req
      pipe.io.in <> pftQueue.io.deq
      io.req <> pipe.io.out
    case bop: BOPParameters => // case bop only
      println(s"${cacheParams.name} Prefetch Config: BOP")
      val pft = Module(new BestOffsetPrefetch)
      val pftQueue = Module(new PrefetchQueue)
      val pipe = Module(new Pipeline(io.req.bits.cloneType, 1))
      pft.io.train <> io.train
      pft.io.resp <> io.resp
      pftQueue.io.enq <> pft.io.req
      pipe.io.in <> pftQueue.io.deq
      io.req <> pipe.io.out
    case receiver: PrefetchReceiverParams => // case sms+bop 
      println(s"${cacheParams.name} Prefetch Config: BOP + SMS receiver")
      val l1_pf = Module(new PrefetchReceiver())
      val bop = Module(new BestOffsetPrefetch()(p.alterPartial({
        case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(BOPParameters()))
      })))
      val pftQueue = Module(new PrefetchQueue)
      val pipe = Module(new Pipeline(io.req.bits.cloneType, 1))
      val bop_en = RegNextN(io_l2_pf_en, 2, Some(true.B))
      // l1 prefetch
      l1_pf.io.recv_addr := ValidIODelay(io.recv_addr, 2)
      // l1_pf.io.train <> DontCare
      // l1_pf.io.resp <> DontCare
      // l2 prefetch
      bop.io.train <> io.train
      bop.io.resp <> io.resp
      // send to prq
      pftQueue.io.enq.valid := l1_pf.io.req.valid || (bop_en && bop.io.req.valid)
      pftQueue.io.enq.bits := Mux(l1_pf.io.req.valid,
        l1_pf.io.req.bits,
        bop.io.req.bits
      )
      l1_pf.io.req.ready := true.B
      bop.io.req.ready := true.B
      pipe.io.in <> pftQueue.io.deq
      io.req <> pipe.io.out
      XSPerfAccumulate( "prefetch_req_fromL1", l1_pf.io.req.valid)
      XSPerfAccumulate( "prefetch_req_fromL2", bop_en && bop.io.req.valid)
      XSPerfAccumulate( "prefetch_req_L1L2_overlapped", l1_pf.io.req.valid && bop_en && bop.io.req.valid)
    case _ => assert(cond = false, "Unknown prefetcher")
  }
  XSPerfAccumulate( "prefetch_train", io.train.fire)
  XSPerfAccumulate( "prefetch_train_on_miss", io.train.fire && io.train.bits.state === AccessState.MISS)
  XSPerfAccumulate( "prefetch_train_on_pf_hit", io.train.fire && io.train.bits.state === AccessState.PREFETCH_HIT)
  XSPerfAccumulate( "prefetch_train_on_cache_hit", io.train.fire && io.train.bits.state === AccessState.HIT)
  XSPerfAccumulate( "prefetch_send2_pfq", io.req.fire)
  XSPerfHistogram(  "prefetch_dead_block", deadPfEviction, counterWrap, 0, 200, 5)
  XSPerfHistogram(  "prefetch_dead_ratio", pf_state, counterWrap, 0, 4, 1)
}
