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
import utility._
import chipsalliance.rocketchip.config.Parameters
import freechips.rocketchip.tilelink._
import coupledL2._
import coupledL2.utils.{XSPerfAccumulate, XSPerfHistogram}

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
  val evict = prefetchOpt.get match {
    case hyper: HyperPrefetchParams => Some(Flipped(DecoupledIO(new PrefetchEvict)))
    case _ => None
  }
  val hint2llc = if(sppMultiLevelRefillOpt.nonEmpty)  Some(ValidIO(new PrefetchReq)) else None
}

class PrefetchQueue(implicit p: Parameters) extends PrefetchModule {
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
  XSPerfAccumulate(cacheParams, "prefetch_queue_enq", io.enq.fire())
  XSPerfAccumulate(cacheParams, "prefetch_queue_fromL1_enq", io.enq.fire() && !io.enq.bits.isBOP)
  XSPerfAccumulate(cacheParams, "prefetch_queue_fromL2_enq", io.enq.fire() && io.enq.bits.isBOP)
  XSPerfAccumulate(cacheParams, "prefetch_queue_deq", io.deq.fire())
  XSPerfAccumulate(cacheParams, "prefetch_queue_fromL1_deq", io.deq.fire() && !io.enq.bits.isBOP)
  XSPerfAccumulate(cacheParams, "prefetch_queue_fromL2_enq", io.deq.fire() && io.enq.bits.isBOP)
  XSPerfHistogram(cacheParams, "prefetch_queue_entry", PopCount(valids.asUInt),
    true.B, 0, inflightEntries, 1)
}

class Prefetcher(implicit p: Parameters) extends PrefetchModule {
  val io = IO(new PrefetchIO)
  val io_l2_pf_en = IO(Input(Bool()))

  val (counterValue, counterWrap) = Counter(true.B, 1024)
  val deadPfEviction = RegInit(0.U(13.W))
  val issued = RegInit(0.U(16.W))
  val pf_state = WireInit(0.U(2.W))
  dontTouch(pf_state)
  io.evict match {
    case Some(evict) =>
    when(evict.valid && evict.bits.is_prefetch) {
      deadPfEviction := deadPfEviction + 1.U
    }
    case None =>
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
    case spp: SPPParameters => // case spp only
      val pft = Module(new SignaturePathPrefetch)
      val pftQueue = Module(new PrefetchQueue)
      val pipe = Module(new Pipeline(io.req.bits.cloneType, 1))
      pft.io.train <> io.train
      pft.io.resp <> io.resp
      pftQueue.io.enq <> pft.io.req
      pipe.io.in <> pftQueue.io.deq
      io.req <> pipe.io.out
      io.hint2llc match{
      case Some(sender) =>
        println(s"${cacheParams.name} Prefetch Config: SPP + SPP cross-level refill")
        pftQueue.io.enq.valid := pft.io.req.valid && (!pft.io.hint2llc)
        pftQueue.io.enq.bits <> pft.io.req.bits
        pipe.io.in <> pftQueue.io.deq
        io.req <> pipe.io.out
        sender.valid := pft.io.hint2llc
        sender.bits := pft.io.req.bits
      case _ =>
        println(s"${cacheParams.name} Prefetch Config: SPP")
        pftQueue.io.enq <> pft.io.req
        pipe.io.in <> pftQueue.io.deq
        io.req <> pipe.io.out
    }
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
      l1_pf.io.train <> DontCare
      l1_pf.io.resp <> DontCare
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
      XSPerfAccumulate(cacheParams, "prefetch_req_fromL1", l1_pf.io.req.valid)
      XSPerfAccumulate(cacheParams, "prefetch_req_fromL2", bop_en && bop.io.req.valid)
      XSPerfAccumulate(cacheParams, "prefetch_req_L1L2_overlapped", l1_pf.io.req.valid && bop_en && bop.io.req.valid)
    
    case hyperPf: HyperPrefetchParams => // case spp +  bop + smsReceiver
      val hybrid_pfts = Module(new HyperPrefetcher())
      val pftQueue = Module(new PrefetchQueue)
      val pipe = Module(new Pipeline(io.req.bits.cloneType, 1))
      hybrid_pfts.io.train <> io.train
      hybrid_pfts.io.resp <> io.resp
      hybrid_pfts.io.recv_addr := ValidIODelay(io.recv_addr, 2)
      io.evict match {
        case Some(evict) =>
        hybrid_pfts.io.evict <> evict
        pftQueue.io.enq <> hybrid_pfts.io.req
        pipe.io.in <> pftQueue.io.deq
        io.req <> pipe.io.out
        case None =>
        hybrid_pfts.io.evict := DontCare
      }
      // has spp multi-level cache option
      io.hint2llc match{
        case Some(sender) =>
          println(s"${cacheParams.name} Prefetch Config: BOP + SMS receiver + SPP + SPP cross-level refill")
          sender <> hybrid_pfts.io.hint2llc
        case _ => println(s"${cacheParams.name} Prefetch Config: BOP + SMS receiver + SPP")
      }
      hybrid_pfts.io.queue_used := pftQueue.io.used
      hybrid_pfts.io.db_degree.valid := counterWrap
      hybrid_pfts.io.db_degree.bits := pf_state
    case _ => assert(cond = false, "Unknown prefetcher")
  }
  XSPerfAccumulate(cacheParams, "prefetch_train", io.train.fire())
  XSPerfAccumulate(cacheParams, "prefetch_train_on_miss", io.train.fire() && io.train.bits.state === AccessState.MISS)
  XSPerfAccumulate(cacheParams, "prefetch_train_on_pf_hit", io.train.fire() && io.train.bits.state === AccessState.PREFETCH_HIT)
  XSPerfAccumulate(cacheParams, "prefetch_train_on_cache_hit", io.train.fire() && io.train.bits.state === AccessState.HIT)
  XSPerfAccumulate(cacheParams, "prefetch_send2_pfq", io.req.fire())
  XSPerfHistogram(cacheParams, "prefetch_dead_block", deadPfEviction, counterWrap, 0, 200, 5)
  XSPerfHistogram(cacheParams, "prefetch_dead_ratio", pf_state, counterWrap, 0, 4, 1)
}
