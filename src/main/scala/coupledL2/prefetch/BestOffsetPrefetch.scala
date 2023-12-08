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

import xs.utils.sram.{SRAMReadBus, SRAMTemplate, SRAMWriteBus}
import org.chipsalliance.cde.config.Parameters
import chisel3._
import chisel3.util._
import coupledL2.HasCoupledL2Parameters
import xs.utils.perf.HasPerfLogging

case class BOPParameters(
  rrTableEntries: Int = 256,
  rrTagBits:      Int = 12,
  scoreBits:      Int = 5,
  roundMax:       Int = 50,
  badScore:       Int = 1,
  delayCycle:     Int = 200,
  delayEntries:   Int = 64,
  offsetList: Seq[Int] = Seq(
    -32, -30, -27, -25, -24, -20, -18, -16, -15,
    -12, -10,  -9,  -8,  -6,  -5,  -4,  -3,  -2,  -1,
      1,   2,   3,   4,   5,   6,   8,   9,  10,
     12,  15,  16,  18,  20,  24,  25,  27,  30//,
    /*32,  36,
     40,  45,  48,  50,  54,  60,  64,  72,  75,  80,
     81,  90,  96, 100, 108, 120, 125, 128, 135, 144,
    150, 160, 162, 180, 192, 200, 216, 225, 240, 243,
    250, 256*/
  ))
    extends PrefetchParameters {
  override val hasPrefetchBit:  Boolean = true
  override val inflightEntries: Int = 16
}

trait HasBOPParams extends HasCoupledL2Parameters {
  val bopParams = prefetchOpt.get.asInstanceOf[BOPParameters]
  // Best offset
  val defaultMinAddrBits = offsetBits + log2Up(bopParams.rrTableEntries) + bopParams.rrTagBits
  val defaultConfig = fullAddressBits >= defaultMinAddrBits

  val rrTableEntries = if (defaultConfig) bopParams.rrTableEntries else 2
  val rrIdxBits = log2Up(rrTableEntries)
  val rrTagBits = if (defaultConfig) bopParams.rrTagBits else (fullAddressBits - offsetBits - rrIdxBits)
  val scoreBits = bopParams.scoreBits
  val roundMax = bopParams.roundMax
  val badScore = bopParams.badScore
  val offsetList = bopParams.offsetList
  val inflightEntries = bopParams.inflightEntries

  val scores = offsetList.length
  val offsetWidth = log2Up(-offsetList(0)) + 1 // -32 <= offset <= 31
  val roundBits = log2Up(roundMax)
  val scoreMax = (1 << scoreBits) - 1
  val scoreTableIdxBits = log2Up(scores)

  val delayCycle = bopParams.delayCycle
  val delayEntries = bopParams.delayEntries
  // val prefetchIdWidth = log2Up(inflightEntries)

  def signedExtend(x: UInt, width: Int): UInt = {
    if (x.getWidth >= width) {
      x
    } else {
      Cat(Fill(width - x.getWidth, x.head(1)), x)
    }
  }
}

abstract class BOPBundle(implicit val p: Parameters) extends Bundle with HasBOPParams
abstract class BOPModule(implicit val p: Parameters) extends Module with HasBOPParams

class ScoreTableEntry(implicit p: Parameters) extends BOPBundle {
  // val offset = UInt(offsetWidth.W)
  val score = UInt(scoreBits.W)

  def apply(score: UInt) = {
    val entry = Wire(this)
    // entry.offset := offset
    entry.score := score
    entry
  }
}

class TestOffsetReq(implicit p: Parameters) extends BOPBundle {
  // find whether (X-d) is in recent request table
  val addr = UInt(fullAddressBits.W)
  val testOffset = UInt(offsetWidth.W)
  val ptr = UInt(scoreTableIdxBits.W)
}

class TestOffsetResp(implicit p: Parameters) extends BOPBundle {
  // val testOffset = UInt(offsetWidth.W)
  val ptr = UInt(scoreTableIdxBits.W)
  val hit = Bool()
}

class TestOffsetBundle(implicit p: Parameters) extends BOPBundle {
  val req = DecoupledIO(new TestOffsetReq)
  val resp = Flipped(DecoupledIO(new TestOffsetResp))
}

class RecentRequestTable(implicit p: Parameters) extends BOPModule {
  val io = IO(new Bundle {
    val w = Flipped(DecoupledIO(UInt(fullAddressBits.W)))
    val r = Flipped(new TestOffsetBundle)
  })

  // RR table is direct mapped, accessed through a hash function, each entry holding a partial tag.
  //        +----------+---------------+---------------+----------------------+
  // paddr: |  ......  |  8-bit hash2  |  8-bit hash1  |  6-bit cache offset  |
  //        +----------+---------------+---------------+----------------------+
  //        +-------+------------------+---------------+----------------------+
  //    or: |  ...  |    12-bit tag    |  8-bit hash1  |  6-bit cache offset  |
  //        +-------+------------------+---------------+----------------------+
  def lineAddr(addr: UInt) = addr(fullAddressBits - 1, offsetBits)
  def hash1(addr:    UInt) = lineAddr(addr)(rrIdxBits - 1, 0)
  def hash2(addr:    UInt) = lineAddr(addr)(2 * rrIdxBits - 1, rrIdxBits)
  def idx(addr:      UInt) = hash1(addr) ^ hash2(addr)
  def tag(addr:      UInt) = lineAddr(addr)(rrTagBits + rrIdxBits - 1, rrIdxBits)
  def rrTableEntry() = new Bundle {
    val valid = Bool()
    val tag = UInt(rrTagBits.W)
  }

  class RRTable(implicit p: Parameters) extends BOPModule {
    val io = IO(new Bundle {
      val r = Flipped(new SRAMReadBus(rrTableEntry(), rrTableEntries, 1))
      val w = Flipped(new SRAMWriteBus(rrTableEntry(), rrTableEntries, 1))
    })
    // private val tags = Mem(rrTableEntries, UInt(rrTagBits.W))
    private val tags = RegInit(VecInit(Seq.fill(rrTableEntries)(0.U(rrTagBits.W))))
    private val valids = RegInit(VecInit(Seq.fill(rrTagBits)(false.B)))
    io.w.req.ready := true.B
    when(io.w.req.valid){
      tags(io.w.req.bits.setIdx) := io.w.req.bits.data.head.tag
      valids(io.w.req.bits.setIdx) := io.w.req.bits.data.head.valid
    }
    io.r.req.ready := !io.w.req.valid

    io.r.resp.data.head.valid := RegEnable(valids(io.r.req.bits.setIdx), io.r.req.fire)
    io.r.resp.data.head.tag := RegEnable(tags(io.r.req.bits.setIdx), io.r.req.fire)
  }

  val rrTable = Module(new RRTable)

  val wAddr = io.w.bits
  rrTable.io.w.req.valid := io.w.valid && !io.r.req.valid
  rrTable.io.w.req.bits.setIdx := idx(wAddr)
  rrTable.io.w.req.bits.data(0).valid := true.B
  rrTable.io.w.req.bits.data(0).tag := tag(wAddr)

  val rAddr = io.r.req.bits.addr - signedExtend((io.r.req.bits.testOffset << offsetBits), fullAddressBits)
  val rData = Wire(rrTableEntry())
  rrTable.io.r.req.valid := io.r.req.fire
  rrTable.io.r.req.bits.setIdx := idx(rAddr)
  rData := rrTable.io.r.resp.data(0)

  assert(!RegNext(io.w.fire && io.r.req.fire), "single port SRAM should not read and write at the same time")

  io.w.ready := rrTable.io.w.req.ready && !io.r.req.valid
  io.r.req.ready := true.B
  io.r.resp.valid := RegNext(rrTable.io.r.req.fire, false.B)
  io.r.resp.bits.ptr := RegNext(io.r.req.bits.ptr)
  io.r.resp.bits.hit := rData.valid && rData.tag === RegNext(tag(rAddr))

}

class DelayQueue(implicit p: Parameters) extends BOPModule {
  val io = IO(new Bundle {
    val enq = Flipped(DecoupledIO(UInt((fullAddressBits - offsetBits).W)))
    val deq = DecoupledIO(UInt((fullAddressBits - offsetBits).W))
  })

  val validEntry = RegInit(VecInit(Seq.fill(delayEntries)(false.B)))
  val addrQueue = RegInit(VecInit(Seq.fill(delayEntries)(0.U((fullAddressBits - offsetBits).W))))
  val counters = RegInit(VecInit(Seq.fill(delayEntries)(0.U((log2Up(delayCycle) + 1).W))))

  val head = RegInit(0.U((log2Up(delayEntries) + 1).W))
  val tail = RegInit(0.U((log2Up(delayEntries) + 1).W))
  val entryCount = RegInit(0.U((log2Up(delayEntries) + 1).W))

  val s_idle :: s_push :: s_pop :: Nil = Enum(3)

  val isFull = entryCount === delayEntries.U
  val canPop = counters(head) >= delayCycle.U

  val state = RegInit(s_idle)

  val deqValid = RegInit(false.B)
  val deqAddr = RegInit(0.U((fullAddressBits - offsetBits).W))

  when(state === s_idle) {
    deqValid := false.B
    when(io.enq.fire && !isFull) {
      state := s_push
    }.elsewhen(canPop) {
      state := s_pop
    }
  }

  val s1_enqBits = RegNext(io.enq.bits)

  when(state === s_push) {
    deqValid := false.B
    addrQueue(tail) := s1_enqBits
    validEntry(tail) := true.B
    counters(tail) := 1.U
    tail := Mux(tail === (delayEntries - 1).U, 0.U, tail + 1.U)
    state := s_idle
    entryCount := entryCount + 1.U
  }

  when(state === s_pop) {
    deqValid := true.B
    deqAddr := addrQueue(head)

    validEntry(head) := false.B
    counters(head) := 0.U
    head := Mux(head === (delayEntries - 1).U, 0.U, head + 1.U)
    state := s_idle
    entryCount := entryCount - 1.U
  }

  // Update counters for all entries except the one being popped
  for (i <- 0 until delayEntries) {
    when(validEntry(i) && (state =/= s_pop || (state === s_pop && i.U =/= head))) {
      counters(i) := counters(i) + 1.U
    }
  }

  io.deq.valid := deqValid
  io.deq.bits := deqAddr
  io.enq.ready := !isFull && (state === s_idle)
}

class OffsetScoreTable(implicit p: Parameters) extends BOPModule with HasPerfLogging{
  val io = IO(new Bundle {
    val req = Flipped(DecoupledIO(UInt(fullAddressBits.W)))
    val prefetchOffset = Output(UInt(offsetWidth.W))
    val testLeft = new TestOffsetBundle
    val testRight = new TestOffsetBundle
  })

  val prefetchOffset = RegInit(2.U(offsetWidth.W))
  // score table
  // val st = RegInit(VecInit(offsetList.map(off => (new ScoreTableEntry).apply(off.U, 0.U))))
  val st = RegInit(VecInit(Seq.fill(scores)((new ScoreTableEntry).apply(0.U))))
  val offList = WireInit(VecInit(offsetList.map(off => off.S(offsetWidth.W).asUInt)))
  val ptr = RegInit(0.U(scoreTableIdxBits.W))
  val round = RegInit(0.U(roundBits.W))

  val bestOffset = RegInit(2.U(offsetWidth.W)) // the entry with the highest score while traversing
  val bestScore = RegInit(badScore.U(scoreBits.W))
  val testOffset = offList(ptr)
  // def winner(e1: ScoreTableEntry, e2: ScoreTableEntry): ScoreTableEntry = {
  //   val w = Wire(new ScoreTableEntry)
  //   w := Mux(e1.score > e2.score, e1, e2)
  //   w
  // }

  val s_idle :: s_learn :: Nil = Enum(2)
  val state = RegInit(s_idle)

  // 1. At the start of a learning phase
  // All the scores are reset to 0.
  // At the end of every learning phase, the prefetch offset is updated as the one with the highest score.
  when(state === s_idle) {
    st.foreach(_.score := 0.U)
    ptr := 0.U
    round := 0.U
    bestScore := badScore.U
    prefetchOffset := bestOffset
    state := s_learn
  }

  // 2. During a learning phase
  // On every eligible L2 read access (miss or prefetched hit), we test an offset d_i from the list.
  // If X-d_i hits in the RR table, the score of offset d_i is incremented. During a round, each offset
  // in the list is test once. When all the offsets in the list have been tested, the current round is
  // finished, and a new round begins from offset d_1 again.
  // The current learning phase finishes at the end of a round when:
  // (1) one of the score equals SCOREMAX, or
  // (2) the number of rounds equals ROUNDMAX.
  when(state === s_learn) {
    when(io.testLeft.req.fire && io.testRight.req.fire ) {
      val roundFinish = ptr === (scores - 1).U
      ptr := Mux(roundFinish, 0.U, ptr + 1.U)
      round := Mux(roundFinish, round + 1.U, round)
    }

    // (2) the number of rounds equals ROUNDMAX.
    when(round >= roundMax.U) {
      state := s_idle
    }

    when(io.testRight.resp.fire && io.testRight.resp.bits.hit) {
      val oldScore = st(io.testRight.resp.bits.ptr).score
      val newScore = oldScore + 1.U
      val offset = offList(io.testRight.resp.bits.ptr)
      st(io.testRight.resp.bits.ptr).score := newScore
      // bestOffset := winner((new ScoreTableEntry).apply(offset, newScore), bestOffset)
      val renewOffset = newScore > bestScore
      bestOffset := Mux(renewOffset, offset, bestOffset)
      bestScore := Mux(renewOffset, newScore, bestScore)
      // (1) one of the score equals SCOREMAX
      when(newScore >= scoreMax.U) {
        state := s_idle
      }
    }.elsewhen(io.testLeft.resp.fire && io.testLeft.resp.bits.hit) {
      val oldScore = st(io.testLeft.resp.bits.ptr).score
      val newScore = oldScore + 1.U
      val offset = offList(io.testLeft.resp.bits.ptr)
      st(io.testLeft.resp.bits.ptr).score := newScore
      // bestOffset := winner((new ScoreTableEntry2).apply(offset, newScore), bestOffset)
      val renewOffset = newScore > bestScore
      bestOffset := Mux(renewOffset, offset, bestOffset)
      bestScore := Mux(renewOffset, newScore, bestScore)
      when(newScore >= scoreMax.U) {
        state := s_idle
      }
    }
  }

  io.req.ready := state === s_learn
  io.prefetchOffset := prefetchOffset

  io.testLeft.req.valid := state === s_learn && io.req.valid
  io.testLeft.req.bits.addr := io.req.bits
  io.testLeft.req.bits.testOffset := testOffset
  io.testLeft.req.bits.ptr := ptr
  io.testLeft.resp.ready := true.B

  io.testRight.req.valid := state === s_learn && io.req.valid
  io.testRight.req.bits.addr := io.req.bits
  io.testRight.req.bits.testOffset := testOffset
  io.testRight.req.bits.ptr := ptr
  io.testRight.resp.ready := true.B

  for (off <- offsetList) {
    if (off < 0) {
      XSPerfAccumulate("best_offset_neg_" + (-off).toString + "_learning_phases",
        Mux(state === s_idle, (bestOffset === off.S(offsetWidth.W).asUInt).asUInt, 0.U))
    } else {
      XSPerfAccumulate("best_offset_pos_" + off.toString + "_learning_phases",
        Mux(state === s_idle, (bestOffset === off.U).asUInt, 0.U))
    }
  }

}

class BestOffsetPrefetch(implicit p: Parameters) extends BOPModule with HasPerfLogging{
  val io = IO(new Bundle() {
    val train = Flipped(DecoupledIO(new PrefetchTrain))
    val req = DecoupledIO(new PrefetchReq)
    val resp = Flipped(DecoupledIO(new PrefetchResp))
  })

  val rrTableRight = Module(new RecentRequestTable)
  val rrTableLeft = Module(new RecentRequestTable)
  val scoreTable = Module(new OffsetScoreTable)
  val delayQueue = Module(new DelayQueue)
  val respQueue = Module(new Queue(new PrefetchResp, 16, flow=true))
  val prefetchOffset = scoreTable.io.prefetchOffset
  val oldAddr = io.train.bits.addr
  val newAddr = oldAddr + signedExtend((prefetchOffset << offsetBits), fullAddressBits)

  respQueue.io.enq <> io.resp
  delayQueue.io.enq.valid := io.train.valid
  delayQueue.io.enq.bits := Cat(io.train.bits.tag, io.train.bits.set)
  delayQueue.io.deq.ready := true.B

  rrTableLeft.io.r <> scoreTable.io.testLeft
  rrTableLeft.io.w.valid := delayQueue.io.deq.valid
  rrTableLeft.io.w.bits := Cat(delayQueue.io.deq.bits, 0.U(offsetBits.W))

  rrTableRight.io.r <> scoreTable.io.testRight
  rrTableRight.io.w.valid := false.B
  rrTableRight.io.w.bits := Cat(Cat(respQueue.io.deq.bits.tag, respQueue.io.deq.bits.set) - signedExtend(prefetchOffset, setBits + fullTagBits), 0.U(offsetBits.W))
  scoreTable.io.req.valid := io.train.valid
  scoreTable.io.req.bits := oldAddr

  val req = Reg(new PrefetchReq)
  val req_valid = RegInit(false.B)
  val crossPage = getPPN(newAddr) =/= getPPN(oldAddr) // unequal tags
  when(io.req.fire) {
    req_valid := false.B
  }
  when(scoreTable.io.req.fire) {
    req.tag := parseFullAddress(newAddr)._1
    req.set := parseFullAddress(newAddr)._2
    req.needT  := DontCare
    req.source := DontCare
    req_valid := !crossPage // stop prefetch when prefetch req crosses pages
  }

  io.req.valid := req_valid
  io.req.bits := req
  io.req.bits.isBOP := true.B
  io.train.ready := scoreTable.io.req.ready && (!req_valid || io.req.ready)
  io.resp.ready := true.B;dontTouch(io.resp.ready)
  respQueue.io.deq.ready := rrTableLeft.io.w.ready

  for (off <- offsetList) {
    if (off < 0) {
      XSPerfAccumulate("best_offset_neg_" + (-off).toString, prefetchOffset === off.S(offsetWidth.W).asUInt)
    } else {
      XSPerfAccumulate("best_offset_pos_" + off.toString, prefetchOffset === off.U)
    }
  }
  XSPerfAccumulate("bop_req", io.req.fire)
  XSPerfAccumulate("bop_train", io.train.fire)
  XSPerfAccumulate("bop_train_stall_for_st_not_ready", io.train.valid && !scoreTable.io.req.ready)
  XSPerfAccumulate("bop_cross_page", scoreTable.io.req.fire && crossPage)
}
