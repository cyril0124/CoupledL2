// error when 000 signature occurs in pTable
package coupledL2.prefetch

import org.chipsalliance.cde.config.Parameters
import chisel3._
import chisel3.util._
import coupledL2.HasCoupledL2Parameters
import xs.utils.CircularShift
import xs.utils.perf.HasPerfLogging
import xs.utils.sram.SRAMTemplate

case class SPPParameters(
  sTableEntries: Int = 256,
  sTagBits: Int = 12,
  pTableEntries: Int = 512,
  pTableDeltaEntries: Int = 4,
  pTableQueueEntries: Int = 4,
  lookCountBits: Int = 6,
  signatureBits: Int = 12,
  unpackQueueEntries: Int = 4,
  fTableEntries: Int = 32
)
    extends PrefetchParameters {
  override val hasPrefetchBit:  Boolean = true
  override val inflightEntries: Int = 32
}

trait HasSPPParams extends HasCoupledL2Parameters {
  val sppParams = prefetchOpt.get.asInstanceOf[SPPParameters]
  val sTagBits = sppParams.sTagBits
  val sTableEntries = sppParams.sTableEntries
  val pTableEntries = sppParams.pTableEntries
  val inflightEntries = sppParams.inflightEntries
  val pTableDeltaEntries = sppParams.pTableDeltaEntries
  val signatureBits = sppParams.signatureBits
  val pTableQueueEntries = sppParams.pTableQueueEntries
  val lookCountBits = sppParams.lookCountBits
  val unpackQueueEntries = sppParams.unpackQueueEntries
  val fTableEntries = sppParams.fTableEntries

  val pageAddrBits = fullAddressBits - pageOffsetBits
  val blkOffsetBits = pageOffsetBits - offsetBits
  val pTagBits = signatureBits - log2Up(pTableEntries)
  val fTagBits = fullAddressBits - offsetBits - log2Up(fTableEntries)

  def strideMap(a: SInt) : UInt = {
    val out = WireInit(0.U(3.W))
    when(a <= -5.S) {
      out := "b100".U
    } .elsewhen(a >= 5.S) {
      out := "b011".U
    } .elsewhen(a <= -3.S && a >= -4.S) {
      out := "b101".U
    } .elsewhen(a <= 4.S && a >= 3.S) {
      out := "b000".U
    } .otherwise {
      out := a.asUInt(2, 0)
    }
    out
  }
}

abstract class SPPBundle(implicit val p: Parameters) extends Bundle with HasSPPParams
abstract class SPPModule(implicit val p: Parameters) extends Module with HasSPPParams with HasPerfLogging

class SignatureTableReq(implicit p: Parameters) extends SPPBundle {
  val pageAddr = UInt(pageAddrBits.W)
  val blkOffset = UInt(blkOffsetBits.W)
}
class BreakPointReq(implicit p: Parameters) extends SPPBundle{
  val pageAddr = UInt(pageAddrBits.W)
  val parent_sig = Vec(1,UInt(signatureBits.W))
  val offset = UInt(blkOffsetBits.W)
}

class SignatureTableResp(implicit p: Parameters) extends SPPBundle {
  val signature = UInt(signatureBits.W)
  val delta = SInt((blkOffsetBits + 1).W)
  val block = UInt((pageAddrBits + blkOffsetBits).W)
}

class PatternTableResp(implicit p: Parameters) extends SPPBundle {
  val deltas = Vec(pTableDeltaEntries, SInt((blkOffsetBits + 1).W))
  val block = UInt((pageAddrBits + blkOffsetBits).W)
  val degree = UInt(lookCountBits.W)
}

class UnpackResp(implicit p: Parameters) extends SPPBundle {
  val prefetchBlock = UInt((pageAddrBits + blkOffsetBits).W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
  val degree = UInt(lookCountBits.W)
}

class DeltaEntry(implicit p: Parameters) extends SPPBundle {
  val delta = SInt((blkOffsetBits + 1).W)
  val cDelta = UInt(4.W)

  def apply(delta: SInt, cDelta: UInt) = {
    val entry = WireInit(0.U.asTypeOf(this))
    entry.delta := delta
    entry.cDelta := cDelta
    entry
  }
}

class SignatureTable(parentName:String="Unkown")(implicit p: Parameters) extends SPPModule {
  val io = IO(new Bundle {
    val req = Flipped(DecoupledIO(new SignatureTableReq))
    val resp = DecoupledIO(new SignatureTableResp) //output old signature and delta to write PT
    val bp_update = Flipped(ValidIO(new BreakPointReq))
  })
  assert(pageAddrBits>=(2 * log2Up(sTableEntries)),s"pageAddrBits as least 20 bits to use hash")
  def hash1(addr:    UInt) = addr(log2Up(sTableEntries) - 1, 0)
  def hash2(addr:    UInt) = addr(2 * log2Up(sTableEntries) - 1, log2Up(sTableEntries))
  def idx(addr:      UInt) = hash1(addr) ^ hash2(addr)
  def tag(addr:      UInt) = addr(sTagBits + log2Up(sTableEntries) - 1, log2Up(sTableEntries))
  def sTableEntry() = new Bundle {
    val valid = Bool()
    val tag = UInt(sTagBits.W)
    val signature = UInt(signatureBits.W)
    val lastBlock = UInt(blkOffsetBits.W)
  }
  println(s"pageAddrBits: ${pageAddrBits}")
  println(s"log2Up(sTableEntries): ${log2Up(sTableEntries)}")
  println(s"fullAddressBits: ${fullAddressBits}")
  println(s"pageOffsetBits: ${pageOffsetBits}")
  println(s"sTagBits: ${sTagBits}")

  val sTable = Module(
    new SRAMTemplate(sTableEntry(), set = sTableEntries, way = 1, bypassWrite = true, shouldReset = true)
  )
  // --------------------------------------------------------------------------------
  // stage 0
  // --------------------------------------------------------------------------------
  // read sTable
  val rAddr_s0  = io.req.bits.pageAddr
  val rValid_s0 = io.req.fire
  sTable.io.r.req.valid       := rValid_s0
  sTable.io.r.req.bits.setIdx := idx(rAddr_s0)
  val accessedPage_s1  = RegEnable(io.req.bits.pageAddr,  0.U(pageAddrBits.W),    rValid_s0)
  val accessedBlock_s1 = RegEnable(io.req.bits.blkOffset, 0.U((blkOffsetBits.W)), rValid_s0)
  val accessedAddr_s1  = RegEnable(Cat(io.req.bits.pageAddr, io.req.bits.blkOffset), 0.U((pageAddrBits+blkOffsetBits).W), rValid_s0)
  // --------------------------------------------------------------------------------
  // stage 1
  // --------------------------------------------------------------------------------
  // get sTable read data, because SRAM read delay, should send to S2 to handle rdata
  // request bp to PT if needed
  val rValid_s1 = RegNext(rValid_s0)
  val rData_s2  = RegEnable(sTable.io.r.resp.data(0), 0.U.asTypeOf(sTableEntry()),  rValid_s1)
  val accessedPage_s2  = RegEnable(accessedPage_s1,  0.U(pageAddrBits.W),                 rValid_s1)
  val accessedBlock_s2 = RegEnable(accessedBlock_s1, 0.U((blkOffsetBits.W)),              rValid_s1)
  val accessedAddr_s2  = RegEnable(accessedAddr_s1,  0.U((pageAddrBits+blkOffsetBits).W), rValid_s1)

  // --------------------------------------------------------------------------------
  // stage 2
  // --------------------------------------------------------------------------------
  // update sTable & req pTable
  val bp_hit = WireInit(false.B)
  val bp_prePredicted_blkOff = WireInit(0.U(blkOffsetBits.W))
  val bp_matched_sig = WireInit(0.U(signatureBits.W))

  //bp, reg realize
  def breakPointEntry() = new Bundle() {
    val valid = Bool()
    val tag = UInt(pageAddrBits.W)
    val parent_sig = Vec(1, UInt(signatureBits.W))
    val prePredicted_blkOffset = UInt(blkOffsetBits.W)
  }

  // write
  val bpTable = RegInit(VecInit(Seq.fill(256)(0.U.asTypeOf(breakPointEntry()))))
  val bp_page = io.bp_update.bits.pageAddr
  when(io.bp_update.valid) {
    bpTable(idx(bp_page)).valid := io.bp_update.valid
    bpTable(idx(bp_page)).tag := bp_page
    bpTable(idx(bp_page)).parent_sig.zip(io.bp_update.bits.parent_sig).foreach(x => x._1 := x._2)
    bpTable(idx(bp_page)).prePredicted_blkOffset := io.bp_update.bits.offset
  }


  val rValid_s2 = RegNext(rValid_s1)
  val hit_s2 = rData_s2.tag === tag(accessedPage_s2) && rData_s2.valid
  val oldSignature_s2 = Mux(hit_s2, rData_s2.signature, 0.U)
  val newDelta_s2     = Mux(hit_s2, accessedBlock_s2.asSInt - rData_s2.lastBlock.asSInt, accessedBlock_s2.asSInt)
  val stableWriteValid_s2 = newDelta_s2 =/= 0.S && rValid_s2

  // bp read
  val s2_bp_access_index = idx(accessedPage_s2)(4, 0)
  val rotate_sig = VecInit(Seq.fill(4)(0.U(signatureBits.W)));
  dontTouch(rotate_sig)
  for (i <- 0 until (4)) {
    rotate_sig(i) := CircularShift(bpTable(s2_bp_access_index).parent_sig.head).left(3 * i)
  }
  val bp_en = WireInit(true.B)
  bp_hit := bp_en && rValid_s2 && bpTable(s2_bp_access_index).tag === accessedPage_s2 && rotate_sig.map(_ === oldSignature_s2).reduce(_ || _)
  bp_prePredicted_blkOff := bpTable(s2_bp_access_index).prePredicted_blkOffset
  val bp_matched_index = WireInit(0.U(2.W))
  bp_matched_sig := rotate_sig(bp_matched_index)


  sTable.io.w.req.valid := stableWriteValid_s2
  sTable.io.w.req.bits.setIdx := idx(accessedPage_s2)
  sTable.io.w.req.bits.data(0).valid := true.B
  sTable.io.w.req.bits.data(0).tag := tag(accessedPage_s2)
  sTable.io.w.req.bits.data(0).signature := (oldSignature_s2 << 3) ^ strideMap(newDelta_s2)
  sTable.io.w.req.bits.data(0).lastBlock := accessedBlock_s2

  io.resp.valid := stableWriteValid_s2
  io.resp.bits.delta  := newDelta_s2

  when(bp_hit){
    io.resp.bits.signature := bp_matched_sig
    io.resp.bits.block := (accessedAddr_s2 >> blkOffsetBits << blkOffsetBits) + bp_prePredicted_blkOff
  }.otherwise {
    io.resp.bits.signature := oldSignature_s2
    io.resp.bits.block := accessedAddr_s2
  }

  io.req.ready := sTable.io.r.req.ready

  XSPerfAccumulate("spp_st_bp_req", bp_hit)
  XSPerfAccumulate("spp_st_bp_update",io.bp_update.valid)
}

class PatternTable(parentName:String="Unkown")(implicit p: Parameters) extends SPPModule {
  val io = IO(new Bundle {
    val req = Flipped(DecoupledIO(new SignatureTableResp))
    val resp = DecoupledIO(new PatternTableResp)
    val db_degree = Input(UInt(2.W))
    val queue_used_degree = Input(UInt(2.W))
    val pt2st_bp = ValidIO(new BreakPointReq)
  })

  def idx(addr:      UInt) = addr(log2Up(pTableEntries) - 1, 0)
  def tag(addr:      UInt) = addr(signatureBits - 1, log2Up(pTableEntries))
  def pTableEntry() = new Bundle {
    val valid = Bool()
    val tag = UInt(pTagBits.W)
    val deltaEntries = Vec(pTableDeltaEntries, new DeltaEntry())
    val count = UInt(4.W)
  }


  val db_degree = io.db_degree

  val pTable = Module(
    new SRAMTemplate(pTableEntry(), set = pTableEntries, way = 1, bypassWrite = true, shouldReset = true)
  )

  val q = Module(new ReplaceableQueueV2(chiselTypeOf(io.req.bits), pTableQueueEntries))
  q.io.enq <> io.req
  val req = q.io.deq.bits

  val s_idle :: s_lookahead0 :: s_lookahead :: Nil = Enum(3)
  val state = RegInit(s_idle)
  val readResult = WireInit(0.U.asTypeOf(pTableEntry()))
  val readSignature = WireInit(0.U(signatureBits.W)) //to differentiate the result from io or lookahead, set based on state
  val readSignature_reg = RegInit(0.U(signatureBits.W))
  val readDelta = WireInit(0.S((blkOffsetBits + 1).W))
  val lastSignature = WireInit(0.U(signatureBits.W))
  val lastDelta = WireInit(0.S((blkOffsetBits + 1).W))
  val hit = WireInit(false.B)
  val enread = WireInit(false.B)
  val enread_reg = RegInit(false.B)
  val enprefetch = WireInit(false.B)
  val enprefetchnl = WireInit(false.B)
  val enwrite = RegNext(q.io.deq.fire && pTable.io.r.req.fire,0.U) //we only modify-write on demand requests
  val current = RegInit(0.U.asTypeOf(new SignatureTableResp))
  val lookCount = RegInit(0.U(lookCountBits.W))
  val miniCount = lookCount

  when(enread_reg) {
    enread := enread_reg
    enread_reg := false.B
  }
  readSignature := readSignature_reg

  //read pTable
  pTable.io.r.req.valid := enread
  pTable.io.r.req.bits.setIdx := idx(readSignature)
  readResult := pTable.io.r.resp.data(0)
  lastSignature := RegNext(readSignature)
  lastDelta := RegNext(readDelta)
  hit := readResult.valid && tag(lastSignature) === readResult.tag
  //set output
  val maxEntry = readResult.deltaEntries.reduce((a, b) => Mux(a.cDelta >= b.cDelta, a, b))
  val delta_list = readResult.deltaEntries.map(x => Mux(x.cDelta > miniCount, x.delta, 0.S))
  val delta_list_checked = delta_list.map(x =>
            Mux((current.block.asSInt + x).asUInt(pageAddrBits + blkOffsetBits - 1, blkOffsetBits)
            === current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits), x, 0.S))
  val delta_list_nl = delta_list.map(_ => 1.S((blkOffsetBits + 1).W))

  io.resp.valid := enprefetch || enprefetchnl
  when(io.resp.valid){
    io.resp.bits.block := current.block
    io.resp.bits.deltas := delta_list_checked
    io.resp.bits.degree := lookCount
  }.otherwise{
    io.resp.bits := 0.U.asTypeOf(io.resp.bits.cloneType)
  }
  when(enprefetchnl) {
    io.resp.bits.deltas := delta_list_nl
  }

  //bp update operation
  val enbp = WireInit(true.B)
  val bp_update = WireInit(false.B)
  io.pt2st_bp.valid := enbp && bp_update
  when(io.pt2st_bp.valid){
    io.pt2st_bp.bits.pageAddr := current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits)
    io.pt2st_bp.bits.parent_sig(0) := lastSignature
    io.pt2st_bp.bits.offset := current.block(blkOffsetBits - 1, 0)
  }.otherwise{
    io.pt2st_bp.bits := 0.U.asTypeOf(io.pt2st_bp.bits.cloneType)
  }



  //modify table
  val deltaEntries = WireInit(VecInit(Seq.fill(pTableDeltaEntries)(0.U.asTypeOf(new DeltaEntry()))))
  val count = WireInit(0.U(4.W))
  when(hit) {
    val exist = readResult.deltaEntries.map(_.delta === lastDelta).reduce(_ || _)
    when(exist) {
      val temp = readResult.deltaEntries.map(x =>
        Mux(x.delta === lastDelta, (new DeltaEntry).apply(lastDelta, x.cDelta + 1.U), x))
      //counter overflow
      when(readResult.count + 1.U === ((1.U << count.getWidth) - 1.U)) {
        deltaEntries := temp.map(x => (new DeltaEntry).apply(x.delta, x.cDelta >> 1))
      } .otherwise {
        deltaEntries := temp
      }
      count := deltaEntries.map(_.cDelta).reduce(_ + _)
    } .otherwise {
      //to do replacement
      val smallest: SInt = readResult.deltaEntries.reduce((a, b) => {
        Mux(a.cDelta < b.cDelta, a, b)
      }).delta
      val indexToReplace : UInt = readResult.deltaEntries.indexWhere(a => a.delta === smallest)
      deltaEntries := VecInit.tabulate(readResult.deltaEntries.length) { i =>
        Mux((i.U === indexToReplace), (new DeltaEntry).apply(lastDelta, 1.U),
        readResult.deltaEntries(i))
      }
      count := deltaEntries.map(_.cDelta).reduce(_ + _)
    }
    //to consider saturate here
  } .otherwise {
    deltaEntries := VecInit(Seq.fill(pTableDeltaEntries)((new DeltaEntry).apply(0.S, 0.U)))
    deltaEntries(0).delta := lastDelta
    deltaEntries(0).cDelta := 1.U
    count := 1.U
  }
  //write pTable
  pTable.io.w.req.valid := enwrite
  pTable.io.w.req.bits.setIdx := idx(lastSignature)
  pTable.io.w.req.bits.data(0).valid := true.B
  pTable.io.w.req.bits.data(0).deltaEntries := deltaEntries
  pTable.io.w.req.bits.data(0).count := count
  pTable.io.w.req.bits.data(0).tag := tag(lastSignature)

  //FSM
  switch(state) {
    is(s_idle) {
      when(q.io.deq.fire) {
        readSignature := req.signature
        readDelta := req.delta
        state := s_lookahead0
        current := req
        enread := true.B
      }
    }
    is(s_lookahead0) {
      enread := true.B
      readSignature := (lastSignature << 3) ^ strideMap(lastDelta)
      state := s_lookahead
    }
    is(s_lookahead) {
      when(RegNext(pTable.io.r.req.fire)) {
        when(hit) {
          val issued = delta_list_checked.map(a => Mux(a =/= 0.S, 1.U, 0.U)).reduce(_ +& _)
          // val testOffset = RegEnable((current.block.asSInt + maxEntry.delta).asUInt, issued =/= 0.U)
          when(issued =/= 0.U) {
            enprefetch := true.B
            val testOffset = (current.block.asSInt + maxEntry.delta).asUInt
            //same page?
            val samePage = (testOffset(pageAddrBits + blkOffsetBits - 1, blkOffsetBits) ===
              current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits))
            when(samePage  && (maxEntry.cDelta > miniCount)) {
              lookCount := lookCount + 1.U
              readSignature_reg := (lastSignature << 3) ^ strideMap(maxEntry.delta)
              enread_reg := true.B
              current.block := testOffset
            } .otherwise {
              lookCount := 0.U
              state := s_idle
            }
          }.otherwise {
            when(lookCount>=4.U){
              bp_update := true.B
            }
            lookCount := 0.U
            state := s_idle
          }
        } .otherwise {
          when(lookCount <= 1.U) {
            val testOffset = current.block + 1.U
            when(testOffset(pageAddrBits + blkOffsetBits - 1, blkOffsetBits) === current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits)) {
              enprefetchnl := true.B
            }
          }
          lookCount := 0.U
          state := s_idle
        }
      }
    }
  }

  q.io.deq.ready := state === s_idle

  //perf
  XSPerfAccumulate(s"spp_pt_do_nextline", enprefetchnl)
  for (i <- 0 until pTableEntries) {
    XSPerfAccumulate(s"spp_pt_touched_entry_onlyset_${i.toString}", pTable.io.r.req.bits.setIdx === i.U(log2Up(pTableEntries).W)
    )
  }
}

//Can add eviction notify or cycle counter for each entry
class Unpack(parentName:String="Unkown")(implicit p: Parameters) extends SPPModule {
  val io = IO(new Bundle {
    val req = Flipped(DecoupledIO(new PatternTableResp))
    val resp = ValidIO(new UnpackResp)
  })

  def idx(addr:      UInt) = addr(log2Up(fTableEntries) - 1, 0)
  def tag(addr:      UInt) = addr(fullAddressBits - offsetBits - 1, log2Up(fTableEntries))

  def fTableEntry() = new Bundle {
    val valid = Bool()
    val tag = UInt(fTagBits.W)
  }
  val fTable = RegInit(VecInit(Seq.fill(fTableEntries)(0.U.asTypeOf(fTableEntry()))))

  val inProcess = RegInit(false.B)
  val endeq = WireInit(false.B)

  val q = Module(new ReplaceableQueueV2(chiselTypeOf(io.req.bits), unpackQueueEntries))
  q.io.enq <> io.req //change logic to replace the tail entry

  val req = RegEnable(q.io.deq.bits, q.io.deq.fire)
  val req_deltas = RegInit(VecInit(Seq.fill(pTableDeltaEntries)(0.S((blkOffsetBits + 1).W))))
  val issue_finish = req_deltas.map(_ === 0.S).reduce(_ && _)
  q.io.deq.ready := !inProcess || issue_finish || endeq
  when(q.io.deq.fire) {
    req_deltas := q.io.deq.bits.deltas
  }

  val enresp = WireInit(false.B)
  val extract_delta = req_deltas.reduce((a, b) => Mux(a =/= 0.S, a, b))
  val prefetchBlock = (req.block.asSInt + extract_delta).asUInt

  val hit = WireInit(false.B)
  val readResult = WireInit(0.U.asTypeOf(fTableEntry()))
  readResult := fTable(idx(prefetchBlock))
  hit := readResult.valid && tag(prefetchBlock) === readResult.tag

  when(enresp && !hit) {
    fTable(idx(prefetchBlock)).valid := true.B
    fTable(idx(prefetchBlock)).tag := tag(prefetchBlock)
  }

  io.resp.valid := enresp && !hit
  io.resp.bits.prefetchBlock := prefetchBlock
  io.resp.bits.degree := req.degree
  io.resp.bits.source := 0.U
  io.resp.bits.needT := false.B

  when(inProcess) {
    when(!issue_finish) {
      val cnt: UInt = req_deltas.count(_ =/= 0.S)
      enresp := true.B
      // req_deltas := req_deltas.map(a => Mux(a === extract_delta, 0.S, a))
      when(cnt === 1.U) {
        endeq := true.B
        when(!q.io.deq.fire) {
          req_deltas := req_deltas.map(a => Mux(a === extract_delta, 0.S, a))
        }
      } .otherwise {
        req_deltas := req_deltas.map(a => Mux(a === extract_delta, 0.S, a))
      }
    } .otherwise {
      when(!q.io.deq.fire) {
        inProcess := false.B
      }
    }
  } .otherwise {
    when(q.io.deq.fire) {
      inProcess := true.B
    }
  }
  XSPerfAccumulate("spp_filter_recv_req", io.req.valid)
  XSPerfAccumulate("spp_filter_hit", q.io.deq.fire && hit)
  XSPerfAccumulate("spp_filter_l2_req", io.req.valid)
  for (off <- (-63 until 64 by 1).toList) {
    if (off < 0) {
      XSPerfAccumulate("spp_pt_pfDelta_neg_" + (-off).toString, hit && extract_delta === off.S((blkOffsetBits + 1).W))
    } else {
      XSPerfAccumulate("spp_pt_pfDelta_pos_" + off.toString, hit && extract_delta === off.S((blkOffsetBits + 1).W))
    }
  }
}

class SignaturePathPrefetch(parentName:String="Unkown")(implicit p: Parameters) extends SPPModule {
  val io = IO(new Bundle() {
    val train = Flipped(DecoupledIO(new PrefetchTrain)) //from higher level cache
    val req = DecoupledIO(new PrefetchReq) //issue to next-level cache
    val resp = Flipped(DecoupledIO(new PrefetchResp)) //fill request from the next-level cache, using this to update filter
    val hint2llc = Output(Bool())
    val db_degree = Flipped(ValidIO(UInt(2.W)))
    val queue_used = Input(UInt(6.W))
  })

  val sTable = Module(new SignatureTable)
  val pTable = Module(new PatternTable)
  val unpack = Module(new Unpack)

  val oldAddr = io.train.bits.addr //received request from L1 cache
  val pageAddr = getPPN(oldAddr)
  val blkOffset = oldAddr(pageOffsetBits - 1, offsetBits)

  // might be lack of prefetch requests
  io.train.ready := sTable.io.req.ready

  sTable.io.req.bits.pageAddr := pageAddr
  sTable.io.req.bits.blkOffset := blkOffset
  sTable.io.req.valid := io.train.fire

  pTable.io.req <> sTable.io.resp //to detail
  pTable.io.pt2st_bp <> sTable.io.bp_update
  pTable.io.resp <> unpack.io.req

  val newAddr = Cat(unpack.io.resp.bits.prefetchBlock, 0.U(offsetBits.W))
  val db_degree = RegEnable(io.db_degree.bits, 1.U, io.db_degree.valid)
  val queue_used_degree = Mux(io.queue_used >= 24.U, 1.U, 0.U)
  val pf_degree = unpack.io.resp.bits.degree
  val send2Llc = pf_degree > 1.U && (queue_used_degree >= 1.U || db_degree > 1.U)

  pTable.io.db_degree := db_degree
  pTable.io.queue_used_degree := queue_used_degree

  io.req.bits.tag := parseFullAddress(newAddr)._1
  io.req.bits.set := parseFullAddress(newAddr)._2
  io.req.bits.needT := unpack.io.resp.bits.needT
  io.req.bits.source := unpack.io.resp.bits.source
  io.req.bits.isBOP := false.B

  io.req.valid := unpack.io.resp.valid
  io.req.valid := unpack.io.resp.valid && !send2Llc
  io.hint2llc := unpack.io.resp.valid && send2Llc

  io.resp.ready := true.B
  //perf
  XSPerfAccumulate( "spp_recv_train", io.train.fire)
  XSPerfAccumulate( "spp_recv_st", sTable.io.resp.fire)
  XSPerfAccumulate( "spp_recv_pt", Mux(pTable.io.resp.fire, pTable.io.resp.bits.deltas.map(a => Mux(a =/= 0.S, 1.U, 0.U)).reduce(_ +& _), 0.U))
  XSPerfAccumulate( "spp_hint", io.hint2llc)
}