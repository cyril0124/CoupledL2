package coupledL2.prefetch

import org.chipsalliance.cde.config.Parameters
import chisel3._
import chisel3.util._
import coupledL2.{HasCoupledL2Parameters,L2ParamKey}
import coupledL2.prefetch.{PrefetchParameters,PrefetchTrain,PrefetchReq,PrefetchResp,PrefetchEvict}
import coupledL2.prefetch.{BestOffsetPrefetch,BOPParameters,PrefetchReceiver,PrefetchReceiverParams}
import coupledL2.prefetch.AccessState
import coupledL2.prefetch.PrefetchQueue
import xs.utils.perf.HasPerfLogging
import xs.utils.sram.SRAMTemplate
import xs.utils.Pipeline
import xs.utils.SRAMQueue
import xs.utils.OneHot
import xs.utils.HighestBit
import xs.utils.ParallelPriorityMux
import xs.utils.RegNextN
import xs.utils.CircularShift
import xs.utils.GenMask
import xs.utils.FastArbiter
import xs.utils.SignExt

object PfCtrlConst{
  object Switch{
    val SMS = 0
    val BOP = 1
    val SPP = 2

    val bits = 3
    def get_fields(x:UInt):UInt = {
      val fields = WireInit(x(bits-1,0));dontTouch(fields)
      fields
    }
  }
  object SppConfig{
    val bits = 5
    def get_fields(x:UInt):UInt = {
      val fields = WireInit(x(Switch.bits+bits-1,Switch.bits));dontTouch(fields)
      fields
    }
  }
  object FitlerTableConfig{
    val bits = 3
    def get_fields(x:UInt):UInt = {
      val fields = WireInit(x(Switch.bits+SppConfig.bits+bits-1,Switch.bits+SppConfig.bits));dontTouch(fields)
      fields
    }
  }
}

object PfSource extends Enumeration {
  val bits = 3
  val NONE    = "b000".U(bits.W)
  val SMS     = "b001".U(bits.W)
  val BOP     = "b010".U(bits.W)
  val SPP     = "b100".U(bits.W)
  val BOP_SPP = "b110".U(bits.W)
}
object PfVectorConst extends {
  val SMS = 0
  val BOP = 1
  val SPP = 2

  val bits = 3
  val DEFAULT = 0.U(bits.W)
}

object PfcovState {
  val bits = 1
  def HIGH     = 0.U(bits.W)
  def LOW      = 1.U(bits.W)

}

object PfaccState {
  val bits = 1

  def HIGH     = 0.U(bits.W)
  def LOW      = 1.U(bits.W)
}

case class SPPParameters(
  sTableEntries: Int = 256,
  bpTableEntries: Int = 32,
  pTableEntries: Int = 512,
  pTableDeltaEntries: Int = 4,
  signatureBits: Int = 12,
  fTableEntries: Int = 32,
  enable_bp: Boolean =true,
  enable_nextline: Boolean = true,
)
    extends PrefetchParameters {
  override val hasPrefetchBit:  Boolean = true
  override val inflightEntries: Int = 32
}

trait HasSPPParams extends HasCoupledL2Parameters {
  val sppParams = SPPParameters()

  val sTableEntries = sppParams.sTableEntries
  val bpTableEntries = sppParams.bpTableEntries
  val pTableEntries = sppParams.pTableEntries
  val inflightEntries = sppParams.inflightEntries
  val pTableDeltaEntries = sppParams.pTableDeltaEntries
  val signatureBits = sppParams.signatureBits
  val pTableQueueEntries = 4
  val unpackQueueEntries = 4
  val fTableEntries = sppParams.fTableEntries
  val lookCountBits = 6
  val hin2llcQueueThreshold = 30

  val pageAddrBits = fullAddressBits - pageOffsetBits
  val blkAddrBits = fullAddressBits - offsetBits
  val blkOffsetBits = pageOffsetBits - offsetBits
  val sTagBits = signatureBits - log2Up(sTableEntries)
  val pTagBits = signatureBits - log2Up(pTableEntries)
  val fTagBits = pageAddrBits - log2Up(fTableEntries)
  val deltaBits = blkOffsetBits + 1
  val shareBOBits = 6

  def strideMap(a: SInt) : UInt = {
    val out = WireInit(0.U(3.W))
    // when(a <= -4.S) {
    //   out := "b100".U
    // } .elsewhen(a >= 4.S) {
    //   out := "b000".U
    // } .elsewhen(-4.S<=a && a <= -3.S) {
    //   out := "b101".U
    // } .elsewhen(3.S <= a && a <= 4.S) {
    //   out := "b000".U
    // } .otherwise {
    //   out := a.asUInt(2, 0)
    // }
    
    when(a > 4.S   )      { out := "b000".U}
    .elsewhen(a === 1.S ) { out := "b001".U}
    .elsewhen(a === 2.S ) { out := "b010".U}
    .elsewhen(a === 3.S ) { out := "b011".U}
    .elsewhen(a === 4.S ) { out := "b100".U}
    .elsewhen(a < -2.S  ) { out := "b101".U}
    .elsewhen(a === -2.S) { out := "b110".U}
    .elsewhen(a === -1.S) { out := "b111".U}
    out
  }
  def makeSign(old_sig:UInt,new_delta:SInt):UInt={
    // (old_sig << 3) ^ new_delta.asUInt
    (old_sig << 3) ^ strideMap(new_delta)
  }

  val ENABLE_BP = sppParams.enable_bp
  val ENABLE_NL = sppParams.enable_nextline
}

abstract class SPPBundle(implicit val p: Parameters) extends Bundle with HasSPPParams
abstract class SPPModule(implicit val p: Parameters) extends Module with HasSPPParams with HasPerfLogging


class ReplaceableQueueV2[T <: Data](val gen: T, val entries: Int) extends Module(){
  object EnqIOV2 {
    def apply[T <: Data](gen: T): DecoupledIO[T] = Decoupled(gen)
  }
  object DeqIOV2 {
    def apply[T <: Data](gen: T): DecoupledIO[T] = Flipped(Decoupled(gen))
  }

  val io = IO(new Bundle{
    val enq = Flipped(EnqIOV2(gen))
    val deq = Flipped(DeqIOV2(gen))
    val empty = Output(Bool())
    val full = Output(Bool())
    val flush = Input(Bool())
  })
  /*  Here we implement a queue that
   *  1. is pipelined  2. flows
   *  3. always has the latest reqs, which means the queue is always ready for enq and deserting the eldest ones
   */
  val queue = RegInit(VecInit(Seq.fill(entries)(0.U.asTypeOf(gen))))
  val valids = RegInit(VecInit(Seq.fill(entries)(false.B)))
  val idxWidth = log2Up(entries)
  val head = RegInit(0.U(idxWidth.W))
  val tail = RegInit(0.U(idxWidth.W))
  val empty = head === tail && !valids.last
  val full = head === tail && valids.last
  io.empty := empty
  io.full := full

  when(!empty && io.deq.ready) {
    valids(head) := false.B
    head := head + 1.U
  }

  when(io.enq.valid) {
    queue(tail) := io.enq.bits
    valids(tail) := !empty || !io.deq.ready // true.B
    tail := tail + (!empty || !io.deq.ready).asUInt
    when(full && !io.deq.ready) {
      head := head + 1.U
    }
  }
  when(io.flush){
    valids.foreach(x => x := false.B)
    tail := 0.U
    head := 0.U
  }

  io.enq.ready := true.B
  io.deq.valid := !empty || (io.enq.valid && !io.flush)
  io.deq.bits := Mux(empty, io.enq.bits, queue(head))

  //XSPerfHistogram(cacheParams, "nrWorkingPfQueueEntries", PopCount(valids), true.B, 0, inflightEntries, 1)
}

class GhrForSpp(implicit p:  Parameters) extends  SPPBundle{
    val l2_deadCov_state = UInt(PfcovState.bits.W)
    val l2_hitAcc_state = UInt(PfaccState.bits.W)
    val shareBO = SInt(shareBOBits.W)
    val global_queue_used = (UInt(6.W))   
}
class SignatureTableReq(implicit p: Parameters) extends SPPBundle {
  val blkAddr = UInt(blkAddrBits.W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
  // val isBP = Bool()
  val fromGHR_shareBO = SInt(shareBOBits.W)
  def get_pageAddr = blkAddr >> blkOffsetBits
  def get_blkOff = blkAddr(blkOffsetBits-1,0)
  def get_accessAddr = Cat(blkAddr,0.U(offsetBits.W))
}

class BreakPointReq(implicit p: Parameters) extends SPPBundle{
  val blkAddr = UInt(blkAddrBits.W)
  val parent_sig = Vec(1,UInt(signatureBits.W))
  def get_pageAddr = blkAddr >> blkOffsetBits
}
class SignatureTableResp_s0(implicit p: Parameters) extends SPPBundle {
  val blkAddr = UInt((pageAddrBits+blkOffsetBits).W)
  // from sram
  val oldSig = UInt(signatureBits.W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
  def get_pageAddr = blkAddr >> blkOffsetBits
  def get_blkOff = blkAddr(blkOffsetBits-1,0)
}
class SignatureTableResp_s1(implicit p: Parameters) extends SPPBundle {
  //read from sram
  val st_hit = Bool()
  val newDelta = SInt(deltaBits.W)
  val newSig = UInt(signatureBits.W)
  // bp data package
  val bp_use_valid = Bool()
  val bp_redirect_blk = UInt(blkAddrBits.W)
  val bp_sig = UInt(signatureBits.W)
}

class PatternTableResp(implicit p: Parameters) extends SPPBundle {
  val deltas = Vec(pTableDeltaEntries, SInt(deltaBits.W))
  val block = UInt((blkAddrBits).W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
}

class UnpackResp(implicit p: Parameters) extends SPPBundle {
  val prefetchBlock = UInt((blkAddrBits).W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
}

class DeltaEntry(implicit p: Parameters) extends SPPBundle {
  val delta = SInt(deltaBits.W)
  val cDelta = UInt(4.W)

  def apply(delta: SInt, cDelta: UInt) = {
    val entry = WireInit(0.U.asTypeOf(this.cloneType))
    entry.delta := delta
    entry.cDelta := cDelta
    entry
  }
}

class SignatureTable(parentName: String = "Unknown")(implicit p: Parameters) extends SPPModule {
  val io = IO(new Bundle {
    val req = Flipped(DecoupledIO(new SignatureTableReq))
    val s0_toPtReq = DecoupledIO(new SignatureTableResp_s0) //output old sig and delta to write PT
    val s1_toPtReq = DecoupledIO(new SignatureTableResp_s1) 
    val s0_bp_update = Flipped(ValidIO(new BreakPointReq))
    val ctrl = new Bundle {
      val en_bp_recovery = Input(Bool())
    }
  })
  def hash1(addr:    UInt) = addr(log2Up(sTableEntries) - 1, 0)
  def hash2(addr:    UInt) = addr(2 * log2Up(sTableEntries) - 1, log2Up(sTableEntries))
  def get_idx(addr:      UInt) = hash1(addr) ^ hash2(addr)
  def get_tag(addr:      UInt) = addr(signatureBits - 1, log2Up(sTableEntries))
  def get_pageAddr(blkAddr: UInt) = blkAddr(blkAddrBits - 1, blkOffsetBits)
  def get_bpIdx(pageAddr: UInt) = pageAddr(log2Up(bpTableEntries) - 1, 0) ^ pageAddr(2 * log2Up(bpTableEntries) - 1, log2Up(bpTableEntries))
  def get_bp_tag(pageAddr: UInt) = pageAddr(pageAddrBits - 1, log2Up(bpTableEntries))
  def sTableEntry() = new Bundle {
    val valid = Bool()
    val tag = UInt(sTagBits.W)
    val sig = UInt(signatureBits.W)
    val last_blkOff = UInt(blkOffsetBits.W)
  }
  def breakPointEntry() = new Bundle() {
    val valid = Bool()
    val tag = UInt((blkAddrBits - blkOffsetBits).W)
    val blkOff = UInt(blkOffsetBits.W)
    val parent_sig = Vec(1, UInt(signatureBits.W))
  }
  
  println(s"fullAddressBits: ${fullAddressBits}")
  println(s"pageOffsetBits: ${pageOffsetBits}")
  println(s"sTagBits: ${sTagBits}")
  
  val sTable = RegInit(VecInit(Seq.fill(sTableEntries)(0.U.asTypeOf(sTableEntry()))))
  // val sTable = Module(
  //   new SRAMTemplate(sTableEntry(), set = sTableEntries, way = 1, 
  //     bypassWrite = true, 
  //     shouldReset = true, 
  //     hasMbist = cacheParams.hasMbist, 
  //     hasShareBus = cacheParams.hasShareBus,
  //     hasClkGate = enableClockGate, 
  //     parentName = parentName
  //   ))
  val bpTable = if(ENABLE_BP) Some(RegInit(VecInit(Seq.fill(bpTableEntries)(0.U.asTypeOf(breakPointEntry()))))) else None
  // --------------------------------------------------------------------------------
  // stage 0
  // --------------------------------------------------------------------------------
  //1. read sTable
  //2. write bpTable
  val s0_valid =  WireInit(false.B);dontTouch(s0_valid)
  val s0_req =  WireInit(0.U.asTypeOf(new SignatureTableReq))
  s0_valid := io.req.fire
  s0_req := io.req.bits

  if(bpTable.isDefined){
    val s0_bp_page = WireInit(io.s0_bp_update.bits.get_pageAddr)
    val s0_bp_wIdx = WireInit(get_bpIdx(s0_bp_page));dontTouch(s0_bp_wIdx)
    //caution: not include power gating there
    bpTable.get(s0_bp_wIdx).valid := io.s0_bp_update.valid
    bpTable.get(s0_bp_wIdx).tag := get_bp_tag(get_pageAddr(io.s0_bp_update.bits.blkAddr))
    bpTable.get(s0_bp_wIdx).blkOff := io.s0_bp_update.bits.blkAddr(blkOffsetBits-1, 0)
    for( i <- 0 until(io.s0_bp_update.bits.parent_sig.length)){
        bpTable.get(s0_bp_wIdx).parent_sig(i) := io.s0_bp_update.bits.parent_sig(i)
    }

  }

  val s0_rEntryData = WireInit(sTable(get_idx(s0_req.get_pageAddr)));dontTouch(s0_rEntryData)
  // pressure cacalute
  val s0_hit = WireInit(s0_rEntryData.tag === get_tag(s0_req.get_pageAddr));dontTouch(s0_hit)
  val s0_delta  = WireInit(s0_req.get_blkOff.asSInt - s0_rEntryData.last_blkOff.asSInt);dontTouch(s0_delta)
  // --------------------------------------------------------------------------------
  // stage 1
  // --------------------------------------------------------------------------------
  //1. update sTable & req pTable
    //- we should write  biggest_blkAddr for solving spp timely problems, let spp prefetching farther!!!
  //2. delta BP from filterTable
    // redirect accessed blockAddr when use bp
    // calculate probeDelta for avoiding biased train signal delta, not make origin good sig overrided
    // calculate probe delata
  val s1_valid        = RegNext(s0_valid,false.B);dontTouch(s1_valid)
  val s1_req          = RegNext(s0_req,0.U.asTypeOf(new SignatureTableReq));dontTouch(s1_req)
  val s1_hit          = RegNext(s0_hit,false.B);dontTouch(s1_hit)
  val s1_delta        = RegNext(s0_delta,0.S);dontTouch(s1_delta)
  val s1_rEntryData   = RegNext(s0_rEntryData);dontTouch(s1_rEntryData)
  val s1_oldSig       = WireInit(s1_rEntryData.sig)
  val s1_newBlkAddr   = s1_req.blkAddr
  // pressure cacalute
  val s1_cal_newSig = WireInit(makeSign(s1_oldSig,s1_delta));dontTouch(s1_cal_newSig)

  //bp read
  val s1_bp_rIdx = WireInit(get_bpIdx(s1_req.get_pageAddr))
  val s1_bp_hit = WireInit(false.B)
  val s1_bp_mask = WireInit(VecInit(Seq.fill(4)(false.B)))
  val s1_bp_redirect_blk = WireInit(0.U(blkAddrBits.W))
  val s1_bp_matched_sig = WireInit(0.U(signatureBits.W))
  val s1_rotate_sig = VecInit(Seq.fill(4)(0.U(signatureBits.W)));dontTouch(s1_rotate_sig)
  if(bpTable.isDefined){
    for (i <- 0 until (4)) {
      s1_rotate_sig(i) := CircularShift(bpTable.get(s1_bp_rIdx).parent_sig.head).left(3 * i)
      s1_bp_mask(i) := s1_rotate_sig(i) === s1_rEntryData.sig 
    }
    s1_bp_redirect_blk := s1_req.blkAddr + bpTable.get(s1_bp_rIdx).blkOff
    s1_bp_hit := ENABLE_BP.asBool && s1_valid && s1_bp_mask.reduce(_ || _) && get_bp_tag(get_pageAddr(s1_req.blkAddr)) === bpTable.get(s1_bp_rIdx).tag
    //TODO: there should set offset for matchedIndex?
    val s1_bp_matchedIdx = WireInit(OneHot.OH1ToUInt(HighestBit(s1_bp_mask.asUInt,4)));dontTouch(s1_bp_matchedIdx)
    s1_bp_matched_sig := s1_rotate_sig(s1_bp_matchedIdx)
  }
  // --------------------------------------------------------------------------------
  // stage 2
  // --------------------------------------------------------------------------------
  val s2_valid  = RegNext(s1_valid,false.B)
  val s2_oldSig = RegNext(s1_oldSig,0.U)
  val s2_req    = RegNext(s1_req,0.U.asTypeOf(new SignatureTableReq))
  val s2_entryData = RegNext(s1_rEntryData,0.U.asTypeOf(sTableEntry()))

  when(s1_valid && s1_delta =/= 0.S){
    sTable(get_idx(s1_req.get_pageAddr)).valid := true.B
    sTable(get_idx(s1_req.get_pageAddr)).tag := get_tag(s1_req.get_pageAddr)
    sTable(get_idx(s1_req.get_pageAddr)).sig := makeSign(s1_oldSig,s1_delta)
    sTable(get_idx(s1_req.get_pageAddr)).last_blkOff := s1_req.get_blkOff
  }
  // s0 send response to paternTable
  // caution : just send data pack to table ,not calculate for serious timing problem
  io.s0_toPtReq.valid := s0_valid
  io.s0_toPtReq.bits.blkAddr := s0_req.blkAddr
  io.s0_toPtReq.bits.oldSig := s0_rEntryData.sig
  io.s0_toPtReq.bits.source := s0_req.source
  io.s0_toPtReq.bits.needT := s0_req.needT
  // s2 send response to paternTable
  io.s1_toPtReq.valid := s1_valid
  io.s1_toPtReq.bits.st_hit := s1_hit
  io.s1_toPtReq.bits.newDelta := s1_delta
  io.s1_toPtReq.bits.newSig := s1_cal_newSig
  io.s1_toPtReq.bits.bp_use_valid := io.ctrl.en_bp_recovery && s1_bp_hit
  io.s1_toPtReq.bits.bp_redirect_blk := s1_bp_redirect_blk
  io.s1_toPtReq.bits.bp_sig := s1_bp_matched_sig

  io.req.ready := io.s0_toPtReq.ready

  XSPerfAccumulate("spp_st_req_nums",io.s0_toPtReq.valid)
  if(ENABLE_BP){
    XSPerfAccumulate("spp_st_bp_req", io.s1_toPtReq.bits.bp_use_valid)
    XSPerfAccumulate("spp_st_bp_update",io.s0_bp_update.valid)
  }
}

class PatternTable(parentName:String="Unkown")(implicit p: Parameters) extends SPPModule {
  val io = IO(new Bundle {
    val fromStReq_s0 = Flipped(DecoupledIO(new SignatureTableResp_s0))
    val fromStReq_s1 = Flipped(DecoupledIO(new SignatureTableResp_s1))
    val resp = DecoupledIO(new PatternTableResp)
    val from_ghr = Flipped(ValidIO(new GhrForSpp))
    val pt2st_bp = ValidIO(new BreakPointReq)
    val ctrl = new Bundle {
      val en_Nextline_Agreesive = Input(Bool())
      val en_bp_recovery = Input(Bool())
      val en_shareBO = Input(Bool())
      val en_slowLookUp = Input(Bool())
    }
  })
  dontTouch(io.from_ghr)
  def get_idx(addr:      UInt) = addr(log2Up(pTableEntries) - 1, 0)
  def get_tag(addr:      UInt) = addr(signatureBits - 1, log2Up(pTableEntries))
  class DeltaEntry(implicit p: Parameters) extends SPPBundle {
    val delta = SInt(deltaBits.W)
    val cDelta = UInt(4.W)

    def apply(delta: SInt, cDelta: UInt) = {
        val entry = WireInit(0.U.asTypeOf(this))
        entry.delta := delta
        entry.cDelta := cDelta
        entry
    }
  }
  class pt_SignatureTableResp(implicit p: Parameters) extends SPPBundle {
    val sig = UInt(signatureBits.W)
    val delta = SInt(deltaBits.W)
    val block = UInt((blkAddrBits).W)
    val needT = Bool()
    val source = UInt(sourceIdBits.W)
  }
  def is_samePage(addr:UInt, originBlockAddr:UInt):Bool = addr(blkAddrBits - 1, blkOffsetBits) === originBlockAddr(blkAddrBits - 1, blkOffsetBits)
  class pTableEntry() extends  Bundle {
    val valid = Bool()
    val tag = UInt(pTagBits.W)
    val deltaEntries = Vec(pTableDeltaEntries, new DeltaEntry())
    val count = UInt(4.W)
  }

  val pTable = Module(
    new SRAMTemplate(new pTableEntry(), set = pTableEntries, way = 1, 
      bypassWrite = true, 
      shouldReset = true, 
      hasMbist = cacheParams.hasMbist, 
      hasShareBus = cacheParams.hasShareBus,
      hasClkGate = enableClockGate, 
      parentName = parentName
    ))
  
  val s0_ghr_shareBO = RegNext(io.from_ghr.bits.shareBO,0.S)
  val s1_ghr_shareBO = WireInit(1.S(shareBOBits.W))
  s1_ghr_shareBO := Mux(io.ctrl.en_shareBO,Mux(s0_ghr_shareBO >= 0.S, s0_ghr_shareBO + 1.S, s0_ghr_shareBO - 1.S), 0.S)
  // --------------------------------------------------------------------------------
  // stage 0
  // --------------------------------------------------------------------------------
  //read pTable
  val s0_fire = WireInit(io.fromStReq_s0.fire);dontTouch(s0_fire)
  val s1_ready = WireInit(false.B)
  val s2_ready = WireInit(false.B)

  val s0_pageAddr = WireInit(io.fromStReq_s0.bits.get_pageAddr)
  val s0_block = WireInit(io.fromStReq_s0.bits.blkAddr);dontTouch(s0_block)
  val s0_sig = WireInit(io.fromStReq_s0.bits.oldSig);dontTouch(s0_sig)

  io.fromStReq_s0.ready := s1_ready
  // --------------------------------------------------------------------------------
  // stage 1
  // --------------------------------------------------------------------------------
  //read pTable
  //1. calculate sram rindex and send read  sram Table requrest
  // when state_s2s1 == s_lookahead 
    //2. when lookcount bigger than sig folding length , start bp update operation
    //3. caculate s1_miniCount, miniCount has been designed 3 strategies for determing need to start next lookahead round
      //-1 slowLookTable(s1_lookCount), use slowLook , relatively conservative query
      //-2 s1_lookCount,  medium level
      //-3 s0_lookCOunt >> 2, very aggressive
      //-4 Mux(q.io.empty, slowLookTable(s1_lookCount), s1_lookCount) ,considering receive queue used situation
    //4. calculate s2_child new data entry
  // s1_child_sig should aligned to s1_parent_sig when first lookahead
  val s3_enprefetch = WireInit(false.B)
  val s3_enprefetchnl = WireInit(false.B)
  val s2_readResult = WireInit(0.U.asTypeOf(new pTableEntry));dontTouch(s2_readResult)
  val s2_child = WireInit(0.U.asTypeOf(new pt_SignatureTableResp));dontTouch(s2_child)
  val s2_valid = WireInit(false.B)
  val s2_first_flag = WireInit(false.B)
  val s2_bp_use_valid = WireInit(false.B)
  val s2_bp_blk = WireInit(0.U(blkAddrBits.W))

  val s1_fromStReq = io.fromStReq_s1
  val s_idle :: s_lookahead0 :: s_lookahead :: Nil = Enum(3)
  val state_s2s1 = RegInit(s_idle)

  val s2_s1_hit = WireInit(false.B)

  val s1_first_flag = RegNext(s0_fire,false.B)
  val s1_continue = WireInit(false.B);dontTouch(s1_continue)
  val s1_valid = WireInit(s1_first_flag || (!s2_valid && s1_continue))

  // sig and block hold from s0
  val s1_parent = WireInit(0.U.asTypeOf(new pt_SignatureTableResp));dontTouch(s1_parent)
  val s1_child = WireInit(0.U.asTypeOf(new pt_SignatureTableResp));dontTouch(s1_child)

  val s1_bp_use_valid = WireInit(io.fromStReq_s1.bits.bp_use_valid);dontTouch(s1_bp_use_valid)
  val s1_bp_blk = WireInit(io.fromStReq_s1.bits.bp_redirect_blk);dontTouch(s1_bp_blk)

  s1_parent.block := RegEnable(s0_block,0.U,s0_fire)
  s1_parent.sig := RegEnable(s0_sig,0.U,s0_fire)
  s1_parent.delta := DontCare

  val s1_lookCount = RegInit(0.U(lookCountBits.W));dontTouch(s1_lookCount)
  val s1_miniCount = WireInit(0.U(lookCountBits.W));dontTouch(s1_miniCount)

  //forward hold dequeue data
  val s2_s1_bypass_result = RegNext(s2_readResult,0.U.asTypeOf(new pTableEntry))
  val s2_s1_bypass_sig = Mux(s1_first_flag||s2_first_flag, s1_parent.sig, RegNext(s2_child.sig,0.U))
  val s2_s1_bypass_block = RegNext(Mux(s2_bp_use_valid, s2_bp_blk, s2_child.block),0.U)

  val s1_cal_maxEntry = WireInit(s2_s1_bypass_result.deltaEntries.reduce((a, b) => Mux(a.cDelta >= b.cDelta, a, b)))
  val s1_bypass_valid = WireInit(s2_s1_bypass_result.valid)
  val s1_bypass_tag = WireInit(s2_s1_bypass_result.tag)
  //temporary calculate only for machine control
  val s2_s1_testBlock = WireInit(s2_s1_bypass_block + SignExt(s1_cal_maxEntry.delta.asUInt,blkAddrBits));dontTouch(s2_s1_testBlock)
  s2_s1_hit := s1_bypass_valid && (get_tag(s2_s1_bypass_sig) === s1_bypass_tag)
  s1_continue := state_s2s1 === s_lookahead && s1_cal_maxEntry.cDelta >= s1_miniCount && !s3_enprefetchnl
  //| sig | delta | block |
  when(state_s2s1 === s_idle){
    s1_lookCount := 0.U
  }.elsewhen(s1_valid){
    s1_lookCount := s1_lookCount + 1.U
  }.otherwise{
    s1_lookCount := s1_lookCount
  }
  
  when(state_s2s1 === s_lookahead){
    s1_child.sig := makeSign(s2_s1_bypass_sig,s1_cal_maxEntry.delta)
    s1_child.block := s2_s1_testBlock
    s1_child.delta := s1_cal_maxEntry.delta
  }.otherwise{
    s1_child.sig := s1_fromStReq.bits.newSig
    s1_child.block := Mux(s1_bp_use_valid, s1_bp_blk, s1_parent.block)
    s1_child.delta := s1_fromStReq.bits.newDelta
  }

  def slowLookTable(lc: UInt): UInt = {
    Mux(lc >= 1.U && lc <= 5.U, (lc >> 1.U) + 1.U, lc)
  }
  //TODO: need to be optimized !!! some error here
  // val s1_miniCount = slowLookTable(s1_lookCount) // test1
  // s1_miniCount := s1_lookCount // test2
  s1_miniCount := Mux(io.ctrl.en_slowLookUp, slowLookTable(s1_lookCount), s1_lookCount) // test3
  s1_ready := state_s2s1 === s_idle
  s1_fromStReq.ready := true.B
  val s1_can_go_s2 = WireInit(!s1_first_flag || s1_fromStReq.bits.newDelta =/= 0.S)
  val s1_can_write = WireInit(s1_can_go_s2 && state_s2s1 === s_lookahead0);dontTouch(s1_can_write)

  // --------------------------------------------------------------------------------
  // stage 2
  // --------------------------------------------------------------------------------
  //1. calculate value for next update
  //2. calculate lookcount when sram read finished
  //caution: do not need check cross page in s1
  s2_valid := RegNext(s1_valid && s1_can_go_s2 ,false.B);dontTouch(s2_valid)
  s2_child := RegNext(s1_child ,0.U.asTypeOf(new pt_SignatureTableResp))
  s2_first_flag := RegNext(s1_first_flag,false.B)

  //directly calculate from sram 
  s2_readResult := pTable.io.r.resp.data(0) //Mux(s2_valid, pTable.io.r.resp.data(0), 0.U.asTypeOf(new pTableEntry))

  //pressure calculate, there should not take complex logics
  val s2_is_crossPage = WireInit(is_samePage(s2_child.block,s1_parent.block));dontTouch(s2_is_crossPage)
  //special access pattern mode optimization
  // 1.simpleStride -> +1+1+1, +2+2+2, +3+3+3
  // 2.complexStride -> +X+Y+X , X!=Y!=Z
  val s2_anchored_sig = s2_child.sig.asTypeOf(Vec(4,UInt(3.W)))
  val s2_is_simpleStrideP = WireInit(s2_anchored_sig.reduce((a,b) => Mux(a === b, true.B, false.B)));dontTouch(s2_is_simpleStrideP)
  val s2_is_complexStrideP = WireInit(s2_anchored_sig.reduce((a,b) => Mux(a =/= b, true.B, false.B)));dontTouch(s2_is_complexStrideP)
  val s2_opcode = WireInit(Cat(s2_is_complexStrideP,s2_is_simpleStrideP,1.U(1.W)))
  val s2_testBO = WireInit(0.S(shareBOBits.W));dontTouch(s2_testBO)

  def M_SIMPLE_TIMELY   = "b011".U
  def M_SIMPLE_UNTIMELY = "b010".U
  def M_COMPLEX_TIMELY  = "b101".U
  def M_COMPLEX_UNTIMELY = "b100".U

  //pressure caculate
  s2_testBO :=  MuxLookup(
      s2_opcode,
      0.S(shareBOBits.W),
      Seq(
        M_SIMPLE_TIMELY -> s1_ghr_shareBO,
        M_SIMPLE_UNTIMELY -> s1_ghr_shareBO,
        M_COMPLEX_TIMELY -> s1_ghr_shareBO,
        M_COMPLEX_UNTIMELY -> s1_ghr_shareBO
      )
    )
  // s2_testBO := s1_ghr_shareBO + 1.S
  // Mux(io.from_ghr.bits.l2pf_hitAcc_state =/= 0.U && io.from_ghr.bits.l2pf_hitAcc_state === 0.U,
  //   s1_ghr_shareBO + 10.S,
  //   s2_testBO2
  // )
  def LOW_COV_LOW_ACC   = "b00".U
  def LOW_COV_HIGH_ACC  = "b01".U
  def HIGH_COV_LOW_ACC  = "b10".U
  def HIGH_COV_HIGH_ACC = "b11".U
  
  val s2_AccMap= io.from_ghr.bits.l2_hitAcc_state
  val s2_CovMap= io.from_ghr.bits.l2_deadCov_state
  val s2_C_A = WireInit(Cat(s2_CovMap,s2_AccMap));dontTouch(s2_C_A)
  val s2_NL_ctrlMask = WireInit(0.U(4.W));dontTouch(s2_NL_ctrlMask)
  s2_NL_ctrlMask := Mux(io.ctrl.en_Nextline_Agreesive,
    "b1111".U,
    MuxLookup(
      s2_C_A,
      GenMask.apply(0),
      Seq(
        LOW_COV_LOW_ACC   -> "b0001".U,
        LOW_COV_HIGH_ACC  -> "b1111".U,
        HIGH_COV_LOW_ACC  -> "b0001".U,
        HIGH_COV_HIGH_ACC -> "b0001".U,
    )
  ))
  //FSM
  switch(state_s2s1) {
    is(s_idle) {
      when(s0_fire) {
        state_s2s1 := s_lookahead0
      }
    }
    is(s_lookahead0) {
        state_s2s1 := s_lookahead
    }
    is(s_lookahead) {
        when(s1_valid || s2_valid) {
            state_s2s1 := s_lookahead
        }.otherwise{
            state_s2s1 := s_idle
        }
    }
  }

  // --------------------------------------------------------------------------------
  // stage 3
  // --------------------------------------------------------------------------------
  //calculate update paternTable's data
  //hold needed write sig when fisrt read sram index
  //1. when leave lookahead0,hold needed writing data
  //2. sendout ptable request
  val s3_valid = RegNext(s2_valid,false.B)
  val s3_state = RegNext(state_s2s1,s_idle)
  val s3_first_flag = RegNext(s2_first_flag,false.B)
  val s3_write_valid = RegNextN(s1_can_write,2,Some(false.B))
  val s3_miniCount = RegNextN(s1_miniCount,2,Some(0.U))
  val s3_lookCount = RegNextN(s1_lookCount,2,Some(0.U))
  
  //these should hold
  val s3_current = RegEnable(s2_child,0.U.asTypeOf(new pt_SignatureTableResp),s2_valid)
  val s3_readResult = RegEnable(s2_readResult,0.U.asTypeOf(new pTableEntry),s2_valid)
  val s3_testBO =  RegEnable(s2_testBO,0.S,s2_valid)
  val s3_NL_ctrlMask = RegEnable(s2_NL_ctrlMask.asTypeOf(Vec(4,Bool())),0.U.asTypeOf(Vec(4,Bool())),s2_valid)

  //TODO : need tag match ???
  val s3_hit = WireInit(s3_readResult.valid && get_tag(s3_current.sig) === s3_readResult.tag)
  //pressure calculate
  // assert(s3_current.delta === 0.S,"s3_current.delta sould equal 0")
  val s3_smallest: SInt = s3_readResult.deltaEntries.reduce((a, b) => Mux(a.cDelta < b.cDelta, a, b)).delta
  val s3_replaceIdx: UInt = s3_readResult.deltaEntries.indexWhere(a => a.delta === s3_smallest)
  val s3_exist = s3_readResult.deltaEntries.map(_.delta === s3_current.delta).reduce(_ || _)
  val s3_wTemp = s3_readResult.deltaEntries.map(x => Mux(x.delta === s3_current.delta, (new DeltaEntry).apply(s3_current.delta, x.cDelta + 1.U), x))
  val s3_wdeltaEntries = WireInit(VecInit(Seq.fill(pTableDeltaEntries)(0.U.asTypeOf(new DeltaEntry()))));dontTouch(s3_wdeltaEntries)
  val s3_wEntry = WireInit(0.U.asTypeOf(new pTableEntry()))

  //set output
  val s3_delta_list = s3_readResult.deltaEntries.map(x => 
    Mux(x.cDelta >= s3_miniCount,
      Mux(io.ctrl.en_shareBO,
        ParallelPriorityMux(
          Seq(
            (x.delta === 0.S) -> 0.S,
            (x.delta > 0.S && s3_testBO > 0.S )-> (x.delta + s3_testBO),
            (x.delta < 0.S && s3_testBO < 0.S) -> (x.delta + s3_testBO),
            (x.delta > 0.S && s3_testBO < 0.S) -> (x.delta - s3_testBO),
            (x.delta < 0.S && s3_testBO > 0.S) -> (x.delta - s3_testBO),
        )),x.delta),
      0.S)
  )

  val s3_delta_list_checked = WireInit(VecInit(Seq.fill(pTableDeltaEntries)(0.S(deltaBits.W))))
  val s3_delta_list_nl_masked = WireInit(VecInit(Seq.fill(pTableDeltaEntries)(0.S(deltaBits.W))));dontTouch(s3_delta_list_nl_masked)
  val s3_delta_longest = WireInit(Mux(s3_enprefetch, s3_delta_list_checked.reduce((a,b) => Mux(a > b, a, b)), 
    s3_delta_list_nl_masked.reduce((a,b) => Mux(a > b, a, b))));dontTouch(s3_delta_longest)
  // pressure calculate
  // normal lookahead
  s3_delta_list_checked := s3_delta_list.map(x => Mux(is_samePage(s3_current.block + x.asUInt, s1_parent.block), x, 0.S))
  // nextline
  s3_delta_list_nl_masked := s3_delta_list.zipWithIndex.map(d => Mux(s3_NL_ctrlMask(d._2), Mux(s3_testBO > 0.S, s3_testBO + d._2.S, s3_testBO - d._2.S), 0.S))

  val s3_issued = s3_delta_list_checked.map(a => Mux(a =/= 0.S, 1.U, 0.U)).reduce(_ +& _)
  val s3_issued_nl = s3_delta_list_nl_masked.map(a => Mux(a =/= 0.S, true.B, false.B)).reduce(_ || _)
  //
  s3_enprefetch := s3_valid && s3_hit && s3_issued =/= 0.U
  when(s3_valid && s3_first_flag && !s3_enprefetch && s3_issued_nl) {
    s3_enprefetchnl := ENABLE_NL.B
  }

  // calculate needed writing delta counters
  when(s3_write_valid && s3_hit) {
    when(s3_exist) {
      //counter overflow --- only considering count overflow
      when(s3_readResult.count + 1.U === ((1.U << s3_readResult.count.getWidth).asUInt - 1.U)) {
        s3_wdeltaEntries := s3_wTemp.map(x => (new DeltaEntry).apply(x.delta, x.cDelta >> 1.asUInt))
      } .otherwise {
        s3_wdeltaEntries := s3_wTemp
      }
    } .otherwise {
      //to do replacement
      s3_wdeltaEntries := VecInit.tabulate(s3_readResult.deltaEntries.length) { i =>
        Mux((i.U === s3_replaceIdx), (new DeltaEntry).apply(s3_current.delta, 1.U), s3_readResult.deltaEntries(i))
      }
    }
    //to consider saturate here
  } .otherwise {
    s3_wdeltaEntries(0).delta := s1_parent.delta
    s3_wdeltaEntries(0).cDelta := 1.U
  }
  s3_wEntry.tag := get_tag(s1_parent.sig)
  s3_wEntry.valid := true.B
  s3_wEntry.deltaEntries := s3_wdeltaEntries
  s3_wEntry.count := DontCare
  // --------------------------------------------------------------------------------
  // stage 4
  // --------------------------------------------------------------------------------
  // write ptable
  val s4_valid = RegNext(s3_valid, false.B)
  val s4_write_valid = RegNext(s3_first_flag,false.B)
  val s4_wEntry = RegNext(s3_wEntry,0.U.asTypeOf(new pTableEntry))
  val s4_sig = RegNext(s3_current.sig,0.U)
  val s4_block = RegNext(s3_current.block,0.U)
  val s4_delta_list_checked = RegNext(s3_delta_list_checked,0.U.asTypeOf((s3_delta_list_checked.cloneType)))
  val s4_delta_list_nl_masked = RegNext(s3_delta_list_nl_masked,0.U.asTypeOf((s3_delta_list_nl_masked.cloneType)))
  val s4_delta_longest = RegNext(s3_delta_longest,0.U.asTypeOf(s3_delta_longest))
  val s4_enprefetch = RegNext(s3_enprefetch,false.B)
  val s4_enprefetchnl = RegNext(s3_enprefetchnl,false.B)

  val s4_bp_update = WireInit(s4_valid && (s4_enprefetch || s4_enprefetchnl) && io.ctrl.en_bp_recovery);dontTouch(s4_bp_update)
  //pressure caculate
  val s4_wCount_accum = WireInit(s4_wEntry.deltaEntries.map(_.cDelta).reduce(_ + _))

  // --------------------------------------------------------------------------------
  // pTable operation
  // --------------------------------------------------------------------------------
  pTable.io.r.req.valid := s0_fire || s1_valid
  when(s0_fire){
    pTable.io.r.req.bits.setIdx := get_idx(s0_sig)
  }.otherwise{
    pTable.io.r.req.bits.setIdx := get_idx(s1_child.sig)
  }

  pTable.io.w.req.valid := s4_valid && s4_write_valid
  pTable.io.w.req.bits.setIdx := RegEnable(get_idx(s1_parent.sig),0.U,s3_write_valid)
  pTable.io.w.req.bits.data(0) := s4_wEntry
  pTable.io.w.req.bits.data(0).count := s4_wCount_accum
  
  //update bp
  io.pt2st_bp.valid := ENABLE_BP.asBool && s4_bp_update
  io.pt2st_bp.bits.blkAddr := s4_block + s4_delta_longest.asUInt
  io.pt2st_bp.bits.parent_sig(0) := s4_sig
  dontTouch(io.pt2st_bp)

  // output
  io.resp.valid := s3_enprefetch || s3_enprefetchnl
  io.resp.bits.block := s3_current.block
  when(s3_enprefetchnl) {
    io.resp.bits.deltas := s3_delta_list_nl_masked
  }.otherwise{
    io.resp.bits.deltas := s3_delta_list_checked
  }
  // io.resp.bits.degree := s1_lookCount
  io.resp.bits.source := RegEnable(s1_parent.source, state_s2s1 === s_lookahead0)
  io.resp.bits.needT := RegEnable(s1_parent.needT, state_s2s1 === s_lookahead0)

  //perf
  XSPerfAccumulate("spp_pt_bp_nums",io.pt2st_bp.valid)
  XSPerfAccumulate("spp_pt_hit",s3_state === s_lookahead && s3_hit)
  XSPerfAccumulate("spp_pt_lookaheadX",state_s2s1 === s_lookahead && s1_valid)
  for (i <- 2 until 7){
      XSPerfAccumulate(s"spp_pt_lookahead${i}",state_s2s1 === s_lookahead && s1_lookCount === i.U)
  }
  XSPerfAccumulate("spp_pt_enpf",state_s2s1 === s_lookahead && s3_enprefetch)
  XSPerfAccumulate("spp_pt_nextLine",state_s2s1 === s_lookahead && s3_enprefetchnl)
  XSPerfAccumulate("spp_pt_cross_page",state_s2s1 === s_lookahead && s2_valid && 
    s3_delta_list.map(x => is_samePage(s3_current.block + x.asUInt,s3_current.block)).reduce(_||_))
  for (i <- 0 until pTableEntries) {
    XSPerfAccumulate(s"spp_pt_touched_entry_onlyset_${i.toString}", pTable.io.r.req.bits.setIdx === i.U(log2Up(pTableEntries).W)
    )
  }
}

class Unpack(parentName:String="Unkown")(implicit p: Parameters) extends SPPModule {
  val io = IO(new Bundle {
    val req = Flipped(DecoupledIO(new PatternTableResp))
    val resp = DecoupledIO(new UnpackResp)
  })
  // --------------------------------------------------------------------------------
  // stage 4
  // --------------------------------------------------------------------------------
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
  q.io.flush := false.B

  val req = RegEnable(q.io.deq.bits,0.U.asTypeOf(new PatternTableResp), q.io.deq.fire)
  val req_deltas = RegInit(VecInit(Seq.fill(pTableDeltaEntries)(0.S(deltaBits.W))))
  val issue_finish = req_deltas.map(_ === 0.S).reduce(_ && _)
  q.io.deq.ready := !inProcess || issue_finish || endeq
  when(q.io.deq.fire) {
    req_deltas := q.io.deq.bits.deltas
  }
  
  val enresp = WireInit(false.B)
  val extract_delta = req_deltas.reduce((a, b) => Mux(a =/= 0.S, a, b))
  val prefetchBlock = WireInit(0.U(blkAddrBits.W));dontTouch(prefetchBlock)
  prefetchBlock := req.block + SignExt(extract_delta.asUInt,blkAddrBits)

  val hit = WireInit(false.B)
  val s1_result = WireInit(0.U.asTypeOf(fTableEntry()))
  s1_result := fTable(idx(prefetchBlock))
  hit := s1_result.valid && tag(prefetchBlock) === s1_result.tag

  when(enresp && !hit) {
    fTable(idx(prefetchBlock)).valid := true.B
    fTable(idx(prefetchBlock)).tag := tag(prefetchBlock)
  }

  io.resp.valid := RegNext(enresp && !hit,false.B)
  io.resp.bits.prefetchBlock := RegNext(prefetchBlock,0.U((blkAddrBits).W))
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
}
class SignaturePathPrefetch(implicit p: Parameters) extends SPPModule {
  val io = IO(new Bundle() {
    val train = Flipped(DecoupledIO(new PrefetchTrain)) 
    val req = DecoupledIO(new PrefetchReq)
    val req_hint2llc = DecoupledIO(new PrefetchReq)
    val resp = Flipped(DecoupledIO(new PrefetchResp))
    val from_ghr = Flipped(ValidIO(new GhrForSpp))
    val sppCtrl = Input(UInt(PfCtrlConst.SppConfig.bits.W))
  })

  val sppCtrl = WireInit(io.sppCtrl);dontTouch(sppCtrl)
  //sppConfig[0] -> enable hint2llc
  //sppConfig[1] -> enable Nextline Agreesive
  //sppConfig[2] -> enable bp recovery
  //sppConfig[3] -> enable shareBO
  //sppConfig[4] -> enable slowLookUp  
  val ctrl_hint2llc_en = WireInit(sppCtrl(0));dontTouch(ctrl_hint2llc_en)
  val ctrl_nl_agressive = WireInit(sppCtrl(1));dontTouch(ctrl_nl_agressive)
  val ctrl_bp_recovery = WireInit(sppCtrl(2));dontTouch(ctrl_bp_recovery)
  val ctrl_shareBO = WireInit(sppCtrl(3));dontTouch(ctrl_shareBO)
  val ctrl_slowLookup = WireInit(sppCtrl(4));dontTouch(ctrl_slowLookup)

  val sTable = Module(new SignatureTable("spp_stable"))
  val pTable = Module(new PatternTable("spp_ptable"))
  val unpack = Module(new Unpack("spp_unpack"))

  sTable.io.req.valid := io.train.valid
  sTable.io.req.bits.blkAddr := io.train.bits.blkAddr
  sTable.io.req.bits.needT := io.train.bits.needT
  sTable.io.req.bits.source := io.train.bits.source
  sTable.io.s0_bp_update <> pTable.io.pt2st_bp
  sTable.io.ctrl.en_bp_recovery := ctrl_bp_recovery
  sTable.io.req.bits.fromGHR_shareBO := DontCare
  io.train.ready := sTable.io.req.ready

  pTable.io.fromStReq_s0 <> sTable.io.s0_toPtReq
  pTable.io.fromStReq_s1 <> sTable.io.s1_toPtReq
  pTable.io.resp <> unpack.io.req
  pTable.io.from_ghr <> RegNext(io.from_ghr,0.U.asTypeOf(io.from_ghr.cloneType))
  pTable.io.ctrl.en_Nextline_Agreesive := ctrl_nl_agressive
  pTable.io.ctrl.en_bp_recovery := ctrl_bp_recovery
  pTable.io.ctrl.en_shareBO := ctrl_shareBO
  pTable.io.ctrl.en_slowLookUp := ctrl_slowLookup

  val req = WireInit(0.U.asTypeOf(new PrefetchReq))

  val pf_newAddr = WireInit(Cat(unpack.io.resp.bits.prefetchBlock, 0.U(offsetBits.W)))
  req.tag := parseFullAddress(pf_newAddr)._1
  req.set := parseFullAddress(pf_newAddr)._2
  req.needT := unpack.io.resp.bits.needT
  req.source := unpack.io.resp.bits.source
  req.pfVec := PfSource.SPP

  io.req.valid := unpack.io.resp.valid && io.from_ghr.bits.global_queue_used <= hin2llcQueueThreshold.U
  io.req.bits := req
  unpack.io.resp.ready := io.req.ready

  dontTouch(io.req_hint2llc)
  dontTouch(io.from_ghr)
  io.req_hint2llc.valid := ctrl_hint2llc_en && unpack.io.resp.valid && io.from_ghr.bits.global_queue_used > hin2llcQueueThreshold.U
  io.req_hint2llc.bits := Mux(io.req_hint2llc.valid,req,0.U.asTypeOf(new PrefetchReq))

  io.resp.ready := true.B

  XSPerfAccumulate("recv_train", io.train.fire)
  XSPerfAccumulate("recv_pt", Mux(pTable.io.resp.fire, pTable.io.resp.bits.deltas.map(a => Mux(a =/= 0.S, 1.U, 0.U)).reduce(_ +& _), 0.U))
  XSPerfAccumulate("recv_up", unpack.io.resp.fire)
}

case class HyperPrefetchParams(
  fTableEntries: Int = 32,
  fTableQueueEntries: Int = 128
) extends PrefetchParameters {
  override val hasPrefetchBit:  Boolean = true
  override val inflightEntries: Int = 32
}

trait HasHyperPrefetchDev2Params extends HasCoupledL2Parameters {
  val hyperParams = HyperPrefetchParams()

  val blkAddrBits = fullAddressBits - offsetBits
  val pageAddrBits = fullAddressBits - pageOffsetBits
  val blkOffsetBits = pageOffsetBits - offsetBits
  val blkNums = 1<<blkOffsetBits //64

  val fTableEntries = hyperParams.fTableEntries
  // for backend restrict
  // 25 - 5 = 20
  val fTagBits = pageAddrBits - log2Up(fTableEntries)
  val fTableQueueEntries = hyperParams.fTableQueueEntries
  val bop_pfReqQueueEntries = 8
  val spp_pfReqQueueEntries = 8
  val sms_pfReqQueueEntries = 16
  val hin2llc_pfReqQueueEntries = 4
}

abstract class HyperPrefetchDev2Module(implicit val p: Parameters) extends Module with HasHyperPrefetchDev2Params with HasPerfLogging
abstract class HyperPrefetchDev2Bundle(implicit val p: Parameters) extends Bundle with HasHyperPrefetchDev2Params

class FilterTable(parentName:String = "Unknown")(implicit p: Parameters) extends HyperPrefetchDev2Module {
  val io = IO(new Bundle() {
    val in_pfReq = Flipped(DecoupledIO(new PrefetchReq))
    val in_trainReq = Flipped(ValidIO(new PrefetchReq))
    val in_respReq = Flipped(DecoupledIO(new PrefetchResp))

    val out_pfReq = DecoupledIO(new PrefetchReq)
    val out_respReq = DecoupledIO(new PrefetchResp)
    //
    val evict = Flipped(DecoupledIO(new PrefetchEvict))
    val is_hint2llc = Input(Bool())
    val hint2llc_out = ValidIO(new PrefetchReq)
    val ctrl = Input(UInt(PfCtrlConst.FitlerTableConfig.bits.W))
  })
  val ctrl_filter_sms = WireInit(io.ctrl(PfVectorConst.SMS));dontTouch(ctrl_filter_sms)
  val ctrl_filter_bop = WireInit(io.ctrl(PfVectorConst.BOP));dontTouch(ctrl_filter_bop)
  val ctrl_filter_spp = WireInit(io.ctrl(PfVectorConst.SPP));dontTouch(ctrl_filter_spp)
  ctrl_filter_sms := false.B
  def hash1(addr:    UInt) = addr(log2Up(fTableEntries) - 1, 0)
  def hash2(addr:    UInt) = addr(2 * log2Up(fTableEntries) - 1, log2Up(fTableEntries))
  def ft_get_idx(pageAddr: UInt): UInt = hash1(pageAddr) ^ hash2(pageAddr)
  def ft_get_tag(addr: UInt) = addr(fTagBits-1, log2Up(fTableEntries))
  val saved_blkAddrBits = 31
  def get_saved_blkAddr(x:UInt) = x(saved_blkAddrBits-1, 0)

  def pf_resp2pf_req(x:PrefetchResp):PrefetchReq={
    val tmp = WireInit(0.U.asTypeOf(new PrefetchReq))
    tmp.tag := x.tag
    tmp.set := x.set
    tmp.pfVec := PfSource.BOP
    tmp
  }

  object FitlerVecState {
    val bits = 3

    def toN = 0.U(bits.W)
    def toB = 1.U(bits.W)
    def toS = 2.U(bits.W)
    def toC = 3.U(bits.W)

    def None          = 0.U(bits.W)
    def SMS           = 1.U(bits.W)
    def BOP           = 2.U(bits.W)
    def SPP           = 4.U(bits.W)

    def COMMON        = 7.U(bits.W)

    //TODO: further study, is need bop update filterTable?
    // def getVecState(isHit:Bool, originV:UInt, trigerId:UInt) = (originV | trigerId) & ~(BOP)
    def getVecState(isHit:Bool, originV:UInt, trigerId:UInt) = (originV | trigerId)
    def checkOne(v:UInt) = v === BOP || v === SPP
    def checkTwo(v:UInt) = v === COMMON
    def hasMyself(v:UInt,originV:UInt) = (v & originV) === v
    def hasMerged(v:UInt,originV:UInt) = v =/= originV
    def is_SPPchase(v:UInt,originV:UInt) = hasMyself(v,SPP) && (originV === BOP || originV === (BOP | SMS))
  }
  def has_sms(x:UInt): Bool=x(PfVectorConst.SMS)
  def has_bop(x:UInt): Bool=x(PfVectorConst.BOP)
  def has_spp(x:UInt): Bool=x(PfVectorConst.SPP)
  val dupNums = 5
  val dupOffsetBits = log2Up(fTableEntries/dupNums)
  val dupBits = log2Up(dupNums)
  val req_dups = RegInit(VecInit(Seq.fill(dupNums)(0.U.asTypeOf(Valid(new PrefetchReq)))))
  // val req_issue = WireInit(0.U.asTypeOf(DecoupledIO(new PrefetchReq())));dontTouch(req_issue)
  dontTouch(io)
  // --------------------------------------------------------------------------------
  // consensus Table cTable
  // --------------------------------------------------------------------------------
  // | valid | tag | cVec[[pfVec],[pfVec],...,[pfVec]] |
  // | valid | tag | cVec[[pfVec],[pfVec],...,[pfVec]] |
  // | valid | tag | cVec[[pfVec],[pfVec],...,[pfVec]] |
  // | valid | tag | cVec[[pfVec],[pfVec],...,[pfVec]] |
  // | valid | tag | cVec[[001], [100] , ..., [111]]   |
  //                               ^
  //                               |
  //                            archored_value
    def fTableEntry() = new Bundle {
      val valid = Bool()
      val tag = UInt(fTagBits.W)
      val cVec = Vec(blkNums, UInt(FitlerVecState.bits.W))
    }
    // val consensusTable = Mem(fTableEntries,fTableEntry())
    val consensusTable = RegInit(VecInit(Seq.fill(fTableEntries)(0.U.asTypeOf(fTableEntry()))))
    // val evict_q = Module(new Queue(UInt(fullAddressBits.W), fTableQueueEntries, flow = false, pipe = true))
    val evict_q = Module(new SRAMQueue(UInt(saved_blkAddrBits.W),entries = fTableQueueEntries, flow = false, 
        hasMbist = cacheParams.hasMbist, hasClkGate=enableClockGate, hasShareBus = cacheParams.hasShareBus, parentName=parentName+"filterDelayQ"))
    // pythisc backend freezed memory cacacipty
    // - _ -
    // |   |
    // |   | 
    // val evict_q_reg = Module(new SyncDataModuleTemplate(
    //   UInt(7.W),
    //   fTableQueueEntries,
    //   numRead = 1,
    //   numWrite = 1,
    //   parentModule = parentName+"filterDelayQ_reg"
    // ))

    // --------------------------------------------------------------------------------
    // stage 0
    // --------------------------------------------------------------------------------
    // bop not need filter, bop flow
    // read filterTable
    val s0_valid = WireInit(false.B);dontTouch(s0_valid)
    val s0_req = WireInit(0.U.asTypeOf(new PrefetchReq));dontTouch(s0_req)
    val s0_result = WireInit(0.U.asTypeOf(fTableEntry()));dontTouch(s0_result)
    val s0_isHint2llc = WireInit(io.is_hint2llc)
    val s0_fromTrain = WireInit(io.in_trainReq.fire)
    val s0_train_pfVec = RegInit(VecInit(Seq.fill(blkNums)(0.U(FitlerVecState.bits.W))))
    val s0_train_pageTag = WireInit(0.U(fTagBits.W));dontTouch(s0_train_pageTag)
    val s0_train_tagHit = WireInit(ft_get_tag(io.in_trainReq.bits.get_pageAddr) === s0_train_pageTag);dontTouch(s0_train_tagHit)
    val s0_isRespRedirect = WireInit(io.in_respReq.fire)
    //flow filter
    val s0_can_flow_filter = WireInit(ft_get_tag(io.in_pfReq.bits.get_pageAddr) === s0_train_pageTag);dontTouch(s0_can_flow_filter)
    val s0_update_train_pfVec = WireInit(io.in_pfReq.fire && s0_can_flow_filter)
    val s0_can_send = WireInit(false.B);dontTouch(s0_can_send)
    val s0_skip_filter = WireInit(false.B)

    val replay_Q0 = Module(new ReplaceableQueueV2(new PrefetchReq, 4))
    val quiteUpdateQ = Module(new ReplaceableQueueV2(new PrefetchReq, 4))

    def get_stall(x:DecoupledIO[PrefetchReq]):Bool = x.valid && !x.ready
    val s0_skip_smp = WireInit(io.in_pfReq.bits.hasSMS && !ctrl_filter_sms)
    val s0_skip_bop = WireInit(io.in_pfReq.bits.hasBOP && !ctrl_filter_bop)
    val s0_skip_spp = WireInit(io.in_pfReq.bits.hasSPP && !ctrl_filter_spp)
    s0_can_send := io.in_pfReq.fire && (s0_skip_smp || s0_skip_bop || s0_skip_spp || (s0_can_flow_filter && (s0_train_pfVec(io.in_pfReq.bits.get_blockOff) === PfSource.NONE)))
    replay_Q0.io.enq <> io.in_pfReq
    replay_Q0.io.enq.valid := io.in_pfReq.fire && !s0_can_flow_filter && !(s0_skip_bop || s0_skip_spp)
    replay_Q0.io.flush := false.B
    //only l2 pf req need go quiteUpdateQ
    quiteUpdateQ.io.enq.valid := s0_can_send && io.out_pfReq.fire
    quiteUpdateQ.io.enq.bits := io.out_pfReq.bits
    quiteUpdateQ.io.enq.bits.pfVec := s0_train_pfVec(io.out_pfReq.bits.get_blockOff) | io.out_pfReq.bits.pfVec
    quiteUpdateQ.io.flush := false.B
    s0_valid := quiteUpdateQ.io.deq.fire || replay_Q0.io.deq.fire || io.in_respReq.fire //|| q_hint2llc.io.deq.valid
    s0_req := ParallelPriorityMux(
      Seq(
        io.in_trainReq.valid -> io.in_trainReq.bits,
        replay_Q0.io.deq.valid -> replay_Q0.io.deq.bits,
        quiteUpdateQ.io.deq.valid -> quiteUpdateQ.io.deq.bits,
        io.in_respReq.valid -> pf_resp2pf_req(io.in_respReq.bits)
       // q_hint2llc.io.deq.valid -> q_hint2llc.io.deq.bits,
      )
    )
    replay_Q0.io.deq.ready := !io.in_trainReq.valid
    quiteUpdateQ.io.deq.ready := !io.in_trainReq.valid && !io.in_pfReq.valid && !replay_Q0.io.deq.valid
    io.in_respReq.ready := !io.in_trainReq.valid  && !io.in_pfReq.valid && !replay_Q0.io.deq.valid && quiteUpdateQ.io.deq.valid

    val s0_fwd_evict_hitTrain = WireInit(false.B);dontTouch(s0_fwd_evict_hitTrain)
    val s0_fwd_evict_blkOff = WireInit(0.U(blkOffsetBits.W))

    when(s0_fwd_evict_hitTrain){
        s0_train_pfVec(s0_fwd_evict_blkOff) := PfSource.NONE
      }.elsewhen(s0_fromTrain && !s0_train_tagHit){
      for(i <- 0 until(blkNums)){
        s0_train_pfVec(i) := s0_result.cVec(i)
      }
    }.elsewhen(s0_update_train_pfVec){
        s0_train_pfVec(io.in_pfReq.bits.get_blockOff) := s0_train_pfVec(io.in_pfReq.bits.get_blockOff) | io.in_pfReq.bits.pfVec
    }

    s0_train_pageTag := RegEnable(s0_result.tag, 0.U, s0_fromTrain)
    s0_skip_filter := quiteUpdateQ.io.deq.fire
    
    val s0_read = WireInit(replay_Q0.io.deq.fire || io.in_trainReq.fire || io.in_respReq.fire);dontTouch(s0_read)
    val s0_rIdx = WireInit(ft_get_idx(s0_req.get_pageAddr));dontTouch(s0_rIdx)
    val s0_train_Idx = RegEnable(s0_rIdx, s0_fromTrain);dontTouch(s0_train_Idx)
    val s0_train_pfVec_need_replace = WireInit(s0_fromTrain && !s0_train_tagHit)
    // --------------------------------------------------------------------------------
    // stage 1
    // --------------------------------------------------------------------------------
    // calculate
    // send out prefetch request
    val s1_valid = VecInit.fill(dupNums)(RegNext(s0_valid,false.B));dontTouch(s1_valid)
    val s1_req = VecInit.fill(dupNums)(RegEnable(s0_req,0.U.asTypeOf(new PrefetchReq),s0_valid));dontTouch(s1_req)
    val s1_result = VecInit.fill(dupNums)(RegEnable(s0_result,0.U.asTypeOf(fTableEntry()),s0_valid));dontTouch(s1_result)
    val s1_isHint2llc = RegNext(s0_isHint2llc,false.B)
    val s1_fromTrain = RegNext(s0_fromTrain,false.B);dontTouch(s1_fromTrain)
    val s1_skip_filter = RegNext(s0_skip_filter,false.B)
    val s1_isRespRedirect = RegNext(s0_isRespRedirect,false.B)

    val s1_train_pfVec_need_replace = RegNext(s0_train_pfVec_need_replace,false.B)
    val s1_wIdx = RegEnable(s0_train_Idx,s0_train_pfVec_need_replace)
    val s1_write_train_pfVec = RegEnable(s0_train_pfVec,s0_train_pfVec_need_replace)
    val s1_write_train_pageTage = RegEnable(s0_train_pageTag,s0_train_pfVec_need_replace)

    val s1_oldAddr = WireInit(s1_req(1).addr);dontTouch(s1_oldAddr)
    val s1_dup_offset = WireInit(s1_req(1).set(dupOffsetBits-1+dupBits-1,dupOffsetBits-1));dontTouch(s1_dup_offset)

    val s1_pageAddr = WireInit(s1_req(1).get_pageAddr);dontTouch(s1_pageAddr)
    val s1_blkOffset = WireInit(s1_req(1).get_blockOff);dontTouch(s1_blkOffset)
    val s1_hit = WireInit(VecInit.fill(dupNums)(false.B))
    
    val s1_hitForMap_filtedpfVec = WireInit(VecInit.fill(dupNums)(0.U(PfSource.bits.W)));dontTouch(s1_hitForMap_filtedpfVec)
    val s1_hitForMap_bitVec = WireInit(VecInit.fill(dupNums)(VecInit.fill(blkNums)(false.B)));dontTouch(s1_hitForMap_bitVec)
    //val hitForMap_needDrop = WireInit(VecInit.fill(dupNums)(false.B));dontTouch(hitForMap_needDrop)
    val s1_can_send2_pfq = WireInit(VecInit.fill(dupNums)(false.B));dontTouch(s1_can_send2_pfq)
    //val s1_anchored_longest_blkOff = WireInit(VecInit.fill(dupNums)(0.U(blkOffsetBits.W)));dontTouch(s1_anchored_longest_blkOff)
    val s1_next_VecState = WireInit(VecInit.fill(dupNums)(0.U(PfVectorConst.bits.W)))

    val s1_wBitMap = WireInit(VecInit.fill(dupNums)(VecInit.fill(blkNums)(0.U(FitlerVecState.bits.W))))
    val s1_wData = WireInit(VecInit.fill(dupNums)(0.U.asTypeOf(fTableEntry())));dontTouch(s1_wData)

    val s1_can_send_bopResp = WireInit(s1_isRespRedirect && has_bop(s1_result(1).cVec(s1_blkOffset)));dontTouch(s1_can_send_bopResp)

    for(i <- 0 until(dupNums)) {
      val trigerId = s1_req(i).pfVec
      val anchored_cVec = s1_result(i).cVec
      val anchored_value = s1_result(i).cVec(s1_blkOffset)
      s1_next_VecState(i) := Mux(s1_hit(i),FitlerVecState.getVecState(true.B, originV = anchored_value, trigerId = s1_req(i).pfVec),s1_req(i).pfVec)

      s1_hit(i) := s1_result(i).valid && ft_get_tag(s1_pageAddr) === s1_result(i).tag
      //hitForMap_needDrop(i) := hit(i) && FitlerVecState.hasMerged(s1_req(i).pfVec, anchored_value)
      for (j <- 0 until s1_result(i).cVec.length){
          when(s1_hit(i)){       
              s1_hitForMap_bitVec(i)(j) := anchored_cVec(j) =/= PfSource.NONE
              s1_hitForMap_filtedpfVec(i) := s1_result(i).cVec(s1_blkOffset)
          }.otherwise{
              s1_hitForMap_bitVec(i)(j) := false.B
              s1_hitForMap_filtedpfVec(i) := PfSource.NONE
          }
      }
      //s1_anchored_longest_blkOff(i) := OneHot.OH1ToUInt(HighestBit(s1_hitForMap_bitVec(i).asUInt,blkNums))
      // should filter when any other prefetchBitVec existed expected prefetch from bop
      s1_can_send2_pfq(i) := !s1_isRespRedirect && !s1_fromTrain && !s1_skip_filter && (!s1_hit(i) || (s1_hit(i) && (anchored_value === PfSource.NONE)))//anchored_value === PfSource.NONE //|| anchored_value === PfSource.BOP || anchored_value === PfSource.SMS

      when(!s1_isRespRedirect && !s1_fromTrain){
        for (j <- 0 until blkNums){
          s1_wBitMap(i)(j) := Mux(j.asUInt === s1_blkOffset, s1_next_VecState(i), PfSource.NONE) 
        }
        s1_wData(i).valid := true.B
        s1_wData(i).tag := ft_get_tag(s1_pageAddr)
        s1_wData(i).cVec := s1_wBitMap(i)
      }
    }
    val s1_pfOut_valid = WireInit(false.B)
    val s1_need_write = WireInit(s1_pfOut_valid);dontTouch(s1_need_write)
    // --------------------------------------------------------------------------------
    // stage 2
    // --------------------------------------------------------------------------------
    // update consensusTable
    val s2_valid = RegNext(s1_valid(4),false.B)
    val s2_hit = RegEnable(s1_hit(4), false.B, s1_valid(4))
    val s2_can_send2_pfq = RegNext(s1_can_send2_pfq(3))
    val s2_isHint2llc = RegNext(s1_isHint2llc)
    val s2_need_write = RegNext(s1_need_write,false.B)
    val s2_req = RegEnable(s1_req(4), 0.U.asTypeOf(new PrefetchReq), s1_valid(4))
    val s2_wData = RegEnable(s1_wData(4), 0.U.asTypeOf(fTableEntry()), s1_valid(4));dontTouch(s2_wData)
    
    val s2_wIdx = WireInit(0.U(log2Up(fTableEntries).W));dontTouch(s2_wIdx)
    
    val s2_evictQ_enq_valid = WireInit(s2_valid && s2_need_write)
    val s2_normalWrite = WireInit(s2_valid && s2_need_write)
    val s2_saved_blkAddr = WireInit(get_saved_blkAddr(s2_req.get_blkAddr));dontTouch(s2_saved_blkAddr)

    //evictQ deq
    val s2_evictQ_needWrite = evict_q.io.deq.fire
    val s2_evictQ_used = evict_q.io.count


    val s2_evictBlkAddr = WireInit(Cat(0.U((blkAddrBits-saved_blkAddrBits).W),evict_q.io.deq.bits));dontTouch(s2_evictBlkAddr)
    val s2_evictPageAddr = s2_evictBlkAddr(blkAddrBits - 1, blkOffsetBits)
    val s2_evictBlkOffset = s2_evictBlkAddr(blkOffsetBits - 1, 0);dontTouch(s2_evictBlkOffset)
    val s2_readEvict = WireInit(0.U.asTypeOf(fTableEntry()));dontTouch(s2_readEvict)

    s0_fwd_evict_hitTrain := s2_evictQ_needWrite && ft_get_tag(s2_evictPageAddr) === s0_train_pageTag
    s0_fwd_evict_blkOff := s2_evictBlkOffset

    val s2_rIdx = WireInit(ft_get_idx(s2_evictPageAddr));dontTouch(s2_rIdx)
    s2_wIdx := Mux(s2_normalWrite, ft_get_idx(s2_req.get_pageAddr), ft_get_idx(s2_evictPageAddr))
    // --------------------------------------------------------------------------------
    // stage 3
    // --------------------------------------------------------------------------------
    val s3_write = RegNext(s2_normalWrite,false.B)
    val s3_hit = RegNext(s2_hit,false.B)
    val s3_wIdx = WireInit(0.U(log2Up(fTableEntries).W));dontTouch(s3_wIdx)

    // --------------------------------------------------------------------------------
    // evict operation
    evict_q.io.enq.valid := RegNext(io.out_pfReq.fire,false.B) // if spp2llc , don't enq
    //drop highest bit
    evict_q.io.enq.bits := RegNext(get_saved_blkAddr(io.out_pfReq.bits.get_blkAddr),0.U)
    evict_q.io.deq.ready := !s2_normalWrite && s2_evictQ_used > (fTableQueueEntries-1).U;

    when(s0_read){
      s0_result := consensusTable(s0_rIdx)
    }
    when(s1_train_pfVec_need_replace){
      consensusTable(s1_wIdx).cVec := s1_write_train_pfVec
    }.elsewhen(s2_evictQ_needWrite) {
      consensusTable(s2_wIdx).cVec(s2_evictBlkOffset) := FitlerVecState.None
    }.elsewhen(s2_normalWrite) {
        when(s2_hit){
            consensusTable(s2_wIdx).cVec := s2_wData.cVec
        }.otherwise{
            consensusTable(s2_wIdx) := s2_wData
        }
    }
    io.evict.ready := true.B

  // --------------------------------------------------------------------------------
  // send out
  val s0_pfOut_valid = WireInit(s0_can_send)
  s1_pfOut_valid := WireInit(s1_valid(0) && s1_can_send2_pfq(0))
  io.out_pfReq.valid := s0_pfOut_valid || s1_pfOut_valid
  io.out_pfReq.bits := Mux(s1_pfOut_valid,s1_req(0),io.in_pfReq.bits)
  io.in_pfReq.ready := !(s1_valid(0) && s1_can_send2_pfq(0))

  io.out_respReq.valid := s1_valid(1) && s1_can_send_bopResp
  io.out_respReq.bits.tag := s1_req(1).tag
  io.out_respReq.bits.set := s1_req(1).set
  io.out_respReq.bits.pfVec := s1_req(1).pfVec

  dontTouch(io.hint2llc_out)
  io.hint2llc_out.valid := s1_valid(3) && s1_can_send2_pfq(3) && s1_isHint2llc
  io.hint2llc_out.bits := s1_req(3)

    val s0_filterd_spp = s0_can_flow_filter && io.in_pfReq.fire && s0_train_pfVec(io.in_pfReq.bits.get_blockOff) === PfSource.NONE
    val s0_filterd_bop = s0_can_flow_filter && io.in_pfReq.fire && s0_train_pfVec(io.in_pfReq.bits.get_blockOff) === PfSource.NONE
    val s1_filter = s1_valid(1) && !s1_fromTrain && !s1_skip_filter && !s1_can_send2_pfq(s1_dup_offset)
    XSPerfAccumulate("hyper_filter_input",io.in_pfReq.fire)
    XSPerfAccumulate("hyper_filter_input_sms",io.in_pfReq.fire && io.in_pfReq.bits.hasSMS)
    XSPerfAccumulate("hyper_filter_input_bop",io.in_pfReq.fire && io.in_pfReq.bits.hasBOP)
    XSPerfAccumulate("hyper_filter_input_spp",io.in_pfReq.fire && io.in_pfReq.bits.hasSPP)
    XSPerfAccumulate("hyper_filter_input_respBOP",io.in_respReq.fire && io.in_respReq.bits.hasBOP)
    // XSPerfAccumulate("hyper_filter_input_hint2llc",io.req.valid && io.is_hint2llc)
    XSPerfAccumulate("hyper_filter_output",io.out_pfReq.valid)
    XSPerfAccumulate("hyper_filter_output_sms",io.out_pfReq.valid && io.out_pfReq.bits.hasSMS)
    XSPerfAccumulate("hyper_filter_output_bop",io.out_pfReq.valid && io.out_pfReq.bits.hasBOP)
    XSPerfAccumulate("hyper_filter_output_spp",io.out_pfReq.valid && io.out_pfReq.bits.hasSPP)
    XSPerfAccumulate("hyper_filter_output_respBOP",io.out_respReq.fire && io.out_respReq.bits.hasSPP)
    XSPerfAccumulate("hyper_filter_ouput_hint2llc",io.hint2llc_out.valid)
    XSPerfAccumulate("hyper_filter_nums",s0_filterd_spp || s0_filterd_bop || s1_filter)
    XSPerfAccumulate("hyper_filter_evict_fomMshr",io.evict.fire)
    XSPerfAccumulate("hyper_filter_evict_fromQ",s2_evictQ_needWrite)
}

class weightRR[T <: Data](gen: T, n: Int, weightBits: Int, parentName:String = "Unknown")(implicit p: Parameters) extends HyperPrefetchDev2Module{
  val io = IO(new Bundle(){
    val in = Flipped(Vec(n, Decoupled(gen)))
    val in_weight = Flipped(Valid(Vec(n, UInt(weightBits.W))))
    val out = Decoupled(gen)
  })
  val set_weight_vec = RegEnable(io.in_weight.bits, 0.U.asTypeOf(Vec(n, UInt(weightBits.W))), io.in_weight.valid)
  val weight_vec = RegInit(0.U.asTypeOf(Vec(n,UInt(weightBits.W))))
  val rr_arb = Module(new FastArbiter(gen,n))
  val need_updateW = WireInit(weight_vec.map(_ === 0.U).reduce(_&&_));dontTouch(need_updateW)
  for(i <- 0 until n){
    rr_arb.io.in(i).valid := io.in(i).fire
    rr_arb.io.in(i).bits := io.in(i).bits
    if(i == 0){
      io.in(i).ready := io.out.ready && (weight_vec(i) =/= 0.U || need_updateW || !io.in(n-1-i).valid)
    }else{
      io.in(i).ready := io.out.ready && (!io.in(n-1-i).valid || weight_vec.zip(io.in).take(i).map(x => Mux(x._1 =/= 0.U && x._2.valid,false.B,true.B)).reduce(_ && _) && weight_vec(i) =/= 0.U)
    }
    
    when(io.in(i).fire){
      weight_vec(i) := Mux(weight_vec(i) =/= 0.U, weight_vec(i) - 1.U, 0.U)
    }.elsewhen(need_updateW){
      weight_vec(i) := set_weight_vec(i)
    }
  }
  io.out <> rr_arb.io.out
}
class DynamicPriorityArbiter[T <: Data](gen: T, n: Int, weightBits: Int, parentName:String = "Unknown")(implicit p: Parameters) extends HyperPrefetchDev2Module{
  val io = IO(new Bundle {
    val in = Flipped(Vec(n, Decoupled(gen)))
    val in_weight = Flipped(Valid(Vec(n, UInt(weightBits.W))))
    val in_priority =Input(Vec(n, UInt(weightBits.W)))
    val out = Decoupled(gen)
  })
  dontTouch(io.in)
  val validInputs = VecInit(io.in.map(_.valid))
  // Generate a mask for prioritized valid inputs based on priority signals
  val priorityInputs = io.in_priority
  val highestPriority = priorityInputs.reduce((a, b) => Mux(a > b, a, b))
  val prioritizedInputs = VecInit(io.in_priority.map(x => x === highestPriority))
  
  // Generate a mask for granted input
  val grantMask = RegInit(0.U(n.W));dontTouch(grantMask)
  when(io.out.fire) {
    grantMask := Cat(validInputs.tail :+ validInputs.head)
  }

  io.out.valid := validInputs.asUInt.orR
  io.out.bits := MuxCase(0.U.asTypeOf(new PrefetchReq), (prioritizedInputs.zipWithIndex :+ (validInputs.asUInt.orR, n - 1)).map {
    case (p, i) => (p, io.in(i).bits)
  })

  for (i <- 0 until n) {
    io.in(i).ready := io.out.ready && grantMask(i)
  }
}

//Only used for hybrid spp and bop
class HyperPrefetchDev2(parentName:String = "Unknown")(implicit p: Parameters) extends HyperPrefetchDev2Module {
  val io = IO(new Bundle() {
    val l2_pf_en = Input(Bool())
    val l2_pf_ctrl = Input(UInt(Csr_PfCtrlBits.W))
    val train = Flipped(DecoupledIO(new PrefetchTrain))
    val req = DecoupledIO(new PrefetchReq)
    val resp = Flipped(DecoupledIO(new PrefetchResp))
    val evict = Flipped(DecoupledIO(new PrefetchEvict))
    val recv_addr = Flipped(ValidIO(UInt(64.W)))
    val hint2llc = ValidIO(new PrefetchReq)
  })
  dontTouch(io)
  // --------------------------------------------------------------------------------
  // csr pf ctrl
  // --------------------------------------------------------------------------------
  // ctrl[15,14,13,12,11,10,9,8,  7, 6, 5, 4, 3,  2, 1, 0]
  //                    |     |   |           |  |      |
  //                    ------    ------------   ------
  //                      |            |           |
  //                  FTConfig    sppConfig     ctrlSwitch
  // default 0000_0101_1110_0111
  // hex:    0    5    e    7
  // default value: 0x05e7
  //switchConfig[0,1,2]
    //| ctrl[0] -> enable sms
    //| ctrl[1] -> enable bop
    //| ctrl[2] -> enable spp
  //sppConfig[3,4,5,6,7]
    //| sppConfig[0] -> enable hint2llc   
    //| sppConfig[1] -> enable Nextline Agreesive
    //| sppConfig[2] -> enable bp recovery
    //| sppConfig[3] -> enable shareBO
    //| sppConfig[4] -> enable slowLookUp
  // filterTableConfig[8,9,10]
    //| fTConfig[0]  -> enable fitter sms
    //| fTConfig[1]  -> enable filter bop
    //| fTConfig[2]  -> enable fitter spp
  val ctrlSwitch = WireInit(PfCtrlConst.Switch.get_fields(io.l2_pf_ctrl));dontTouch(ctrlSwitch)
  val ctrl_SMSen = WireInit(ctrlSwitch(PfCtrlConst.Switch.SMS));dontTouch(ctrl_SMSen)
  val ctrl_BOPen = WireInit(ctrlSwitch(PfCtrlConst.Switch.BOP));dontTouch(ctrl_BOPen)
  val ctrl_SPPen = WireInit(ctrlSwitch(PfCtrlConst.Switch.SPP));dontTouch(ctrl_SPPen)

  val ctrl_sppConfig = WireInit(PfCtrlConst.SppConfig.get_fields(io.l2_pf_ctrl));dontTouch(ctrl_sppConfig)
  val ctrl_fitlerTableConfig = WireInit(PfCtrlConst.FitlerTableConfig.get_fields(io.l2_pf_ctrl));dontTouch(ctrl_fitlerTableConfig)
  
  // --------------------------------------------------------------------------------
  // instance each algorithm moudle
  // --------------------------------------------------------------------------------
  val fTable = Module(new FilterTable("hyper_tTable"))

  val spp = Module(new SignaturePathPrefetch()(p.alterPartial({
        case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(SPPParameters()))
  })))
  val bop = Module(new BestOffsetPrefetch()(p.alterPartial({
        case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(BOPParameters()))
  })))
  val sms = Module(new PrefetchReceiver()(p.alterPartial({
        case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(PrefetchReceiverParams()))
  })))

  val train_spp_q = Module(new ReplaceableQueueV2(new PrefetchTrain, entries = 8))

  val q_sms = Module(new ReplaceableQueueV2(new PrefetchReq, sms_pfReqQueueEntries))
  val q_bop = Module(new ReplaceableQueueV2(new PrefetchReq, bop_pfReqQueueEntries))
  val q_spp = Module(new ReplaceableQueueV2(new PrefetchReq, spp_pfReqQueueEntries))
  val q_hint2llc = Module(new ReplaceableQueueV2(new PrefetchReq, hin2llc_pfReqQueueEntries))
  // val pftQueue = Module(new PrefetchQueue(inflightEntries = hyperParams.inflightEntries))
  // --------------------------------------------------------------------------------
  // global counter 
  // --------------------------------------------------------------------------------
  // seperate eache prefetcher perf counter
  def get_perfState(perfCounter:UInt, allIssued:UInt, perf_state: UInt)={
    when((perfCounter << 2) > allIssued + allIssued + allIssued) {
      perf_state := 3.U
    } .elsewhen((perfCounter << 1) > allIssued) {
      perf_state := 2.U
    } .elsewhen((perfCounter << 2) > allIssued) {
      perf_state := 1.U
    } .otherwise {
      perf_state := 0.U
    }
  }
  class globalCounter extends HyperPrefetchDev2Bundle{
    val l1pf_hitAcc = UInt(6.W)
    val l2pf_hitAcc = UInt(6.W)
    val bop_issued = UInt(7.W)
    val spp_issued = UInt(7.W)
    val l1pf_issued = UInt(7.W)
  }
  val ghr_l1pf_hitAccState = WireInit(0.U(PfaccState.bits.W))
  val ghr_l2pf_hitAccState = WireInit(0.U(PfaccState.bits.W)) 
  val ghr = RegInit(0.U.asTypeOf(new  globalCounter()));dontTouch(ghr)
  val ghr_coarse = RegInit(0.U.asTypeOf(new  globalCounter()));dontTouch(ghr_coarse)
  val ghr_last1Round = RegInit(0.U.asTypeOf(new  globalCounter()));dontTouch(ghr_last1Round)
  val ghr_last2Round = RegInit(0.U.asTypeOf(new  globalCounter()));dontTouch(ghr_last2Round)
  val ghr_last3Round = RegInit(0.U.asTypeOf(new  globalCounter()));dontTouch(ghr_last3Round)
  val ghr_last4Round = RegInit(0.U.asTypeOf(new  globalCounter()));dontTouch(ghr_last4Round)
  val ghr_avgRound = RegInit(0.U.asTypeOf(new  globalCounter()));dontTouch(ghr_avgRound)
  // fineGrain
  val ghrCounter_fineGrain = Counter(io.l2_pf_en, 512)
  val ghr_roundReset = WireInit(false.B);dontTouch(ghr_roundReset)
  val ghr_roundCnt = ghrCounter_fineGrain._1
  ghr_roundReset := ghrCounter_fineGrain._2
  // coarseGrain
  val ghrCounter_coarseGrain = Counter(io.l2_pf_en, 4096)
  val ghr_roundReset_coarseGrain = WireInit(false.B);dontTouch(ghr_roundReset)
  val ghr_roundCnt_coarseGrain = ghrCounter_coarseGrain._1
  ghr_roundReset_coarseGrain := ghrCounter_coarseGrain._2

  val deadPfEviction = RegInit(0.U(13.W))
  val issued = RegInit(0.U(16.W))
  val pf_deadCov_state = WireInit(0.U(PfcovState.bits.W));dontTouch(pf_deadCov_state)
  when(io.evict.valid && io.evict.bits.is_prefetch) {
    deadPfEviction := deadPfEviction + 1.U
  }
  when(io.req.fire){
    issued := issued + 1.U
  }
  when(ghr_roundReset) {
    deadPfEviction := 0.U
    issued := 0.U
    get_perfState(deadPfEviction,issued,pf_deadCov_state) 
  }
  // global acc state
  val ghrTrain = io.train.bits
  when((io.train.valid && io.train.bits.state === AccessState.PREFETCH_HIT)){
    when(ghrTrain.is_l1pf){
      ghr.l1pf_hitAcc := ghr.l1pf_hitAcc + 1.U
    }
    when(ghrTrain.is_l2pf){
      ghr.l2pf_hitAcc := ghr.l2pf_hitAcc + 1.U
      ghr_coarse.l2pf_hitAcc := ghr_coarse.l2pf_hitAcc + 1.U
    }
  }
  when(io.req.fire){
    when(io.req.bits.is_l1pf){
      ghr.l1pf_issued := ghr.l1pf_issued + 1.U
    }
    when(io.req.bits.hasBOP){
      ghr.bop_issued := ghr.bop_issued + 1.U
      ghr_coarse.bop_issued := ghr_coarse.bop_issued + 1.U
    }
    when(io.req.bits.hasSPP){
      ghr.spp_issued := ghr.spp_issued + 1.U
      ghr_coarse.spp_issued := ghr_coarse.spp_issued + 1.U
    }
  }
  //ghr update
  def get_accumu2(x:UInt,y:UInt) = (x + y)
  def get_avg2(x:UInt,y:UInt) = (x + y) >> 2.U
  //avgRound 
  ghr_avgRound.l2pf_hitAcc := get_avg2(ghr.l2pf_hitAcc,ghr_last1Round.l2pf_hitAcc)
  ghr_avgRound.bop_issued  := get_avg2(ghr.bop_issued ,ghr_last1Round.bop_issued )
  ghr_avgRound.spp_issued  := get_avg2(ghr.spp_issued ,ghr_last1Round.spp_issued )
  when(ghr_roundReset){
    ghr := 0.U.asTypeOf(new globalCounter())
    ghr_last1Round := ghr
    ghr_last2Round := ghr_last1Round
    ghr_last3Round := ghr_last2Round
    ghr_last4Round := ghr_last3Round
    get_perfState(ghr.l2pf_hitAcc, ghr.bop_issued + ghr.spp_issued, ghr_l2pf_hitAccState) 
  }
  when(ghr_roundReset_coarseGrain){
    ghr_coarse := 0.U.asTypeOf(new globalCounter())
  }
  
  // --------------------------------------------------------------------------------
  // spp train diverter queue
  // --------------------------------------------------------------------------------
  //devert
  def sms2sppTrain(in:PrefetchReq):PrefetchTrain={
    val out = WireInit(0.U.asTypeOf(new PrefetchTrain))
    out.tag := in.tag
    out.set := in.set
    out.needT := false.B
    out.source := 0.U
    out
  }    
  train_spp_q.io.enq.valid := io.train.valid || sms.io.req.valid
  train_spp_q.io.enq.bits := Mux(io.train.valid,io.train.bits,sms2sppTrain(sms.io.req.bits))
  // train_spp_q.io.enq.valid := io.train.valid
  // train_spp_q.io.enq.bits := io.train.bits
  train_spp_q.io.flush := false.B

  spp.io.train.valid := ctrl_SPPen && train_spp_q.io.deq.valid
  spp.io.train.bits := train_spp_q.io.deq.bits
  train_spp_q.io.deq.ready := spp.io.train.ready
  //
  bop.io.train.valid := ctrl_BOPen && io.train.valid
  bop.io.train.bits := io.train.bits
  //TODO: need respALL ?
  //
  bop.io.resp.valid := io.resp.valid && io.resp.bits.hasBOP
  bop.io.resp.bits := io.resp.bits
  io.resp.ready := bop.io.resp.ready
  fTable.io.in_respReq.valid := false.B
  fTable.io.in_respReq.bits <> 0.U.asTypeOf(new PrefetchResp)
  fTable.io.out_respReq.ready := false.B
  // val respQ = Module(new ReplaceableQueueV2(new PrefetchResp,4))
  // respQ.io.flush := false.B
  // respQ.io.enq <> fTable.io.out_respReq
  // bop.io.resp <>  respQ.io.deq
  // fTable.io.in_respReq <> io.resp

  spp.io.resp := DontCare
  spp.io.from_ghr.valid := ghr_roundReset
  spp.io.from_ghr.bits.l2_deadCov_state := pf_deadCov_state
  spp.io.from_ghr.bits.l2_hitAcc_state := ghr_l2pf_hitAccState
  spp.io.from_ghr.bits.shareBO := RegNext(bop.io.shareBO,0.S)
  spp.io.from_ghr.bits.global_queue_used := q_spp.io.full //RegNext(pftQueue.io.queue_used)
  spp.io.sppCtrl := ctrl_sppConfig

  sms.io.recv_addr.valid := ctrl_SMSen && io.recv_addr.valid
  sms.io.recv_addr.bits := io.recv_addr.bits
  sms.io.req.ready := true.B

  q_hint2llc.io.enq <> spp.io.req_hint2llc
  //
  q_sms.io.enq <> sms.io.req
  q_bop.io.enq <> bop.io.req
  q_spp.io.enq <> spp.io.req

  // --------------------------------------------------------------------------------
  // stage 0
  // --------------------------------------------------------------------------------
  val s1_ready = WireInit(false.B)
  val s0_req = WireInit(0.U.asTypeOf(DecoupledIO(new PrefetchReq)))
  q_hint2llc.io.deq.ready := s1_ready && !q_sms.io.deq.valid && !q_bop.io.deq.valid && !q_spp.io.deq.valid
  val out_wRR =  Module(new weightRR(new PrefetchReq, n = 2, weightBits = 4))

  // --------------------------------------------------------------------------------
  // pfQueue scheduler algorithm
  // --------------------------------------------------------------------------------
  // SPP Scheduler Table       |    BOP Scheduler Table   
  // |bop\sms| N | L | H |     |    |bop\sms| N | L | H |
  // --------------------      |    --------------------
  // | N     | 1 | 3 | 5 |     |    | N     | 1 | 2 | 1 |
  // | L     | 2 | 3 | 5 |     |    | L     | 1 | 2 | 1 |
  // | H     | 2 | 3 | 5 |     |    | H     | 3 | 4 | 1 |

  val bop_state_cur = WireInit(0.U(2.W));dontTouch(bop_state_cur)
  val bop_state_avg = WireInit(0.U(2.W));dontTouch(bop_state_avg)
  val spp_state_cur = WireInit(0.U(2.W));dontTouch(spp_state_cur)
  val spp_state_avg = WireInit(0.U(2.W));dontTouch(spp_state_avg)
  val ghr_state_cur = WireInit(0.U(2.W));dontTouch(spp_state_cur)
  val ghr_state_avg = WireInit(0.U(2.W));dontTouch(spp_state_avg)
  object bop_scheduler{
    val s_NONE :: s_LOW :: s_HIGH :: Nil = Enum(3)
    def get_bop_state(acc:UInt,cov:UInt)={
      val state = WireInit(s_LOW);dontTouch(state)
      when(acc === 0.U){
        state := s_NONE
      }.elsewhen((acc << 1.U) < cov){
        state := s_LOW
      }.otherwise(
        state := s_HIGH
      )
      state
    }
    val weightBits = 4
    bop_state_cur := get_bop_state(ghr.l2pf_hitAcc,ghr.bop_issued)
    bop_state_avg := get_bop_state(ghr_avgRound.l2pf_hitAcc,ghr_avgRound.bop_issued);dontTouch(bop_state_avg)

    def get_bop_weight(now:UInt = bop_state_cur, last:UInt = bop_state_avg, spp_state:UInt):UInt={
      val weight = WireInit(0.U(weightBits.W));dontTouch(weight)

      weight := MuxLookup(
        Cat(spp_state,bop_state_cur),
        1.U,
        Seq(
          Cat(s_NONE,s_NONE)  -> 1.U,
          Cat(s_NONE,s_LOW)   -> 1.U,
          Cat(s_NONE,s_HIGH)  -> 3.U,
          Cat(s_LOW, s_NONE)  -> 2.U,
          Cat(s_LOW, s_LOW)   -> 2.U,
          Cat(s_LOW, s_HIGH)  -> 4.U,
          Cat(s_HIGH,s_NONE)  -> 1.U,
          Cat(s_HIGH,s_LOW)   -> 1.U,
          Cat(s_HIGH,s_HIGH)  -> 1.U,
        )
      )
      weight  
    }
    def flush_pfQ = ghr_avgRound.l2pf_hitAcc === 0.U
  }
  
  object spp_scheduler{
    val s_NONE :: s_LOW :: s_HIGH :: Nil = Enum(3)
    def get_spp_state(acc:UInt,cov:UInt)={
      val state = WireInit(s_LOW);dontTouch(state)
      when(acc === 0.U){
        state := s_NONE
      }.elsewhen((acc << 1.U) < cov){
        state := s_LOW
      }.otherwise(
        state := s_HIGH
      )
      state
    }
    val weightBits = 4
    spp_state_cur := get_spp_state(ghr.l2pf_hitAcc, ghr.spp_issued)
    spp_state_avg := get_spp_state(ghr_avgRound.l2pf_hitAcc, ghr_avgRound.spp_issued);dontTouch(spp_state_avg)

    def is_rubbish:Bool = (ghr_last1Round.l2pf_hitAcc === 0.U && ghr_last2Round.l2pf_hitAcc === 0.U && ghr_last3Round.l2pf_hitAcc === 0.U && ghr_last4Round.l2pf_hitAcc === 0.U)
    def get_spp_weight(now:UInt = spp_state_cur, last:UInt = spp_state_avg, bop_state:UInt):UInt={
      val weight = WireInit(0.U(weightBits.W));dontTouch(weight)

      weight := MuxLookup(
        Cat(spp_state_cur,bop_state),
        1.U,
        Seq(
          Cat(s_NONE,s_NONE)  -> 2.U,
          Cat(s_NONE,s_LOW )  -> 2.U,
          Cat(s_NONE,s_HIGH)  -> 2.U,
          Cat(s_LOW ,s_NONE)  -> 3.U,
          Cat(s_LOW ,s_LOW )  -> 3.U,
          Cat(s_LOW ,s_HIGH)  -> 3.U,
          Cat(s_HIGH,s_NONE)  -> 5.U,
          Cat(s_HIGH,s_LOW )  -> 5.U,
          Cat(s_HIGH,s_HIGH)  -> 5.U,
        )
      )
      weight
    }
    
    def flush_pfQ = ghr_avgRound.l2pf_hitAcc === 0.U || is_rubbish
    
  }
  object ghr_scheduler{
    val s_NONE :: s_LOW :: s_HIGH :: Nil = Enum(3)
    def get_ghr_state(acc:UInt,cov:UInt)={
      val state = WireInit(s_LOW);dontTouch(state)
      when(acc === 0.U){
        state := s_NONE
      }.elsewhen((acc << 1.U) < cov){
        state := s_LOW
      }.otherwise(
        state := s_HIGH
      )
      state
    }
    val weightBits = 4
    ghr_state_cur := get_ghr_state(ghr.l2pf_hitAcc, ghr.bop_issued)
    ghr_state_avg := get_ghr_state(ghr_avgRound.l2pf_hitAcc, ghr_avgRound.bop_issued);dontTouch(ghr_state_avg)

    def get_bop_weight(now:UInt = ghr_state_cur, last2avg:UInt = ghr_state_avg):UInt={
      val weight = WireInit(0.U(weightBits.W));dontTouch(weight)

      weight := MuxLookup(
        Cat(now,last2avg),
        1.U,
        Seq(
          Cat(s_NONE,s_NONE)  -> 2.U,
          Cat(s_NONE,s_LOW)   -> 1.U,
          Cat(s_NONE,s_HIGH)  -> 3.U,
          Cat(s_LOW ,s_NONE)  -> 2.U,
          Cat(s_LOW ,s_LOW)   -> 2.U,
          Cat(s_LOW ,s_HIGH)  -> 2.U,
          Cat(s_HIGH,s_NONE)  -> 1.U,
          Cat(s_HIGH,s_LOW)   -> 1.U,
          Cat(s_HIGH,s_HIGH)  -> 1.U,
        )
      )
      weight
    }
    def get_spp_weight(now:UInt = ghr_state_cur, last2avg:UInt = ghr_state_avg):UInt={
      val weight = WireInit(0.U(weightBits.W));dontTouch(weight)

      weight := MuxLookup(
        Cat(now,last2avg),
        1.U,
        Seq(
          Cat(s_NONE,s_NONE)  -> 2.U,
          Cat(s_NONE,s_LOW)   -> 2.U,
          Cat(s_NONE,s_HIGH)  -> 2.U,
          Cat(s_LOW ,s_NONE)  -> 3.U,
          Cat(s_LOW ,s_LOW)   -> 3.U,
          Cat(s_LOW ,s_HIGH)  -> 3.U,
          Cat(s_HIGH,s_NONE)  -> 5.U,
          Cat(s_HIGH,s_LOW)   -> 5.U,
          Cat(s_HIGH,s_HIGH)  -> 5.U,
        )
      )
      weight
    }

    def is_rubbish:Bool = WireInit(ghr_avgRound.l2pf_hitAcc === 0.U && ghr_coarse.spp_issued =/= 0.U);dontTouch(is_rubbish)
    def sms_flush_pfQ = ghr.l1pf_hitAcc === 0.U && ghr_coarse.l1pf_hitAcc << 4.U < ghr_coarse.l1pf_issued
    def bop_flush_pfQ = false.B//ghr.l2pf_hitAcc === 0.U && ghr_coarse.l2pf_hitAcc << 4.U < (ghr_coarse.bop_issued + ghr_coarse.spp_issued)
    def spp_flush_pfQ = {
      val s_IDLE :: s_WAIT :: s_RESET :: Nil = Enum(3)
      val state = RegInit(s_IDLE)
      val resetCounter = RegInit(0.U(2.W))
      val resetThreshold = RegInit(0.U(2.W))

      val lut_Threshold = WireInit(0.U(2.W))
      def empty_hit(x:UInt) = x === 0.U
      lut_Threshold  := MuxLookup(
        Cat(empty_hit(ghr_last3Round.l2pf_hitAcc),empty_hit(ghr_last4Round.l2pf_hitAcc)),
        1.U,
        Seq(
          "b100".U  -> 1.U,
          "b110".U  -> 2.U,
          "b111".U  -> 3.U,
        )
      )

      when(is_rubbish){
        resetThreshold := lut_Threshold
      }

      when(state === s_WAIT && ghr_roundReset){
        resetCounter := resetCounter + 1.U
      }.elsewhen(state === s_IDLE){
        resetCounter := 0.U
      }

      switch(state){
        is(s_IDLE){
          when(is_rubbish){
            state := s_WAIT
          }
        }
        is(s_WAIT){
          when(resetCounter === resetThreshold){
            state := s_RESET
          }
        }
        is(s_RESET){
          when(ghr_roundReset){
            state := s_IDLE
          }
        }
      }
      
      val flush =WireInit(state === s_WAIT)
      flush
    }
  }

  q_sms.io.flush := false.B
  q_bop.io.flush := ghr_scheduler.bop_flush_pfQ
  q_spp.io.flush := ghr_scheduler.spp_flush_pfQ
  q_hint2llc.io.flush := false.B

  out_wRR.io.in(0) <> q_bop.io.deq
  out_wRR.io.in(1) <> q_spp.io.deq
  out_wRR.io.in_weight.valid := ghr_roundReset
  out_wRR.io.in_weight.bits(0) := Mux(ctrl_BOPen, ghr_scheduler.get_bop_weight(), 0.U)
  out_wRR.io.in_weight.bits(1) := Mux(ctrl_SPPen, ghr_scheduler.get_spp_weight(), 0.U)
  dontTouch(out_wRR.io)

  // qurry fTable
  // fTable.io.in_pfReq <> s0_req
  fTable.io.in_pfReq.valid := q_sms.io.deq.fire || out_wRR.io.out.fire
  fTable.io.in_pfReq.bits := ParallelPriorityMux(
    Seq(
        q_sms.io.deq.valid -> q_sms.io.deq.bits,
        out_wRR.io.out.valid -> out_wRR.io.out.bits
    )
  )
  q_sms.io.deq.ready := fTable.io.in_pfReq.ready
  out_wRR.io.out.ready := fTable.io.in_pfReq.ready && !q_sms.io.deq.valid

  fTable.io.in_trainReq.valid := io.train.valid
  fTable.io.in_trainReq.bits := io.train.bits

  fTable.io.is_hint2llc := q_hint2llc.io.deq.fire
  fTable.io.ctrl := ctrl_fitlerTableConfig
  s0_req <> fTable.io.out_pfReq
  //hint to llc
  io.hint2llc.valid := RegNextN(fTable.io.hint2llc_out.valid, 2, Some(false.B))
  io.hint2llc.bits := RegNextN(fTable.io.hint2llc_out.bits, 2 , Some(0.U.asTypeOf(new PrefetchReq)))
  fTable.io.evict.valid := false.B//io.evict.valid
  fTable.io.evict.bits := io.evict.bits
  io.evict.ready := fTable.io.evict.ready
  io.train.ready := true.B
  // --------------------------------------------------------------------------------
  // stage 1 send out 
  // --------------------------------------------------------------------------------
  // now directly flow
  val s1_req = WireInit(0.U.asTypeOf(DecoupledIO(new PrefetchReq)))
  s1_req.valid := s0_req.fire
  s1_req.bits := ParallelPriorityMux(
    Seq(
        q_sms.io.deq.valid -> q_sms.io.deq.bits,
        s0_req.valid -> s0_req.bits
    )
  )
  q_sms.io.deq.ready := s1_req.ready
  s0_req.ready := s1_req.ready //&& !q_sms.io.deq.valid
  val pftQueue = Module(new ReplaceableQueueV2(new PrefetchReq, 16))
  pftQueue.io.enq <> s1_req
  pftQueue.io.flush := false.B
  io.req <> pftQueue.io.deq

  XSPerfAccumulate("pfQ_sms_replaced_enq", q_sms.io.full && q_sms.io.enq.valid && !q_sms.io.enq.ready)
  XSPerfAccumulate("pfQ_bop_replaced_enq", q_bop.io.full && q_bop.io.enq.valid && !q_bop.io.enq.ready)
  XSPerfAccumulate("pfQ_spp_replaced_enq", q_spp.io.full && q_spp.io.enq.valid && !q_spp.io.enq.ready)
}