package coupledL2.prefetch.intel_sppDev1

import org.chipsalliance.cde.config.Parameters
import chisel3._
import chisel3.util._
import coupledL2.HasCoupledL2Parameters
import xs.utils.CircularShift
import xs.utils.perf.HasPerfLogging
import xs.utils.sram.SRAMTemplate
import coupledL2.prefetch.{PrefetchParameters,HasPrefetchParameters,ReplaceableQueueV2}
import coupledL2.prefetch.{PrefetchReq,PrefetchTrain,PrefetchResp}
import xs.utils.OneHot
import xs.utils.HighestBit
import coupledL2.prefetch.PfcovState
import coupledL2.prefetch.PfaccState
import coupledL2.PfSource
import coupledL2.prefetch.AccessState

case class SPPParameters(
  sTableEntries: Int = 256,
  bpTableEntries: Int = 64,
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

trait HasSPPParams extends HasPrefetchParameters {
//  val p: Parameters
//  val cacheParams = p(L2ParamKey)
  val sppParams = SPPParameters()
  val sTagBits = sppParams.sTagBits
  val sTableEntries = sppParams.sTableEntries
  val pTableEntries = sppParams.pTableEntries
  val pTableWays = 1
  val pTableDeltaEntries = sppParams.pTableDeltaEntries
  val signatureBits = sppParams.signatureBits
  val pTableQueueEntries = sppParams.pTableQueueEntries
  val lookCountBits = sppParams.lookCountBits
  val unpackQueueEntries = sppParams.unpackQueueEntries
  val fTableEntries = sppParams.fTableEntries
  val bpTableEntries = sppParams.bpTableEntries

  val pageAddrBits = fullAddressBits - pageOffsetBits
  val blkAddrBits = fullAddressBits - offsetBits
  val blkOffsetBits = pageOffsetBits - offsetBits
  val pTagBits = signatureBits - log2Up(pTableEntries)
  val fTagBits = fullAddressBits - offsetBits - log2Up(fTableEntries)

  val ENABLE_BP = true
  val ENABLE_NL = true

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
  // def makeSign(old_sig:UInt,new_delta:SInt)=(old_sig << 3) ^ new_delta.asUInt
  def makeSign(old_sig:UInt,new_delta:UInt)=(old_sig << 3) ^ new_delta.asUInt
}


abstract class SPPBundle(implicit val p: Parameters) extends Bundle with HasSPPParams
abstract class SPPModule(implicit val p: Parameters) extends Module with HasSPPParams with HasPerfLogging 

class SignatureTableReq(implicit p: Parameters) extends SPPBundle {
  val blkAddr = UInt(blkAddrBits.W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
  val isBP = Bool()
  val fromGHR_shareBO = SInt(6.W)
  def get_pageAddr = blkAddr >> blkOffsetBits
  def get_blkOff = blkAddr(blkOffsetBits-1,0)
  def get_accessAddr = Cat(blkAddr,0.U(offsetBits.W))
}
class BreakPointReq(implicit p: Parameters) extends SPPBundle{
  val blkAddr = UInt(blkAddrBits.W)
  val parent_sig = Vec(1,UInt(signatureBits.W))
  def get_pageAddr = blkAddr >> blkOffsetBits
}

class SignatureTableResp(implicit p: Parameters) extends SPPBundle {
  val signature = UInt(signatureBits.W)
  val delta = SInt((blkOffsetBits + 1).W)
  val block = UInt(blkAddrBits.W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
  val isBP = Bool()
}

class PatternTableResp(implicit p: Parameters) extends SPPBundle {
  val deltas = Vec(pTableDeltaEntries, SInt((blkOffsetBits + 1).W))
  val block = UInt((pageAddrBits + blkOffsetBits).W)
  val degree = UInt(lookCountBits.W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
}

class UnpackResp(implicit p: Parameters) extends SPPBundle {
  val prefetchBlock = UInt((pageAddrBits + blkOffsetBits).W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
  val degree = UInt(lookCountBits.W)
}

class SignatureTable(parentName: String = "Unknown")(implicit p: Parameters) extends SPPModule {
  val io = IO(new Bundle {
    val req = Flipped(DecoupledIO(new SignatureTableReq))
    val resp = DecoupledIO(new SignatureTableResp)
    val s0_bp_update = Flipped(ValidIO(new BreakPointReq))
  })
  assert(pageAddrBits>=(2 * log2Up(sTableEntries)),s"pageAddrBits ${pageAddrBits} ,it as least ${2 * log2Up(sTableEntries)} bits to use hash")
  def hash1(addr:    UInt) = addr(log2Up(sTableEntries) - 1, 0)
  def hash2(addr:    UInt) = addr(2 * log2Up(sTableEntries) - 1, log2Up(sTableEntries))
  def get_idx(addr:      UInt) = hash1(addr) ^ hash2(addr)
  def get_bpIdx(addr: UInt) = addr(log2Up(bpTableEntries) - 1, 0) ^ addr(2 * log2Up(bpTableEntries) - 1, log2Up(bpTableEntries))
  def get_tag(addr:      UInt) = addr(sTagBits + log2Up(sTableEntries) - 1, log2Up(sTableEntries))
  def sTableEntry() = new Bundle {
    val valid = Bool()
    val tag = UInt(sTagBits.W)
    val signature = UInt(signatureBits.W)
    val lastBlockOff = UInt(blkOffsetBits.W)
  }

  val sTable = Module(
    new SRAMTemplate(sTableEntry(), set = sTableEntries, way = 1, 
      bypassWrite = true, 
      shouldReset = true, 
      hasMbist = cacheParams.hasMbist, 
      hasShareBus = cacheParams.hasShareBus,
      hasClkGate = enableClockGate, 
      parentName = parentName
    ))

  def breakPointEntry() = new Bundle() {
    val valid = Bool()
    val pre_blkAddr = UInt(blkAddrBits.W)
    val parent_sig = Vec(1, UInt(signatureBits.W))
  }
  val bpTable = if(ENABLE_BP)Some(RegInit(VecInit(Seq.fill(bpTableEntries)(0.U.asTypeOf(breakPointEntry()))))) else None

  // --------------------------------------------------------------------------------
  // stage 0
  // --------------------------------------------------------------------------------
  //1. read sTable
  //2. write bpTable
  val s0_valid = io.req.valid
  val s0_req = io.req.bits
  sTable.io.r.req.valid       := s0_valid
  sTable.io.r.req.bits.setIdx := get_idx(s0_req.get_pageAddr)
  if(bpTable.isDefined){
    val s0_bp_page = io.s0_bp_update.bits.get_pageAddr
    val s0_bp_wIdx = WireInit(get_bpIdx(s0_bp_page));dontTouch(s0_bp_wIdx)
    when(io.s0_bp_update.valid){
      bpTable.get(s0_bp_wIdx).valid := true.B
      bpTable.get(s0_bp_wIdx).pre_blkAddr := io.s0_bp_update.bits.blkAddr
      for( i <- 0 until(io.s0_bp_update.bits.parent_sig.length)){
          bpTable.get(s0_bp_wIdx).parent_sig(i) := io.s0_bp_update.bits.parent_sig(i)
      }
    }
  }
  // --------------------------------------------------------------------------------
  //TODO : need remove this process when timing passed?
  // stage 1
  // --------------------------------------------------------------------------------
  // get sTable read data, because SRAM read delay, should send to S2 to handle rdata
  // request bp to PT if needed
  // calculate bp
  val s1_valid = RegNext(s0_valid,false.B)
  val s1_req = RegEnable(s0_req,s0_valid)
  val s1_entryData = sTable.io.r.resp.data(0)
  // bp read
  val s1_bp_rIdx = WireInit(get_bpIdx(s1_req.get_pageAddr))
  val s1_bp_hit = WireInit(false.B)
  val s1_bp_mask = WireInit(VecInit(Seq.fill(4)(false.B)))
  val s1_bp_blkAddr = WireInit(0.U(blkOffsetBits.W))
  val s1_bp_matched_sig = WireInit(0.U(signatureBits.W))
  val rotate_sig = VecInit(Seq.fill(4)(0.U(signatureBits.W)));dontTouch(rotate_sig)

  // --------------------------------------------------------------------------------
  // stage 2
  // --------------------------------------------------------------------------------
  //1. update sTable & req pTable
    //- we should write  biggest_blkAddr for solving spp timely problems, let spp prefetching farther!!!
  //2. delta BP from filterTable
    // redirect accessed blockAddr when use bp
    // calculate probeDelta for avoiding biased train signal delta, not make origin good signature overrided
    // calculate probe delata
  val s2_valid = RegNext(s1_valid,false.B)
  val s2_req = RegEnable(s1_req,s1_valid)
  val s2_entryData = RegEnable(sTable.io.r.resp.data(0), 0.U.asTypeOf(sTableEntry()),  s1_valid)
  val s2_hit = s2_valid && s2_entryData.tag === get_tag(s2_req.get_pageAddr)
  // val s2_hit = RegNext(s1_hit,false.B)

  val s2_bp_hit = RegEnable(s1_bp_hit,s1_valid)
  val s2_bp_matched_sig = RegEnable(s1_bp_matched_sig,s1_valid)
  val s2_bp_blkAddr = RegEnable(s1_bp_blkAddr,s1_valid)
 
  val s2_oldSignature = Mux(!s2_hit,0.U, s2_entryData.signature)
  // used for prefetch hit traning and probe one delta
  val s2_probeDelta   = Mux(s2_req.isBP,s2_oldSignature.head(9).tail(6).asSInt,0.S)
  def get_latest_lastTrigerDelta(now:UInt,origin:UInt):SInt={
    val is_bigger = now > origin
    val out=Mux(is_bigger,(now-origin).asSInt,io.req.bits.fromGHR_shareBO+2.S)
    out
  }
  def get_biggest_blkAddr(now:UInt,origin:UInt):UInt={
    val is_bigger = now > origin
    val out=Mux(is_bigger,now,origin)
    out
  }
  // val s2_newDelta     = Mux(s2_hit, get_latest_lastTrigerDelta(s2_req.blkOffset,s2_entryData.lastBlockOff), 0.S) // should hold 0 when miss
  val s2_newDelta =  Mux(s2_hit, s2_req.get_blkOff.asSInt - s2_entryData.lastBlockOff.asSInt, s2_req.get_blkOff.asSInt)
  //   val s2_newBlkAddr   = get_biggest_blkAddr(s2_req.get_blkAddr,Cat(s2_req.pageAddr,s2_entryData.lastBlockOff))
  val s2_newBlkAddr  = s2_req.blkAddr

  def get_predicted_sig(old_sig:UInt,delta:SInt):UInt={
    // assert delta should > 0
    // should reserve origin sig to avoid disturbing
    val sig = WireInit(0.U(signatureBits.W))
    val anchored_distance = WireInit(s2_newDelta)
    val is_biggerThan_Last2Sig = s2_newDelta.asUInt > s2_oldSignature(5,3)
    sig := Mux(is_biggerThan_Last2Sig,old_sig, makeSign(s2_oldSignature,strideMap(s2_newDelta)))
    sig
  }


  sTable.io.w.req.valid := s2_valid
  sTable.io.w.req.bits.setIdx := get_idx(s2_req.get_pageAddr)
  sTable.io.w.req.bits.data(0).valid := true.B
  sTable.io.w.req.bits.data(0).tag := get_tag(s2_req.get_pageAddr)
  //TODO: there should hold strideMap-> delta signal!!
  sTable.io.w.req.bits.data(0).signature := makeSign(s2_oldSignature,strideMap(s2_newDelta))
  //sTable.io.w.req.bits.data(0).signature := get_predicted_sig(s2_oldSignature,s2_newDelta)
  sTable.io.w.req.bits.data(0).lastBlockOff := s2_newBlkAddr

  // val resp_delta = Mux(s2_req.isBP, s2_probeDelta, s2_newDelta)
  val resp_delta = s2_newDelta

  // send response to paternTable
  io.resp.valid := resp_delta =/= 0.S && s2_hit && s2_valid
  io.resp.bits.delta  :=resp_delta
  io.resp.bits.source := s2_req.source
  io.resp.bits.needT := s2_req.needT
  io.resp.bits.isBP := s2_req.isBP
  when(s2_bp_hit){
    io.resp.bits.signature := s2_bp_matched_sig
    io.resp.bits.block := s2_bp_blkAddr
  }.otherwise {
    io.resp.bits.signature := s2_oldSignature
    io.resp.bits.block := s2_newBlkAddr
  }
  io.req.ready := true.B

  XSPerfAccumulate("spp_st_req_nums",io.resp.valid)
  XSPerfAccumulate("spp_st_reqfire_nums",io.resp.fire)
  XSPerfAccumulate("spp_st_bp_req", s2_valid && s2_bp_hit)
  XSPerfAccumulate("spp_st_bp_update",io.s0_bp_update.valid)
}

class PatternTable(parentName:String="Unkown")(implicit p: Parameters) extends SPPModule {
  val io = IO(new Bundle {
    val req = Flipped(DecoupledIO(new SignatureTableResp))
    val resp = DecoupledIO(new PatternTableResp)
    val from_ghr = (new Bundle {
        val deadCov_state = Input(UInt(PfcovState.bits.W))
        val hitAcc_state = Input(UInt(PfaccState.bits.W))
        val global_queue_used = Input((UInt(6.W)))
    })
    val pt2st_bp = ValidIO(new BreakPointReq)
  })

  def get_idx(addr:      UInt) = addr(log2Up(pTableEntries) - 1, 0)
  def get_tag(addr:      UInt) = addr(signatureBits - 1, log2Up(pTableEntries))
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

  // val q = Module(new Queue(chiselTypeOf(io.req.bits), pTableQueueEntries, flow = true, pipe = false))
  val q = Module(new ReplaceableQueueV2(chiselTypeOf(io.req.bits), pTableQueueEntries))
  q.io.enq <> io.req
  val issueReq = RegInit(0.U.asTypeOf(new SignatureTableResp))
  when(q.io.deq.valid){
    issueReq := q.io.deq.bits
  }
  val s_idle :: s_lookahead0 :: s_updateTable :: s_lookahead :: Nil = Enum(4)
  val state = RegInit(s_idle)
  q.io.deq.ready := state === s_idle || state === s_updateTable
  val enprefetch = WireInit(false.B)
  val enprefetchnl = WireInit(false.B)

  //read pTable
  // --------------------------------------------------------------------------------
  // stage 0
  // -------------------------------------------------------------------------------
  //1. calculate sram rindex and send read  sram Table requrest
  // when state == s_lookahead 
    //2. when lookcount bigger than signature folding length , start bp update operation
    //3. caculate s0_miniCount, miniCount has been designed 3 strategies for determing need to start next lookahead round
      //-1 slowLookTable(s0_lookCount), use slowLook , relatively conservative query
      //-2 s0_lookCount,  medium level
      //-3 s0_lookCOunt >> 2, very aggressive
      //-4 Mux(q.io.empty, slowLookTable(s0_lookCount), s0_lookCount) ,considering receive queue used situation
    //4. calculate s0_current new data entry
  val s1_first_flag = WireInit(false.B)
  val s1_continue = WireInit(false.B)
  val s1_readResult = WireInit(0.U.asTypeOf(new pTableEntry))
  val s1_maxEntry = WireInit(0.U.asTypeOf(new DeltaEntry))
  val s1_current = WireInit(0.U.asTypeOf(new SignatureTableResp));dontTouch(s1_current)
  val s1_valid = WireInit(false.B)
  val s1_testOffset = WireInit(0.U((pageAddrBits + blkOffsetBits).W))
  val s1_lookCount = WireInit(0.U(lookCountBits.W))

  val s0_first_flag = RegInit(false.B)
  val s0_valid = WireInit((state === s_lookahead0 && q.io.deq.valid) || state === s_lookahead0 || (state === s_lookahead &&  (s0_first_flag || ~s1_valid)))
  val s0_current = WireInit(0.U.asTypeOf(new SignatureTableResp));dontTouch(s0_current)
  val s0_lookCount = WireInit(0.U(lookCountBits.W))
  //| signature | delta | block |

  when(s0_valid && state === s_lookahead){
    s0_lookCount := s1_lookCount + 1.U
  }.elsewhen(state === s_idle){
    s0_lookCount := 0.U
  }.otherwise{
    s0_lookCount := s1_lookCount
  }

  when(state === s_lookahead0){
    s0_first_flag := true.B
  }.elsewhen(state === s_lookahead){
    s0_first_flag := false.B
  }

  //forward hold dequeue data
  when(state === s_lookahead){
    s0_current.signature := makeSign(s1_current.signature,strideMap(s1_maxEntry.delta))
  }.otherwise{
    s0_current.signature := issueReq.signature
  }

  when(state === s_lookahead && !s1_first_flag){
    s0_current.delta := s1_maxEntry.delta
    s0_current.block := s1_testOffset //TODO: need opimize?
    s0_current.isBP := false.B
  }.elsewhen(state === s_idle){
    s0_current := q.io.deq.bits
  }.otherwise{
    s0_current := issueReq
  }

  val s0_bp_update = WireInit(s0_lookCount >= 3.U && s0_valid)
  io.pt2st_bp.valid := ENABLE_BP.asBool &&  s0_bp_update
  io.pt2st_bp.bits.blkAddr := s0_current.block
  io.pt2st_bp.bits.parent_sig(0) := s0_current.signature

  def slowLookTable(lc: UInt): UInt = {
    Mux(lc >= 1.U && lc <= 4.U, (lc >> 1.U) + 1.U, lc)
  }
  //TODO: need to be optimized !!! some error here
  // val s0_miniCount = slowLookTable(s0_lookCount) // test1
  // val s0_miniCount = s0_lookCount // test2
  val s0_miniCount = Mux(q.io.empty, slowLookTable(s0_lookCount), s0_lookCount) // test3

  pTable.io.r.req.valid := q.io.deq.fire || (s0_valid && state === s_lookahead)
  pTable.io.r.req.bits.setIdx := get_idx(s0_current.signature)
  // --------------------------------------------------------------------------------
  // stage 1
  // -------------------------------------------------------------------------------
  //1. calculate value for next update
  //2. calculate lookcount when sram read finished
  s1_valid := RegNext(s0_valid ,false.B)
  s1_first_flag := RegNext(s0_first_flag,false.B)
  s1_lookCount := RegNext(s0_lookCount,0.U)
  s1_current := RegEnable(s0_current,s0_valid)


  //directly calculate from sram 
  s1_readResult := pTable.io.r.resp.data(0)
  s1_maxEntry := s1_readResult.deltaEntries.reduce((a, b) => Mux(a.cDelta >= b.cDelta, a, b))
  //set output
  val s1_delta_list = s1_readResult.deltaEntries.map(x => Mux(x.cDelta > s0_miniCount.asUInt, x.delta, 0.S))
  val s1_delta_list_checked = s1_delta_list.map(x =>
    Mux((s1_current.block.asSInt + x).asUInt(pageAddrBits + blkOffsetBits - 1, blkOffsetBits) === s1_current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits),
      x, 0.S))
  val s1_hit = WireInit(s1_readResult.valid && get_tag(s1_current.signature) === s1_readResult.tag)

  val s1_count = WireInit(0.U(4.W));dontTouch(s1_count)
  val s1_exist = s1_readResult.deltaEntries.map(_.delta === s1_current.delta).reduce(_ || _)
  val s1_temp = s1_readResult.deltaEntries.map(x => Mux(x.delta === s1_current.delta, (new DeltaEntry).apply(s1_current.delta, x.cDelta + 1.U), x))
  val s1_smallest: SInt = s1_readResult.deltaEntries.reduce((a, b) => Mux(a.cDelta < b.cDelta, a, b)).delta
  val s1_replaceIdx: UInt = s1_readResult.deltaEntries.indexWhere(a => a.delta === s1_smallest)
  //predict
  val s1_issued = s1_delta_list_checked.map(a => Mux(a =/= 0.S, 1.U, 0.U)).reduce(_ +& _)
  s1_testOffset := Mux(s1_issued =/= 0.U,(s1_current.block.asSInt + s1_maxEntry.delta).asUInt,s1_current.block)
  // val s1_testOffset = (current.block.asSInt + maxEntry.delta).asUInt
  //same page?
  val s1_samePage = (s1_testOffset(pageAddrBits + blkOffsetBits - 1, blkOffsetBits) === s1_current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits))

  // enable prefetch
  enprefetch :=  !s0_first_flag && s1_valid && s1_hit && s1_issued =/= 0.U && state === s_lookahead && s1_samePage
  // enable nextline when
  val s1_delta_list_nl = s1_delta_list.map(_ => 1.S((blkOffsetBits + 1).W))

  when(!s0_valid && s1_valid && s1_lookCount === 1.U && state === s_lookahead && !enprefetch) {
    val s1_testOffset = s1_current.block + 1.U
    when(s1_testOffset(pageAddrBits + blkOffsetBits - 1, blkOffsetBits) === s1_current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits)) {
      enprefetchnl := ENABLE_NL.B
    }
  }
  s1_first_flag := s1_lookCount === 1.U
  s1_continue := enprefetch && (s1_maxEntry.cDelta > s0_miniCount)
  // --------------------------------------------------------------------------------
  // update paternTable
  // --------------------------------------------------------------------------------
  //write pTable
  //hold needed write sig when fisrt read sram index
  //1. when leave lookahead0,hold needed writing data
  val s1_wdeltaEntries = WireInit(VecInit(Seq.fill(pTableDeltaEntries)(0.U.asTypeOf(new DeltaEntry()))))
  when(s1_hit) {
    when(s1_exist) {
      //counter overflow --- only considering count overflow
      when(s1_readResult.count + 1.U === ((1.U << s1_count.getWidth).asUInt - 1.U)) {
        s1_wdeltaEntries := s1_temp.map(x => (new DeltaEntry).apply(x.delta, x.cDelta >> 1.asUInt))
      } .otherwise {
        s1_wdeltaEntries := s1_temp
      }
    } .otherwise {
      //to do replacement
      s1_wdeltaEntries := VecInit.tabulate(s1_readResult.deltaEntries.length) { i =>
        Mux((i.U === s1_replaceIdx), (new DeltaEntry).apply(s1_current.delta, 1.U), s1_readResult.deltaEntries(i))
      }
    }
    s1_count := s1_wdeltaEntries.map(_.cDelta).reduce(_ + _) //todo: must be optimized!
    //to consider saturate here
  } .otherwise {
    s1_wdeltaEntries(0).delta := issueReq.delta
    s1_wdeltaEntries(0).cDelta := 1.U
    s1_count := 1.U
  }
  val write_hold = state === s_lookahead0
  pTable.io.w.req.valid := state === s_updateTable //&& !issueReq.isBP
  pTable.io.w.req.bits.setIdx := RegEnable(get_idx(s0_current.signature),write_hold)
  pTable.io.w.req.bits.data(0).valid := true.B
  pTable.io.w.req.bits.data(0).deltaEntries := RegEnable(s1_wdeltaEntries,write_hold)
  pTable.io.w.req.bits.data(0).count := RegEnable(s1_count,write_hold)
  pTable.io.w.req.bits.data(0).tag := RegEnable(get_tag(s1_current.signature),write_hold)


  //FSM
  switch(state) {
    is(s_idle) {
      when(q.io.deq.valid) {
        state := s_lookahead0
      }
    }
    is(s_lookahead0) {
      when(s0_valid){
        state := s_lookahead
      }
    }
    is(s_lookahead) {
        when(!s0_first_flag && s1_valid && !enprefetch) {
            state := s_updateTable
        }.otherwise{
            state := s_lookahead
        }
    }
    is(s_updateTable) {
        state := s_idle
    }
  }
  // output
  io.resp.valid := enprefetch || enprefetchnl
  io.resp.bits.block := s1_current.block
  when(enprefetchnl) {
    io.resp.bits.deltas := s1_delta_list_nl
  }.otherwise{
    io.resp.bits.deltas := s1_delta_list_checked
  }
  io.resp.bits.degree := s1_lookCount
  io.resp.bits.source := s1_current.source
  io.resp.bits.needT := s1_current.needT

  //perf
  XSPerfAccumulate("spp_pt_bp_nums",io.pt2st_bp.valid)
  XSPerfAccumulate("spp_pt_lookahead2",state === s_lookahead && s1_valid && s1_continue)
  XSPerfAccumulate("spp_pt_nextLine",state === s_lookahead && enprefetchnl)
  XSPerfAccumulate("spp_pt_cross_page",state === s_lookahead && s1_valid && s1_samePage)
//  XSPerfAccumulate(s"spp_pt_do_nextline", enprefetchnl)
//  for (i <- 0 until pTableEntries) {
//    XSPerfAccumulate(s"spp_pt_touched_entry_onlyset_${i.toString}", pTable.io.r.req.bits.setIdx === i.U(log2Up(pTableEntries).W)
//    )
//  }
}

//Can add eviction notify or cycle counter for each entry
class Unpack(implicit p: Parameters) extends SPPModule {
  val io = IO(new Bundle {
    val req = Flipped(DecoupledIO(new PatternTableResp))
    val resp = ValidIO(new UnpackResp)
  })

  def get_idx(addr:      UInt) = addr(log2Up(fTableEntries) - 1, 0)
  def get_tag(addr:      UInt) = addr(fullAddressBits - offsetBits - 1, log2Up(fTableEntries))

  def fTableEntry() = new Bundle {
    val valid = Bool()
    val tag = UInt(fTagBits.W)
  }
  val fTable = RegInit(VecInit(Seq.fill(fTableEntries)(0.U.asTypeOf(fTableEntry()))))

  val inProcess = RegInit(false.B)
  val endeq = WireInit(false.B)

  val q = Module(new ReplaceableQueueV2(chiselTypeOf(io.req.bits), pTableQueueEntries))
  // val q = Module(new Queue(chiselTypeOf(io.req.bits), unpackQueueEntries,flow = true, pipe = false))
  q.io.enq <> io.req //change logic to replace the tail entry
  val req= RegInit(0.U.asTypeOf(new PatternTableResp))
  when(q.io.deq.fire){
    req := q.io.deq.bits
  }

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
  readResult := fTable(get_idx(prefetchBlock))
  hit := readResult.valid && get_tag(prefetchBlock) === readResult.tag

  when(enresp && !hit) {
    fTable(get_idx(prefetchBlock)).valid := true.B
    fTable(get_idx(prefetchBlock)).tag := get_tag(prefetchBlock)
  }

  io.resp.valid := enresp && !hit
  io.resp.bits.prefetchBlock := prefetchBlock
  io.resp.bits.degree := req.degree
  io.resp.bits.source := req.source
  io.resp.bits.needT := req.needT

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
 XSPerfAccumulate("spp_filter_recv", io.req.valid)
 XSPerfAccumulate("spp_filter_nums", q.io.deq.fire && hit)
 XSPerfAccumulate("spp_filter_req", io.resp.valid)
//  for (off <- (-63 until 64 by 1).toList) {
//    if (off < 0) {
//      XSPerfAccumulate("spp_pt_pfDelta_neg_" + (-off).toString, hit && extract_delta === off.S((blkOffsetBits + 1).W))
//    } else {
//      XSPerfAccumulate("spp_pt_pfDelta_pos_" + off.toString, hit && extract_delta === off.S((blkOffsetBits + 1).W))
//    }
//  }
}

class SignaturePathPrefetch(parentName:String="Unkown")(implicit p: Parameters) extends SPPModule {
  val io = IO(new Bundle() {
    val train = Flipped(DecoupledIO(new PrefetchTrain)) //train from mshr ,now recommand using MISS
    val req = DecoupledIO(new PrefetchReq) //issue to current or next-level cache
    val hint_req = DecoupledIO(new PrefetchReq)
    val resp = Flipped(DecoupledIO(new PrefetchResp)) //fill request from the next-level cache, using this to update filter
    val db_degree = Flipped(ValidIO(UInt(2.W)))
    val queue_used = Input(UInt(6.W))
    val from_ghr = Flipped(ValidIO(new Bundle {
        val deadCov_state = UInt(PfcovState.bits.W)
        val hitAcc_state = UInt(PfaccState.bits.W)
        val shareBO = SInt(6.W)
        val global_queue_used = (UInt(6.W))
    }))
  })
  println(s"pageAddrBits: ${pageAddrBits}")
  println(s"blkAddrBits: ${pageAddrBits}")
  println(s"log2Up(sTableEntries): ${log2Up(sTableEntries)}")
  println(s"fullAddressBits: ${fullAddressBits}")
  println(s"pageOffsetBits: ${pageOffsetBits}")
  println(s"sTagBits: ${sTagBits}")
  println(s"stableEntries: ${sTableEntries}")
  println(s"ptableEntries: ${pTableEntries}")
  println(s"pTagBits: ${pTagBits}")

  val sTable = Module(new SignatureTable(parentName + "stable_"))
  val pTable = Module(new PatternTable(parentName + "ptable_"))
  val unpack = Module(new Unpack)

  val oldAddr = io.train.bits.addr //received request from L1 cache
  val pageAddr = getPPN(oldAddr)
  val blkOffset = oldAddr(pageOffsetBits - 1, offsetBits)

  // might be lack of prefetch requests
  io.train.ready := sTable.io.req.ready

  sTable.io.req.valid := io.train.valid
  sTable.io.req.bits.blkAddr := io.train.bits.blkAddr
  sTable.io.req.bits.needT := false.B//io.train.bits.needT
  sTable.io.req.bits.source := 0.U //io.train.bits.source
  sTable.io.req.bits.isBP := false.B//io.train.bits.state === AccessState.PREFETCH_HIT
  sTable.io.req.bits.fromGHR_shareBO := io.from_ghr.bits.shareBO

  pTable.io.req <> sTable.io.resp //to detail
  pTable.io.pt2st_bp := DontCare
  pTable.io.pt2st_bp <> sTable.io.s0_bp_update
  pTable.io.resp <> unpack.io.req

  val newAddr = Cat(unpack.io.resp.bits.prefetchBlock, 0.U(offsetBits.W))
  val ghr_deadCov_state = RegEnable(io.from_ghr.bits.deadCov_state, 1.U, io.from_ghr.valid)
  val ghr_hitAcc_state = RegEnable(io.from_ghr.bits.hitAcc_state, 1.U, io.from_ghr.valid)
  val send2Llc = WireInit(false.B)
  send2Llc := unpack.io.resp.bits.degree > 1.U && (io.from_ghr.bits.global_queue_used >= 24.U || ghr_deadCov_state > PfcovState.p_25)

  pTable.io.from_ghr.deadCov_state := ghr_deadCov_state
  pTable.io.from_ghr.hitAcc_state := ghr_hitAcc_state
  pTable.io.from_ghr.global_queue_used := io.from_ghr.bits.global_queue_used

  io.req.valid := unpack.io.resp.valid
  io.req.bits.tag := parseFullAddress(newAddr)._1
  io.req.bits.set := parseFullAddress(newAddr)._2
  io.req.bits.needT := unpack.io.resp.bits.needT
  io.req.bits.source := unpack.io.resp.bits.source
  io.req.bits.pfVec := PfSource.SPP
  //hint req 
  io.hint_req.valid := unpack.io.resp.valid && send2Llc
  io.hint_req.bits := io.req.bits 


  io.resp.ready := true.B
  //perf
  XSPerfAccumulate( "spp_recv_train", io.train.valid)
  XSPerfAccumulate( "spp_recv_st", sTable.io.resp.valid)
  XSPerfAccumulate( "spp_recv_pt", Mux(pTable.io.resp.valid, pTable.io.resp.bits.deltas.map(a => Mux(a =/= 0.S, 1.U, 0.U)).reduce(_ +& _), 0.U))
  XSPerfAccumulate( "spp_hintReq", io.hint_req.valid)
}