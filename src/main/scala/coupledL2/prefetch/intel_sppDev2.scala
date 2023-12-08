package coupledL2.prefetch

import org.chipsalliance.cde.config.Parameters
import chisel3._
import chisel3.util._
import xs.utils.sram.SRAMTemplate
import xs.utils.Pipeline

import coupledL2.{HasCoupledL2Parameters,L2ParamKey}
import xs.utils.perf.HasPerfLogging
import coupledL2.prefetch.{PrefetchParameters,PrefetchTrain,PrefetchReq,PrefetchResp,PrefetchEvict}
import coupledL2.prefetch.{BestOffsetPrefetch,BOPParameters,PrefetchReceiver,PrefetchReceiverParams}
import xs.utils.SRAMQueue
import xs.utils.OneHot
import xs.utils.HighestBit
import xs.utils.ParallelPriorityMux

object PfSource extends Enumeration {
  val bits = 3
  val NONE    = "b000".U(bits.W)
  val BOP     = "b001".U(bits.W)
  val SPP     = "b010".U(bits.W)
  val SMS     = "b100".U(bits.W)
  val BOP_SPP = "b011".U(bits.W)

}
object PfVectorConst extends {
  val BOP = 0
  val SPP = 1
  val SMS = 2

  val bits = 3
  val DEFAULT = 0.U(bits.W)
}

object PfcovState {
  val bits = 2

  def p_0     = 0.U(bits.W)
  def p_25    = 1.U(bits.W)
  def p_50    = 2.U(bits.W)
  def p_75    = 3.U(bits.W)
}

object PfaccState {
  val bits = 2

  def p_0     = 0.U(bits.W)
  def p_25    = 1.U(bits.W)
  def p_50    = 2.U(bits.W)
  def p_75    = 3.U(bits.W)
}

object EnqIOV2 {
  def apply[T <: Data](gen: T): DecoupledIO[T] = Decoupled(gen)
}

/** Consumer - drives (outputs) ready, inputs valid and bits.
  * @param gen The type of data to dequeue
  */
object DeqIOV2 {
  def apply[T <: Data](gen: T): DecoupledIO[T] = Flipped(Decoupled(gen))
}

/** An I/O Bundle for Queues
  * @param gen The type of data to queue
  * @param entries The max number of entries in the queue.
  * @param hasFlush A boolean for whether the generated Queue is flushable
  * @groupdesc Signals The hardware fields of the Bundle
  */
class QueueIOV2[T <: Data](
  private val gen: T,
  val entries:     Int)
    extends Bundle { 
  /** I/O to enqueue data (client is producer, and Queue object is consumer), is [[chisel3.util.DecoupledIO]] flipped.
    * @group Signals
    */
  val enq = Flipped(EnqIOV2(gen))

  /** I/O to dequeue data (client is consumer and Queue object is producer), is [[chisel3.util.DecoupledIO]]
    * @group Signals
    */
  val deq = Flipped(DeqIOV2(gen))

  val empty = Output(Bool())
  val full = Output(Bool())
}

/** A hardware module implementing a Queue
  * @param gen The type of data to queue
  * @param entries The max number of entries in the queue
  * @param pipe True if a single entry queue can run at full throughput (like a pipeline). The ''ready'' signals are
  * combinationally coupled.
  * @param flow True if the inputs can be consumed on the same cycle (the inputs "flow" through the queue immediately).
  * The ''valid'' signals are coupled.
  * @param useSyncReadMem True uses SyncReadMem instead of Mem as an internal memory element.
  * @param hasFlush True if generated queue requires a flush feature
  * @example {{{
  * val q = Module(new Queue(UInt(), 16))
  * q.io.enq <> producer.io.out
  * consumer.io.in <> q.io.deq
  * }}}
  */
class ReplaceableQueueV2[T <: Data](
  val gen:            T,
  val entries:        Int) extends Module()
{
  val io = IO(new QueueIOV2(gen, entries))
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

  io.enq.ready := true.B
  io.deq.valid := !empty || io.enq.valid
  io.deq.bits := Mux(empty, io.enq.bits, queue(head))

  //XSPerfHistogram(cacheParams, "nrWorkingPfQueueEntries", 
  //  PopCount(valids), true.B, 0, inflightEntries, 1)
}


case class SPPParameters(
  sTableEntries: Int = 256,
  pTableEntries: Int = 512,
  pTableDeltaEntries: Int = 4,
  pTableQueueEntries: Int = 4,
  signatureBits: Int = 12,
  unpackQueueEntries: Int = 4,
  fTableEntries: Int = 32
)
    extends PrefetchParameters {
  override val hasPrefetchBit:  Boolean = true
  override val inflightEntries: Int = 32
}

trait HasSPPParams extends HasCoupledL2Parameters {
  val sppParams = SPPParameters()

  val sTableEntries = sppParams.sTableEntries
  val pTableEntries = sppParams.pTableEntries
  val inflightEntries = sppParams.inflightEntries
  val pTableDeltaEntries = sppParams.pTableDeltaEntries
  val signatureBits = sppParams.signatureBits
  val pTableQueueEntries = sppParams.pTableQueueEntries
  val unpackQueueEntries = sppParams.unpackQueueEntries
  val fTableEntries = sppParams.fTableEntries
  val lookCountBits = 6

  val pageAddrBits = fullAddressBits - pageOffsetBits
  val blkOffsetBits = pageOffsetBits - offsetBits
  val sTagBits = pageAddrBits - log2Up(sTableEntries)
  val pTagBits = signatureBits - log2Up(pTableEntries)
  val fTagBits = pageAddrBits - log2Up(fTableEntries)
  def makeSign(old_sig:UInt,new_delta:SInt)=(old_sig << 3) ^ new_delta.asUInt

  val ENABLE_BP = false
  val ENABLE_NL = true
}

abstract class SPPBundle(implicit val p: Parameters) extends Bundle with HasSPPParams
abstract class SPPModule(implicit val p: Parameters) extends Module with HasSPPParams with HasPerfLogging

class SignatureTableReq(implicit p: Parameters) extends SPPBundle {
  val pageAddr = UInt(pageAddrBits.W)
  val blkOffset = UInt(blkOffsetBits.W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
  def get_blkAddr = Cat(pageAddr,blkOffset)
  def get_accessAddr = Cat(pageAddr,blkOffset,0.U(offsetBits.W))
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
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
}

class PatternTableResp(implicit p: Parameters) extends SPPBundle {
  val deltas = Vec(pTableDeltaEntries, SInt((blkOffsetBits + 1).W))
  val block = UInt((pageAddrBits + blkOffsetBits).W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
}

class UnpackResp(implicit p: Parameters) extends SPPBundle {
  val prefetchBlock = UInt((pageAddrBits + blkOffsetBits).W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
}

class DeltaEntry(implicit p: Parameters) extends SPPBundle {
  val delta = SInt((blkOffsetBits + 1).W)
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
    val resp = DecoupledIO(new SignatureTableResp) //output old signature and delta to write PT
  })
  def hash1(addr:    UInt) = addr(log2Up(sTableEntries) - 1, 0)
  def hash2(addr:    UInt) = addr(2 * log2Up(sTableEntries) - 1, log2Up(sTableEntries))
  def get_idx(addr:      UInt) = hash1(addr) ^ hash2(addr)
  def get_tag(addr:      UInt) = addr(pageAddrBits - 1, log2Up(sTableEntries))
  def sTableEntry() = new Bundle {
    val valid = Bool()
    val tag = UInt(sTagBits.W)
    val signature = UInt(signatureBits.W)
    val lastBlock = UInt(blkOffsetBits.W)
  }

  println(s"fullAddressBits: ${fullAddressBits}")
  println(s"pageOffsetBits: ${pageOffsetBits}")
  println(s"sTagBits: ${sTagBits}")
  
  val sTable = Module(
    new SRAMTemplate(sTableEntry(), set = sTableEntries, way = 1, 
      bypassWrite = true, 
      shouldReset = true, 
      hasMbist = cacheParams.hasMbist, 
      hasShareBus = cacheParams.hasShareBus,
      hasClkGate = enableClockGate, 
      parentName = parentName
    ))
  // --------------------------------------------------------------------------------
  // stage 0
  // --------------------------------------------------------------------------------
  //1. read sTable
  //2. write bpTable
  val s0_valid =  WireInit(false.B);dontTouch(s0_valid)
  val s0_req =  WireInit(0.U.asTypeOf(new SignatureTableReq))
  s0_valid := io.req.fire
  s0_req := io.req.bits
  sTable.io.r.req.valid       := s0_valid
  sTable.io.r.req.bits.setIdx := get_idx(s0_req.pageAddr)
  val s0_bp_hit = WireInit(false.B)
  val s0_bp_prePredicted_blkOff = WireInit(0.U(blkOffsetBits.W))
  //TODO: there should set offset for matchedIndex?
  // val s0_bp_matchedIdx = WireInit()
  val s0_bp_matched_sig = WireInit(0.U(signatureBits.W))
  // --------------------------------------------------------------------------------
  // stage 2
  // --------------------------------------------------------------------------------
  //1. update sTable & req pTable
    //- we should write  biggest_blkAddr for solving spp timely problems, let spp prefetching farther!!!
  //2. delta BP from filterTable
    // redirect accessed blockAddr when use bp
    // calculate probeDelta for avoiding biased train signal delta, not make origin good signature overrided
    // calculate probe delata
  val s1_valid        = RegNext(s0_valid,false.B);dontTouch(s1_valid)
  val s1_req          = RegEnable(s0_req,0.U.asTypeOf(new SignatureTableReq),s0_valid);dontTouch(s1_req)
  val s1_entryData    = WireInit(0.U.asTypeOf(sTableEntry()));dontTouch(s1_entryData)
  val s1_hit          = WireInit(false.B);dontTouch(s1_hit)
  val s1_newDelta     = WireInit(Mux(s1_hit, s1_req.blkOffset.asSInt - s1_entryData.lastBlock.asSInt, s1_req.blkOffset.asSInt))
  val s1_oldSignature = WireInit(Mux(s1_hit, s1_entryData.signature, 0.U))
  val s1_newBlkAddr  = s1_req.get_blkAddr

  when(s1_valid){
    s1_hit := s1_entryData.tag === get_tag(s1_req.pageAddr)
    s1_entryData := sTable.io.r.resp.data(0)
  }.otherwise{
    s1_hit := false.B
    s1_entryData := 0.U.asTypeOf(sTableEntry())
  }
  
  //bp
  val s1_bp_hit = RegEnable(s0_bp_hit,false.B,s1_valid)
  val s1_bp_matched_sig = RegEnable(s0_bp_matched_sig,0.U(signatureBits.W),s1_valid)
  val s1_bp_prePredicted_blkOff = RegEnable(s0_bp_prePredicted_blkOff,0.U(blkOffsetBits.W),s1_valid)

  sTable.io.w.req.valid := s1_valid && s1_newDelta =/= 0.S
  sTable.io.w.req.bits.setIdx := get_idx(s1_req.pageAddr)
  sTable.io.w.req.bits.data(0).valid := true.B
  sTable.io.w.req.bits.data(0).tag := get_tag(s1_req.pageAddr)
  //TODO: there should hold strideMap-> delta signal!! fuck!!!
  //TODO: there should hold origin delta signal!!
  // sTable.io.w.req.bits.data(0).signature := makeSign(s1_oldSignature,strideMap(s1_newDelta))
  sTable.io.w.req.bits.data(0).signature := makeSign(s1_oldSignature,s1_newDelta)
  sTable.io.w.req.bits.data(0).lastBlock := s1_newBlkAddr

  // send response to paternTable
  io.resp.valid := s1_newDelta =/= 0.S && s1_hit && s1_valid
  io.resp.bits.delta  :=s1_newDelta
  io.resp.bits.source := s1_req.source
  io.resp.bits.needT := s1_req.needT
  // io.resp.bits.isBP := s1_req.isBP
  when(s1_bp_hit){
    io.resp.bits.signature := s1_bp_matched_sig
    io.resp.bits.block := (s1_newBlkAddr) + s1_bp_prePredicted_blkOff
  }.otherwise {
    io.resp.bits.signature := s1_oldSignature
    io.resp.bits.block := s1_newBlkAddr
  }
  io.req.ready := sTable.io.r.req.ready
  XSPerfAccumulate("spp_st_req_nums",io.resp.valid)
  XSPerfAccumulate("spp_st_reqfire_nums",io.resp.fire)
  // XSPerfAccumulate("spp_st_bp_req", s1_valid && s1_bp_hit)
  // XSPerfAccumulate("spp_st_bp_update",io.s0_bp_update.valid)
}

// class PatternTable(implicit p: Parameters) extends SPPModule {
//   val io = IO(new Bundle {
//     val req = Flipped(DecoupledIO(new SignatureTableResp))
//     val resp = DecoupledIO(new PatternTableResp)
//   })  

//   def pTableEntry() = new Bundle {
//     val valid = Bool()
//     //val deltaEntries = VecInit(Seq.fill(pTableDeltaEntries)((new DeltaEntry).apply(0.S, 0.U)))
//     val deltaEntries = Vec(pTableDeltaEntries, new DeltaEntry())
//     val count = UInt(4.W)
//   }

//   def slowLookTable(lc: UInt): UInt = {
//     Mux(lc >= 1.U && lc <= 4.U, (lc >> 1.U) + 1.U, lc)
//   }

//   val pTable = Module(
//     new SRAMTemplate(pTableEntry(), set = pTableEntries, way = 1, bypassWrite = true, shouldReset = true)
//   )

//   val q = Module(new ReplaceableQueueV2(chiselTypeOf(io.req.bits), pTableQueueEntries))
//   q.io.enq <> io.req
//   val req = q.io.deq.bits

//   val s_idle :: s_lookahead0 :: s_lookahead :: Nil = Enum(3)
//   val state = RegInit(s_idle)
//   val s1_result = Wire(pTableEntry())
//   val readSignature = WireInit(0.U(signatureBits.W)) //to differentiate the result from io or lookahead, set based on state
//   val readDelta = WireInit(0.S((blkOffsetBits + 1).W))
//   val lastSignature = Wire(UInt(signatureBits.W))
//   val lastDelta = Wire(SInt((blkOffsetBits + 1).W))
//   val hit = WireInit(false.B)
//   val enread = WireInit(false.B)
//   val enprefetch = WireInit(false.B)
//   val enprefetchnl = WireInit(false.B)
//   val enwrite = RegNext(q.io.deq.fire && pTable.io.r.req.fire) //we only modify-write on demand requests
//   val current = Reg(new SignatureTableResp) // RegInit(0.U.asTypeOf(new PatternTableResp))
//   val lookCount = RegInit(0.U(6.W))
//   val miniCount = Mux(q.io.empty, slowLookTable(lookCount), lookCount)
//   // val miniCount = slowLookTable(lookCount)

//   //read pTable
//   pTable.io.r.req.valid := enread
//   pTable.io.r.req.bits.setIdx := readSignature
//   s1_result := pTable.io.r.resp.data(0)
//   hit := s1_result.valid
//   lastSignature := RegNext(readSignature)
//   lastDelta := RegNext(readDelta)
//   //set output
//   val maxEntry = s1_result.deltaEntries.reduce((a, b) => Mux(a.cDelta >= b.cDelta, a, b))
//   val delta_list = s1_result.deltaEntries.map(x => Mux(x.cDelta > miniCount, x.delta, 0.S))
//   val delta_list_checked = delta_list.map(x => 
//             Mux((current.block.asSInt + x).asUInt(pageAddrBits + blkOffsetBits - 1, blkOffsetBits)
//             === current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits), x, 0.S))
//   val delta_list_nl = delta_list.map(_ => 1.S((blkOffsetBits + 1).W))

//   io.resp.valid := enprefetch || enprefetchnl
//   io.resp.bits.block := current.block
//   io.resp.bits.deltas := delta_list_checked
//   io.resp.bits.needT := current.needT
//   io.resp.bits.source := current.source
//   when(enprefetchnl) {
//     io.resp.bits.deltas := delta_list_nl
//   }

//   //modify table
//   val deltaEntries = Wire(Vec(pTableDeltaEntries, new DeltaEntry()))
//   val count = Wire(UInt(4.W))
//   when(hit) {
//     val exist = s1_result.deltaEntries.map(_.delta === lastDelta).reduce(_ || _)
//     when(exist) {
//       val temp = s1_result.deltaEntries.map(x =>
//         Mux(x.delta === lastDelta, (new DeltaEntry).apply(lastDelta, x.cDelta + 1.U), x)) 
//       //counter overflow
//       when(s1_result.count + 1.U === ((1.U << count.getWidth) - 1.U)) {
//         deltaEntries := temp.map(x => (new DeltaEntry).apply(x.delta, x.cDelta >> 1.U))
//       } .otherwise {
//         deltaEntries := temp
//       }
//       count := deltaEntries.map(_.cDelta).reduce(_ + _)
//     } .otherwise {
//       //to do replacement
//       val smallest: SInt = s1_result.deltaEntries.reduce((a, b) => {
//         Mux(a.cDelta < b.cDelta, a, b)
//       }).delta
//       val indexToReplace : UInt = s1_result.deltaEntries.indexWhere(a => a.delta === smallest)
//       deltaEntries := VecInit.tabulate(s1_result.deltaEntries.length) { i =>
//         Mux((i.U === indexToReplace), (new DeltaEntry).apply(lastDelta, 1.U), 
//         s1_result.deltaEntries(i))
//       }
//       count := deltaEntries.map(_.cDelta).reduce(_ + _)
//     }
//     //to consider saturate here
//   } .otherwise {
//     deltaEntries := VecInit(Seq.fill(pTableDeltaEntries)((new DeltaEntry).apply(0.S, 0.U)))
//     deltaEntries(0).delta := lastDelta
//     deltaEntries(0).cDelta := 1.U
//     count := 1.U
//   }
//   //write pTable
//   pTable.io.w.req.valid := enwrite
//   pTable.io.w.req.bits.setIdx := lastSignature
//   pTable.io.w.req.bits.data(0).valid := true.B
//   pTable.io.w.req.bits.data(0).deltaEntries := deltaEntries
//   pTable.io.w.req.bits.data(0).count := count
  
//   //FSM
//   switch(state) {
//     is(s_idle) {
//       when(q.io.deq.fire) {
//         readSignature := req.signature
//         readDelta := req.delta
//         state := s_lookahead0
//         current := req
//         enread := true.B
//       }
//     }
//     is(s_lookahead0) {
//       enread := true.B
//       readSignature := (lastSignature << 3) ^ lastDelta.asUInt
//       state := s_lookahead
//     }
//     is(s_lookahead) {
//       when(hit) {
//         val issued = delta_list_checked.map(a => Mux(a =/= 0.S, 1.U, 0.U)).reduce(_ +& _)
//         when(issued =/= 0.U) {
//           enprefetch := true.B
//           val testOffset = (current.block.asSInt + maxEntry.delta).asUInt
//           //same page?
//           when(testOffset(pageAddrBits + blkOffsetBits - 1, blkOffsetBits) === 
//             current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits)
//             && maxEntry.cDelta > miniCount) {
//             lookCount := lookCount + 1.U
//             readSignature := (lastSignature << 3) ^ maxEntry.delta.asUInt
//             current.block := testOffset
//             enread := true.B
//           } .otherwise {
//             lookCount := 0.U
//             state := s_idle
//           }
//         }.otherwise {
//           lookCount := 0.U
//           state := s_idle
//         } 
//       } .otherwise {
//         when(lookCount <= 1.U) {
//           val testOffset = current.block + 1.U
//           when(testOffset(pageAddrBits + blkOffsetBits - 1, blkOffsetBits) === 
//             current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits)) {
//             enprefetchnl := true.B
//           }
//         }
//         lookCount := 0.U
//         state := s_idle
//       }
//     }
//   }
//   XSPerfAccumulate("spp_pt_input_nums",io.req.valid)
//   XSPerfAccumulate("spp_pt_lookahead2",state === s_lookahead && enprefetch)
//   XSPerfAccumulate("spp_pt_nextLine",state === s_lookahead && enprefetchnl)
//   q.io.deq.ready := state === s_idle
// }

class PatternTableTiming(parentName:String="Unkown")(implicit p: Parameters) extends SPPModule {
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
    s0_current.signature := makeSign(s1_current.signature,s1_maxEntry.delta)
    // s0_current.signature := makeSign(s1_current.signature,strideMap(s1_maxEntry.delta))
  }.otherwise{
    s0_current.signature := issueReq.signature
  }

  when(state === s_lookahead && !s1_first_flag){
    s0_current.delta := s1_maxEntry.delta
    s0_current.block := s1_testOffset //TODO: need opimize?
    // s0_current.isBP := false.B
  }.elsewhen(state === s_idle){
    s0_current := q.io.deq.bits
  }.otherwise{
    s0_current := issueReq
  }

  val s0_bp_update = WireInit(s0_lookCount >= 3.U && s0_valid)
  io.pt2st_bp.valid := ENABLE_BP.asBool &&  s0_bp_update
  io.pt2st_bp.bits.pageAddr := s0_current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits)
  io.pt2st_bp.bits.parent_sig(0) := s0_current.signature
  io.pt2st_bp.bits.offset := s0_current.block(blkOffsetBits - 1, 0)

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
  s1_current := RegEnable(s0_current,0.U.asTypeOf(new SignatureTableResp),s0_valid)


  //directly calculate from sram 
  s1_readResult := Mux(s1_valid,pTable.io.r.resp.data(0),0.U.asTypeOf(new pTableEntry))
  s1_maxEntry := s1_readResult.deltaEntries.reduce((a, b) => Mux(a.cDelta >= b.cDelta, a, b))
  //set output
  val s1_delta_list = s1_readResult.deltaEntries.map(x => Mux(x.cDelta > s0_miniCount.asUInt, x.delta, 0.S))
  val s1_delta_list_nl = s1_delta_list.map(_ => 1.S((blkOffsetBits + 1).W))
  val s1_delta_list_checked = s1_delta_list.map(x =>
    Mux((s1_current.block.asSInt + x).asUInt(pageAddrBits + blkOffsetBits - 1, blkOffsetBits) === s1_current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits),
      x, 0.S))
  //TODO : need tag match ???
  val s1_hit = WireInit(s1_readResult.valid && get_tag(s1_current.signature) === s1_readResult.tag)
  // val s1_hit = WireInit(s1_readResult.valid)

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
  pTable.io.w.req.bits.setIdx := RegEnable(get_idx(s0_current.signature),0.U,write_hold)
  pTable.io.w.req.bits.data(0).valid := true.B
  pTable.io.w.req.bits.data(0).deltaEntries := RegEnable(s1_wdeltaEntries,0.U.asTypeOf(pTable.io.w.req.bits.data(0).deltaEntries.cloneType),write_hold)
  pTable.io.w.req.bits.data(0).count := RegEnable(s1_count,0.U(4.W),write_hold)
  pTable.io.w.req.bits.data(0).tag := RegEnable(get_tag(s1_current.signature),0.U,write_hold)


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
  // io.resp.bits.degree := s1_lookCount
  io.resp.bits.source := s1_current.source
  io.resp.bits.needT := s1_current.needT

  //perf
  XSPerfAccumulate("spp_pt_bp_nums",io.pt2st_bp.valid)
  XSPerfAccumulate("spp_pt_hit",state === s_lookahead && s1_hit)
  XSPerfAccumulate("spp_pt_lookahead2",state === s_lookahead && s1_valid && s1_continue)
  XSPerfAccumulate("spp_pt_enpf",state === s_lookahead && enprefetch)
  XSPerfAccumulate("spp_pt_nextLine",state === s_lookahead && enprefetchnl)
  XSPerfAccumulate("spp_pt_cross_page",state === s_lookahead && s1_valid && s1_samePage)
  for (i <- 0 until pTableEntries) {
    XSPerfAccumulate(s"spp_pt_touched_entry_onlyset_${i.toString}", pTable.io.r.req.bits.setIdx === i.U(log2Up(pTableEntries).W)
    )
  }
}

class Unpack(implicit p: Parameters) extends SPPModule {
  val io = IO(new Bundle {
    val req = Flipped(DecoupledIO(new PatternTableResp))
    val resp = DecoupledIO(new UnpackResp)
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

  val req = RegEnable(q.io.deq.bits,0.U.asTypeOf(new PatternTableResp), q.io.deq.fire)
  val req_deltas = Reg(Vec(pTableDeltaEntries, SInt((blkOffsetBits + 1).W)))
  val issue_finish = req_deltas.map(_ === 0.S).reduce(_ && _)
  q.io.deq.ready := !inProcess || issue_finish || endeq
  when(q.io.deq.fire) {
    req_deltas := q.io.deq.bits.deltas
  }
  
  val enresp = WireInit(false.B)
  val extract_delta = req_deltas.reduce((a, b) => Mux(a =/= 0.S, a, b))
  val prefetchBlock = (req.block.asSInt + extract_delta).asUInt

  val hit = WireInit(false.B)
  val s1_result = WireInit(0.U.asTypeOf(fTableEntry()))
  s1_result := fTable(idx(prefetchBlock))
  hit := s1_result.valid && tag(prefetchBlock) === s1_result.tag

  when(enresp && !hit) {
    fTable(idx(prefetchBlock)).valid := true.B
    fTable(idx(prefetchBlock)).tag := tag(prefetchBlock)
  }

  io.resp.valid := enresp && !hit
  io.resp.bits.prefetchBlock := prefetchBlock
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
    val train = Flipped(DecoupledIO(new PrefetchTrain)) //from higher level cache
    val req = DecoupledIO(new PrefetchReq) //issue to next-level cache
    val resp = Flipped(DecoupledIO(new PrefetchResp)) //fill request from the next-level cache, using this to update filter
  })
  val sTable = Module(new SignatureTable)
  val pTable = Module(new PatternTableTiming)
  val unpack = Module(new Unpack)

  val oldAddr = io.train.bits.addr //received request from L1 cache
  val pageAddr = getPPN(oldAddr)
  val blkOffset = oldAddr(pageOffsetBits - 1, offsetBits)

  sTable.io.req.valid := io.train.valid
  sTable.io.req.bits.pageAddr := pageAddr
  sTable.io.req.bits.blkOffset := blkOffset
  sTable.io.req.bits.needT := io.train.bits.needT
  sTable.io.req.bits.source := io.train.bits.source
  io.train.ready := sTable.io.req.ready

  pTable.io.req <> sTable.io.resp //to detail
  pTable.io.resp <> unpack.io.req
  pTable.io.from_ghr := DontCare

  val req = WireInit(0.U.asTypeOf(new PrefetchReq))

  val pf_newAddr = WireInit(Cat(unpack.io.resp.bits.prefetchBlock, 0.U(offsetBits.W)))
  req.tag := parseFullAddress(pf_newAddr)._1
  req.set := parseFullAddress(pf_newAddr)._2
  req.needT := unpack.io.resp.bits.needT
  req.source := unpack.io.resp.bits.source
  // req.isBOP := false.B
  req.pfVec := PfSource.SPP

  io.req.valid := unpack.io.resp.valid
  io.req.bits := req
  unpack.io.resp.ready := io.req.ready

  io.resp.ready := true.B

  XSPerfAccumulate("recv_train", io.train.fire)
  XSPerfAccumulate("recv_st", sTable.io.resp.fire)
  XSPerfAccumulate("recv_pt", Mux(pTable.io.resp.fire, 
      pTable.io.resp.bits.deltas.map(a => Mux(a =/= 0.S, 1.U, 0.U)).reduce(_ +& _), 0.U))
  XSPerfAccumulate("recv_up", unpack.io.resp.fire)
}

case class HyperPrefetchParams(
  fTableEntries: Int = 32,
  pTableQueueEntries: Int = 2,
  fTableQueueEntries: Int = 256
)
    extends PrefetchParameters {
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
  val fTagBits = pageAddrBits - log2Up(fTableEntries)
  val pTableQueueEntries = hyperParams.pTableQueueEntries
  val fTableQueueEntries = hyperParams.fTableQueueEntries
  val pfReqQueueEntries = 4
  def get_blockAddr(x:UInt) = x(fullAddressBits-1,offsetBits)
}

abstract class HyperPrefetchDev2Module(implicit val p: Parameters) extends Module with HasHyperPrefetchDev2Params with HasPerfLogging
abstract class HyperPrefetchDev2Bundle(implicit val p: Parameters) extends Bundle with HasHyperPrefetchDev2Params

class FilterTable(parentName:String = "Unknown")(implicit p: Parameters) extends HyperPrefetchDev2Module {
  val io = IO(new Bundle() {
    val req = Flipped(DecoupledIO(new PrefetchReq))
    val resp = DecoupledIO(new PrefetchReq)
    val evict = Flipped(DecoupledIO(new PrefetchEvict))
  })

  def get_idx(addr:      UInt) = addr(log2Up(fTableEntries) - 1, 0)
  def get_tag(addr:      UInt) = addr(pageAddrBits - 1, log2Up(fTableEntries))
  object FitlerVecState {
    val bits = 3

    def toN = 0.U(bits.W)
    def toB = 1.U(bits.W)
    def toS = 2.U(bits.W)
    def toC = 3.U(bits.W)

    def None          = 0.U(bits.W)
    def BOP           = 1.U(bits.W)
    def SPP           = 2.U(bits.W)
    def SMS           = 4.U(bits.W)
    def COMMON        = 3.U(bits.W)

    def getVecState(isHit:Bool, originV:UInt, trigerId:UInt) = (originV | trigerId) & ~(BOP)
    def checkOne(v:UInt) = v === BOP || v === SPP
    def checkTwo(v:UInt) = v === COMMON
    def hasMyself(v:UInt,originV:UInt) = (v & originV) === v
    def hasMerged(v:UInt,originV:UInt) = v =/= originV
    def is_SPPchase(v:UInt,originV:UInt) = hasMyself(v,SPP) && (originV === BOP || originV === (BOP | SMS))
  }
  val dupNums = 8
  val dupOffsetBits = log2Up(fTableEntries/dupNums)
  val dupBits = log2Up(dupNums)
  val req_dups = RegInit(VecInit(Seq.fill(dupNums)(0.U.asTypeOf(Valid(new PrefetchReq)))))
  val req_issue = WireInit(0.U.asTypeOf(DecoupledIO(new PrefetchReq())));dontTouch(req_issue)
  dontTouch(io)
  // --------------------------------------------------------------------------------
  // consensus Table cTable
  // --------------------------------------------------------------------------------
  // | valid | tag | cVec[[pfVec],[pfVec],...,[pfVec]]
  // | valid | tag | cVec[[pfVec],[pfVec],...,[pfVec]]
  // | valid | tag | cVec[[001], [100] , ..., [111]]
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
    val evict_q = Module(new Queue(UInt(fullAddressBits.W), fTableQueueEntries, flow = false, pipe = true))
    // val evict_q = Module(new SRAMQueue(UInt(blkAddrBits.W),entries = fTableQueueEntries, flow = false, 
    //     hasMbist = cacheParams.hasMbist, hasClkGate=enableClockGate, hasShareBus = cacheParams.hasShareBus, parentName=parentName+"filterDelayQ"))

    // --------------------------------------------------------------------------------
    // stage 0
    // --------------------------------------------------------------------------------
    // read filterTable
    val s0_valid = WireInit(false.B);dontTouch(s0_valid)
    val s0_req = WireInit(0.U.asTypeOf(new PrefetchReq));dontTouch(s0_req)
    val s0_result = WireInit(0.U.asTypeOf(fTableEntry()));dontTouch(s0_result)
    val s0_oldAddr = WireInit(s0_req.addr);dontTouch(s0_oldAddr)
    val s0_pageAddr = WireInit(s0_oldAddr(fullAddressBits - 1, pageOffsetBits));dontTouch(s0_pageAddr)
    val s0_blkOffset = WireInit(s0_oldAddr(pageOffsetBits - 1, offsetBits));dontTouch(s0_blkOffset)

    s0_valid := io.req.valid
    s0_req := Mux(s0_valid,io.req.bits,0.U.asTypeOf(new PrefetchReq))
    when(s0_valid){
        s0_result := consensusTable(get_idx(s0_pageAddr))
    }.otherwise{
        s0_result := 0.U.asTypeOf(fTableEntry())
    }
    // --------------------------------------------------------------------------------
    // stage 1
    // --------------------------------------------------------------------------------
    // calculate
    val s1_valid = VecInit.fill(dupNums)(RegNext(s0_valid,false.B));dontTouch(s1_valid)
    val s1_req = VecInit.fill(dupNums)(RegEnable(s0_req,0.U.asTypeOf(new PrefetchReq),s0_valid(0)));dontTouch(s1_req)
    val s1_result = VecInit.fill(dupNums)(RegEnable(s0_result,0.U.asTypeOf(fTableEntry()),s0_valid(0)));dontTouch(s1_result)
    val s1_oldAddr = WireInit(s1_req(1).addr);dontTouch(s1_oldAddr)
    val s1_dup_offset = WireInit(s1_req(1).set(dupOffsetBits-1+dupBits-1,dupOffsetBits-1));dontTouch(s1_dup_offset)

    val s1_pageAddr = WireInit(s1_oldAddr(fullAddressBits - 1, pageOffsetBits));dontTouch(s1_pageAddr)
    val s1_blkOffset = WireInit(s1_oldAddr(pageOffsetBits - 1, offsetBits));dontTouch(s1_blkOffset)
    val s1_hit = WireInit(VecInit.fill(dupNums)(false.B))
    
    val s1_hitForMap_filtedpfVec = WireInit(VecInit.fill(dupNums)(0.U(PfSource.bits.W)));dontTouch(s1_hitForMap_filtedpfVec)
    val s1_hitForMap_bitVec = WireInit(VecInit.fill(dupNums)(VecInit.fill(blkNums)(false.B)));dontTouch(s1_hitForMap_bitVec)
    //val hitForMap_needDrop = WireInit(VecInit.fill(dupNums)(false.B));dontTouch(hitForMap_needDrop)
    val s1_can_send2_pfq = WireInit(VecInit.fill(dupNums)(false.B));dontTouch(s1_can_send2_pfq)
    //val s1_anchored_longest_blkOff = WireInit(VecInit.fill(dupNums)(0.U(blkOffsetBits.W)));dontTouch(s1_anchored_longest_blkOff)
    val s1_next_VecState = WireInit(VecInit.fill(dupNums)(0.U(PfVectorConst.bits.W)))

    val s1_wBitMap = WireInit(VecInit.fill(dupNums)(VecInit.fill(blkNums)(0.U(FitlerVecState.bits.W))));dontTouch(s1_wBitMap)
    val s1_wData = WireInit(VecInit.fill(dupNums)(0.U.asTypeOf(fTableEntry())))

    for(i <- 0 until(dupNums)) {
        when(s1_req(i).set(dupOffsetBits-1+dupBits-1,dupOffsetBits-1) === i.U(dupBits.W)) {
        val trigerId = s1_req(i).pfVec
        s1_hit(i) := s1_result(i).valid && get_tag(s1_pageAddr) === s1_result(i).tag

        val anchored_cVec = s1_result(i).cVec
        val anchored_value = s1_result(i).cVec(s1_blkOffset)
        //hitForMap_needDrop(i) := hit(i) && FitlerVecState.hasMerged(s1_req(i).pfVec, anchored_value)
        s1_next_VecState(i) := Mux(s1_hit(i),FitlerVecState.getVecState(true.B, originV = anchored_value, trigerId = s1_req(i).pfVec),s1_req(i).pfVec)
        
        for (j <- 0 until s1_result(i).cVec.length){
            when(s1_hit(i)){
                s1_wBitMap(i)(j) := Mux(j.asUInt === s1_blkOffset, s1_next_VecState(i), anchored_cVec(j))
                s1_hitForMap_bitVec(i)(j) := anchored_cVec(j) =/= PfSource.NONE
                s1_hitForMap_filtedpfVec(i) := s1_result(i).cVec(s1_blkOffset)
            }.otherwise{
                s1_wBitMap(i)(j) := Mux(j.asUInt === s1_blkOffset, s1_next_VecState(i), PfSource.NONE)
                s1_hitForMap_bitVec(i)(j) := false.B
                s1_hitForMap_filtedpfVec(i) := PfSource.NONE
            }
        }
        //s1_anchored_longest_blkOff(i) := OneHot.OH1ToUInt(HighestBit(s1_hitForMap_bitVec(i).asUInt,blkNums))
        // should filter when any other prefetchBitVec existed expected prefetch from bop
        s1_can_send2_pfq(i) := !s1_hit(i) || (s1_hit(i) && (anchored_value === PfSource.NONE|| s1_req(i).hasBOP))//anchored_value === PfSource.NONE //|| anchored_value === PfSource.BOP || anchored_value === PfSource.SMS

        s1_wData(i).valid := true.B
        s1_wData(i).tag := get_tag(s1_pageAddr)
        s1_wData(i).cVec := s1_wBitMap(i)
        }.otherwise{
        s1_result(i) := 0.U.asTypeOf(fTableEntry())
        }
    }
    val s1_widx = WireInit(get_idx(s1_req(s1_dup_offset).addr(fullAddressBits - 1, pageOffsetBits)(log2Up(fTableEntries)-1,0)));dontTouch(s1_widx)
    when(s1_valid(s1_dup_offset)) {
        when(s1_hit(s1_dup_offset)){
            consensusTable(s1_widx).cVec := s1_wData(s1_dup_offset).cVec
        }.otherwise{
            consensusTable(s1_widx) := s1_wData(s1_dup_offset)
        }
    }

    io.req.ready := true.B
    io.resp.valid := s1_valid(s1_dup_offset) && s1_can_send2_pfq(s1_dup_offset)
    io.resp.bits := s1_req(s1_dup_offset)
    // --------------------------------------------------------------------------------
    // evict operation
    // --------------------------------------------------------------------------------
    evict_q.io.enq.valid := s1_valid(s1_dup_offset) && s1_can_send2_pfq.reduce(_ ||_ ) // if spp2llc , don't enq
    evict_q.io.enq.bits := get_blockAddr(req_dups(s1_dup_offset).bits.addr)
    val isqFull = evict_q.io.count === (fTableQueueEntries-1).U
    evict_q.io.deq.ready := isqFull;dontTouch(evict_q.io.deq.ready)

    val evictAddr = WireInit(Cat(evict_q.io.deq.bits,0.U(offsetBits.W)))
    val evictPageAddr = evictAddr(fullAddressBits - 1, pageOffsetBits)
    val evictBlkOffset = evictAddr(pageOffsetBits - 1, offsetBits)
    val evictBlkAddr = evictAddr(fullAddressBits - 1, offsetBits)
    val readEvict = WireInit(0.U.asTypeOf(fTableEntry()))
    val hitEvict =  WireInit(false.B)
    val req_evict = req_dups(dupNums-1)

    val oldAddr = req_evict.bits.addr
    val blkAddr = oldAddr(fullAddressBits - 1, offsetBits)
    val conflict = req_evict.valid && blkAddr === evictBlkAddr
    readEvict := consensusTable(get_idx(evictPageAddr))
    hitEvict := evict_q.io.deq.fire && readEvict.valid && get_tag(evictPageAddr) === readEvict.tag && !conflict

    when(hitEvict) {
      // consensusTable(get_idx(evictPageAddr)).cVec(evictBlkOffset) := consensusTable(get_idx(evictPageAddr)).cVec(evictBlkOffset) & FitlerVecState.BOP
      consensusTable(get_idx(evictPageAddr)).cVec(evictBlkOffset) := FitlerVecState.None //TODO: need further study
    }
    io.evict.ready := true.B

  XSPerfAccumulate("hyper_filter_nums",s1_valid(s1_dup_offset) && !io.resp.valid)
  XSPerfAccumulate("hyper_filter_input",io.req.valid)
  XSPerfAccumulate("hyper_filter_input_sms",io.req.valid && io.req.bits.pfVec === FitlerVecState.SMS)
  XSPerfAccumulate("hyper_filter_input_bop",io.req.valid && io.req.bits.pfVec === FitlerVecState.BOP)
  XSPerfAccumulate("hyper_filter_input_spp",io.req.valid && io.req.bits.pfVec === FitlerVecState.SPP)
  XSPerfAccumulate("hyper_filter_output",io.resp.valid)
  XSPerfAccumulate("hyper_filter_output_sms",io.resp.valid && io.resp.bits.pfVec === FitlerVecState.SMS)
  XSPerfAccumulate("hyper_filter_output_bop",io.resp.valid && io.resp.bits.pfVec === FitlerVecState.BOP)
  XSPerfAccumulate("hyper_filter_output_spp",io.resp.valid && io.resp.bits.pfVec === FitlerVecState.SPP)
  XSPerfAccumulate("hyper_filter_evict_fomMshr",io.evict.fire)
  XSPerfAccumulate("hyper_filter_evict_fromQ",hitEvict)
}

//Only used for hybrid spp and bop
class HyperPrefetchDev2(parentName:String = "Unknown")(implicit p: Parameters) extends HyperPrefetchDev2Module {
  val io = IO(new Bundle() {
    val train = Flipped(DecoupledIO(new PrefetchTrain))
    val req = DecoupledIO(new PrefetchReq)
    val resp = Flipped(DecoupledIO(new PrefetchResp))
    val evict = Flipped(DecoupledIO(new PrefetchEvict))
    val recv_addr = Flipped(ValidIO(UInt(64.W)))
  })

  val fTable = Module(new FilterTable)

  val spp = Module(new SignaturePathPrefetch()(p.alterPartial({
        case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(SPPParameters()))
  })))
  val bop = Module(new BestOffsetPrefetch()(p.alterPartial({
        case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(BOPParameters()))
  })))
  val sms = Module(new PrefetchReceiver()(p.alterPartial({
        case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(PrefetchReceiverParams()))
  })))

  val q_bop = Module(new ReplaceableQueueV2(chiselTypeOf(bop.io.req.bits), pfReqQueueEntries))
  val q_spp = Module(new ReplaceableQueueV2(chiselTypeOf(spp.io.req.bits), pfReqQueueEntries))
  val q_sms = Module(new ReplaceableQueueV2(chiselTypeOf(spp.io.req.bits), pfReqQueueEntries))
  // --------------------------------------------------------------------------------
  // train diverter queue
  // --------------------------------------------------------------------------------
  val train_q = Module(new Queue(new PrefetchTrain, entries = 4, flow = true, pipe = false))
  val train_bop_q = Module(new Queue(new PrefetchTrain, entries = 2, flow = true, pipe = false))
  val train_spp_q = Module(new Queue(new PrefetchTrain, entries = 2, flow = true, pipe = false))
  dontTouch(train_q.io)
  train_q.io.enq <> io.train
  train_bop_q.io.enq <> train_q.io.deq
  train_spp_q.io.enq <> train_q.io.deq
  //devert
  bop.io.train.valid := train_bop_q.io.deq.valid
  bop.io.train.bits := train_q.io.deq.bits
  train_bop_q.io.deq.ready := bop.io.train.ready

  spp.io.train.valid := train_spp_q.io.deq.valid
  spp.io.train.bits := train_spp_q.io.deq.bits
  train_spp_q.io.deq.ready := spp.io.train.ready

  bop.io.resp.valid := io.resp.valid && io.resp.bits.hasBOP
  bop.io.resp.bits := io.resp.bits
  io.resp.ready := bop.io.resp.ready

  spp.io.resp.valid := false.B
  spp.io.resp.bits.tag := 0.U
  spp.io.resp.bits.set := 0.U
  spp.io.resp.bits.pfVec := PfSource.SPP

  sms.io.recv_addr.valid := io.recv_addr.valid
  sms.io.recv_addr.bits := io.recv_addr.bits
  sms.io.req.ready := true.B
  // 
  q_sms.io.enq <> sms.io.req
  q_bop.io.enq <> bop.io.req
  q_spp.io.enq <> spp.io.req 
  // qurry fTable
  fTable.io.req.valid := q_spp.io.deq.valid || q_bop.io.deq.valid ||  q_sms.io.deq.valid
  fTable.io.req.bits := ParallelPriorityMux(
    Seq(
      q_sms.io.deq.valid -> q_sms.io.deq.bits,
      q_bop.io.deq.valid -> q_bop.io.deq.bits,
      q_spp.io.deq.valid -> q_spp.io.deq.bits,
    )
  )
  q_sms.io.deq.ready := fTable.io.req.ready
  q_bop.io.deq.ready := fTable.io.req.ready && !q_sms.io.deq.valid
  q_spp.io.deq.ready := fTable.io.req.ready && !q_sms.io.deq.valid && !q_bop.io.deq.valid

  io.req <> fTable.io.resp

  // io.req <> q_bop.io.deq
  fTable.io.evict.valid := false.B//io.evict.valid
  fTable.io.evict.bits := io.evict.bits
  io.evict.ready := fTable.io.evict.ready

  io.train.ready := true.B

  XSPerfAccumulate("spp_deq_blocked", q_spp.io.deq.valid && !q_spp.io.deq.ready)
  XSPerfAccumulate("bop_deq_blocked", q_bop.io.deq.valid && !q_bop.io.deq.ready)
}