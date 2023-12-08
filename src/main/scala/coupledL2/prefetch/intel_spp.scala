// error when 000 signature occurs in pTable
package coupledL2.prefetch.intel_spp

import org.chipsalliance.cde.config.Parameters
import chisel3._
import chisel3.util._
import xs.utils.sram.SRAMTemplate
import xs.utils.Pipeline

import coupledL2.{HasCoupledL2Parameters,L2ParamKey}
import xs.utils.perf.HasPerfLogging
import coupledL2.prefetch.{PrefetchParameters,PrefetchTrain,PrefetchReq,PrefetchResp,PrefetchEvict}
import coupledL2.prefetch.{BestOffsetPrefetch,BOPParameters,PrefetchReceiver,PrefetchReceiverParams}

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

  val pageAddrBits = fullAddressBits - pageOffsetBits
  val blkOffsetBits = pageOffsetBits - offsetBits
  val sTagBits = pageAddrBits - log2Up(sTableEntries)
  val fTagBits = fullAddressBits - offsetBits - log2Up(fTableEntries)
}

abstract class SPPBundle(implicit val p: Parameters) extends Bundle with HasSPPParams
abstract class SPPModule(implicit val p: Parameters) extends Module with HasSPPParams with HasPerfLogging

class SignatureTableReq(implicit p: Parameters) extends SPPBundle {
  val pageAddr = UInt(pageAddrBits.W)
  val blkOffset = UInt(blkOffsetBits.W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
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
    val entry = Wire(this)
    entry.delta := delta
    entry.cDelta := cDelta
    entry
  }
}


class SignatureTable(implicit p: Parameters) extends SPPModule {
  val io = IO(new Bundle {
    val req = Flipped(DecoupledIO(new SignatureTableReq))
    val resp = DecoupledIO(new SignatureTableResp) //output old signature and delta to write PT
  })
  def hash1(addr:    UInt) = addr(log2Up(sTableEntries) - 1, 0)
  def hash2(addr:    UInt) = addr(2 * log2Up(sTableEntries) - 1, log2Up(sTableEntries))
  def idx(addr:      UInt) = hash1(addr) ^ hash2(addr)
  def tag(addr:      UInt) = addr(pageAddrBits - 1, log2Up(sTableEntries))
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
    new SRAMTemplate(sTableEntry(), set = sTableEntries, way = 1, bypassWrite = true, shouldReset = true)
  )

  val rAddr = io.req.bits.pageAddr
  val rData = Wire(sTableEntry())
  val lastAccessedPage = RegNext(io.req.bits.pageAddr)
  val lastAccessedBlock = RegNext(io.req.bits.blkOffset)

  sTable.io.r.req.valid := io.req.fire
  sTable.io.r.req.bits.setIdx := idx(rAddr)
  rData := sTable.io.r.resp.data(0)

  val hit = rData.valid && rData.tag === tag(lastAccessedPage)
  val oldSignature = Mux(hit, rData.signature, 0.U)
  val newDelta = Mux(hit, lastAccessedBlock.asSInt - rData.lastBlock.asSInt, lastAccessedBlock.asSInt)

  sTable.io.w.req.valid := RegNext(sTable.io.r.req.fire) && newDelta =/= 0.S
  sTable.io.w.req.bits.setIdx := idx(lastAccessedPage)
  sTable.io.w.req.bits.data(0).valid := true.B
  sTable.io.w.req.bits.data(0).tag := tag(lastAccessedPage)
  sTable.io.w.req.bits.data(0).signature := (oldSignature << 3) ^ newDelta.asUInt
  sTable.io.w.req.bits.data(0).lastBlock := lastAccessedBlock

  io.resp.valid := RegNext(sTable.io.r.req.fire) && newDelta =/= 0.S
  io.resp.bits.signature := oldSignature
  io.resp.bits.delta := newDelta
  io.resp.bits.block := RegNext(Cat(io.req.bits.pageAddr, io.req.bits.blkOffset))
  io.resp.bits.needT := RegNext(io.req.bits.needT)
  io.resp.bits.source := RegNext(io.req.bits.source)

  io.req.ready := sTable.io.r.req.ready
}

class PatternTable(implicit p: Parameters) extends SPPModule {
  val io = IO(new Bundle {
    val req = Flipped(DecoupledIO(new SignatureTableResp))
    val resp = DecoupledIO(new PatternTableResp)
  })  

  def pTableEntry() = new Bundle {
    val valid = Bool()
    //val deltaEntries = VecInit(Seq.fill(pTableDeltaEntries)((new DeltaEntry).apply(0.S, 0.U)))
    val deltaEntries = Vec(pTableDeltaEntries, new DeltaEntry())
    val count = UInt(4.W)
  }

  def slowLookTable(lc: UInt): UInt = {
    Mux(lc >= 1.U && lc <= 4.U, (lc >> 1.U) + 1.U, lc)
  }

  val pTable = Module(
    new SRAMTemplate(pTableEntry(), set = pTableEntries, way = 1, bypassWrite = true, shouldReset = true)
  )

  val q = Module(new ReplaceableQueueV2(chiselTypeOf(io.req.bits), pTableQueueEntries))
  q.io.enq <> io.req
  val req = q.io.deq.bits

  val s_idle :: s_lookahead0 :: s_lookahead :: Nil = Enum(3)
  val state = RegInit(s_idle)
  val readResult = Wire(pTableEntry())
  val readSignature = WireDefault(0.U(signatureBits.W)) //to differentiate the result from io or lookahead, set based on state
  val readDelta = WireDefault(0.S((blkOffsetBits + 1).W))
  val lastSignature = Wire(UInt(signatureBits.W))
  val lastDelta = Wire(SInt((blkOffsetBits + 1).W))
  val hit = WireDefault(false.B)
  val enread = WireDefault(false.B)
  val enprefetch = WireDefault(false.B)
  val enprefetchnl = WireDefault(false.B)
  val enwrite = RegNext(q.io.deq.fire && pTable.io.r.req.fire) //we only modify-write on demand requests
  val current = Reg(new SignatureTableResp) // RegInit(0.U.asTypeOf(new PatternTableResp))
  val lookCount = RegInit(0.U(6.W))
  val miniCount = Mux(q.io.empty, slowLookTable(lookCount), lookCount)
  // val miniCount = slowLookTable(lookCount)

  //read pTable
  pTable.io.r.req.valid := enread
  pTable.io.r.req.bits.setIdx := readSignature
  readResult := pTable.io.r.resp.data(0)
  hit := readResult.valid
  lastSignature := RegNext(readSignature)
  lastDelta := RegNext(readDelta)
  //set output
  val maxEntry = readResult.deltaEntries.reduce((a, b) => Mux(a.cDelta >= b.cDelta, a, b))
  val delta_list = readResult.deltaEntries.map(x => Mux(x.cDelta > miniCount, x.delta, 0.S))
  val delta_list_checked = delta_list.map(x => 
            Mux((current.block.asSInt + x).asUInt(pageAddrBits + blkOffsetBits - 1, blkOffsetBits)
            === current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits), x, 0.S))
  val delta_list_nl = delta_list.map(_ => 1.S((blkOffsetBits + 1).W))

  io.resp.valid := enprefetch || enprefetchnl
  io.resp.bits.block := current.block
  io.resp.bits.deltas := delta_list_checked
  io.resp.bits.needT := current.needT
  io.resp.bits.source := current.source
  when(enprefetchnl) {
    io.resp.bits.deltas := delta_list_nl
  }

  //modify table
  val deltaEntries = Wire(Vec(pTableDeltaEntries, new DeltaEntry()))
  val count = Wire(UInt(4.W))
  when(hit) {
    val exist = readResult.deltaEntries.map(_.delta === lastDelta).reduce(_ || _)
    when(exist) {
      val temp = readResult.deltaEntries.map(x =>
        Mux(x.delta === lastDelta, (new DeltaEntry).apply(lastDelta, x.cDelta + 1.U), x)) 
      //counter overflow
      when(readResult.count + 1.U === ((1.U << count.getWidth) - 1.U)) {
        deltaEntries := temp.map(x => (new DeltaEntry).apply(x.delta, x.cDelta >> 1.U))
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
  pTable.io.w.req.bits.setIdx := lastSignature
  pTable.io.w.req.bits.data(0).valid := true.B
  pTable.io.w.req.bits.data(0).deltaEntries := deltaEntries
  pTable.io.w.req.bits.data(0).count := count
  
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
      readSignature := (lastSignature << 3) ^ lastDelta.asUInt
      state := s_lookahead
    }
    is(s_lookahead) {
      when(hit) {
        val issued = delta_list_checked.map(a => Mux(a =/= 0.S, 1.U, 0.U)).reduce(_ +& _)
        when(issued =/= 0.U) {
          enprefetch := true.B
          val testOffset = (current.block.asSInt + maxEntry.delta).asUInt
          //same page?
          when(testOffset(pageAddrBits + blkOffsetBits - 1, blkOffsetBits) === 
            current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits)
            && maxEntry.cDelta > miniCount) {
            lookCount := lookCount + 1.U
            readSignature := (lastSignature << 3) ^ maxEntry.delta.asUInt
            current.block := testOffset
            enread := true.B
          } .otherwise {
            lookCount := 0.U
            state := s_idle
          }
        }.otherwise {
          lookCount := 0.U
          state := s_idle
        } 
      } .otherwise {
        when(lookCount <= 1.U) {
          val testOffset = current.block + 1.U
          when(testOffset(pageAddrBits + blkOffsetBits - 1, blkOffsetBits) === 
            current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits)) {
            enprefetchnl := true.B
          }
        }
        lookCount := 0.U
        state := s_idle
      }
    }
  }

  q.io.deq.ready := state === s_idle
}

//Can add eviction notify or cycle counter for each entry
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
  val endeq = WireDefault(false.B)

  val q = Module(new ReplaceableQueueV2(chiselTypeOf(io.req.bits), unpackQueueEntries))
  q.io.enq <> io.req //change logic to replace the tail entry

  val req = RegEnable(q.io.deq.bits, q.io.deq.fire)
  val req_deltas = Reg(Vec(pTableDeltaEntries, SInt((blkOffsetBits + 1).W)))
  val issue_finish = req_deltas.map(_ === 0.S).reduce(_ && _)
  q.io.deq.ready := !inProcess || issue_finish || endeq
  when(q.io.deq.fire) {
    req_deltas := q.io.deq.bits.deltas
  }
  
  val enresp = WireDefault(false.B)
  val extract_delta = req_deltas.reduce((a, b) => Mux(a =/= 0.S, a, b))
  val prefetchBlock = (req.block.asSInt + extract_delta).asUInt

  val hit = Wire(Bool())
  val readResult = Wire(fTableEntry())
  readResult := fTable(idx(prefetchBlock))
  hit := readResult.valid && tag(prefetchBlock) === readResult.tag

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
  val pTable = Module(new PatternTable)
  val unpack = Module(new Unpack)

  val oldAddr = io.train.bits.addr //received request from L1 cache
  val pageAddr = getPPN(oldAddr)
  val blkOffset = oldAddr(pageOffsetBits - 1, offsetBits)

  // might be lack of prefetch requests
  io.train.ready := sTable.io.req.ready
  
  sTable.io.req.bits.pageAddr := pageAddr
  sTable.io.req.bits.blkOffset := blkOffset
  sTable.io.req.bits.needT := io.train.bits.needT
  sTable.io.req.bits.source := io.train.bits.source
  sTable.io.req.valid := io.train.fire

  pTable.io.req <> sTable.io.resp //to detail
  pTable.io.resp <> unpack.io.req

  val req = Reg(new PrefetchReq)
  val req_valid = RegInit(false.B)
  unpack.io.resp.ready := true.B
  when(io.req.fire && !unpack.io.resp.fire) {
    req_valid := false.B
  }
  when(unpack.io.resp.fire) {
    val newAddr = Cat(unpack.io.resp.bits.prefetchBlock, 0.U(offsetBits.W))
    req.tag := parseFullAddress(newAddr)._1
    req.set := parseFullAddress(newAddr)._2
    req.needT := unpack.io.resp.bits.needT
    req.source := unpack.io.resp.bits.source
    req.isBOP := false.B
    req_valid := true.B 
  }
  io.req.valid := req_valid
  io.req.bits := req
  io.resp.ready := true.B

  XSPerfAccumulate("recv_train", io.train.fire)
  XSPerfAccumulate("recv_st", sTable.io.resp.fire)
  XSPerfAccumulate("recv_pt", Mux(pTable.io.resp.fire, 
      pTable.io.resp.bits.deltas.map(a => Mux(a =/= 0.S, 1.U, 0.U)).reduce(_ +& _), 0.U))
  XSPerfAccumulate("recv_up", unpack.io.resp.fire)
}

case class PrefetchBranchV2Params(
  fTableEntries: Int = 32,
  pTableQueueEntries: Int = 2,
  fTableQueueEntries: Int = 256
)
    extends PrefetchParameters {
  override val hasPrefetchBit:  Boolean = true
  override val inflightEntries: Int = 32
}

trait HasPrefetchBranchV2Params extends HasCoupledL2Parameters {
  val prefetchBranchV2Params = PrefetchBranchV2Params()

  val pageAddrBits = fullAddressBits - pageOffsetBits
  val blkOffsetBits = pageOffsetBits - offsetBits

  val fTableEntries = prefetchBranchV2Params.fTableEntries
  val fTagBits = pageAddrBits - log2Up(fTableEntries)
  val pTableQueueEntries = prefetchBranchV2Params.pTableQueueEntries
  val fTableQueueEntries = prefetchBranchV2Params.fTableQueueEntries
}

abstract class PrefetchBranchV2Module(implicit val p: Parameters) extends Module with HasPrefetchBranchV2Params with HasPerfLogging
abstract class PrefetchBranchV2Bundle(implicit val p: Parameters) extends Bundle with HasPrefetchBranchV2Params

class FilterV2(implicit p: Parameters) extends PrefetchBranchV2Module {
  val io = IO(new Bundle() {
    val req = Flipped(DecoupledIO(new PrefetchReq))
    val resp = DecoupledIO(new PrefetchReq)
    val evict = Flipped(DecoupledIO(new PrefetchEvict))
    val from_bop = Input(Bool())
  })

  def idx(addr:      UInt) = addr(log2Up(fTableEntries) - 1, 0)
  def tag(addr:      UInt) = addr(pageAddrBits - 1, log2Up(fTableEntries))

  def fTableEntry() = new Bundle {
    val valid = Bool()
    val tag = UInt(fTagBits.W)
    val bitMap = Vec(64, Bool())
  }

  val fTable = RegInit(VecInit(Seq.fill(fTableEntries)(0.U.asTypeOf(fTableEntry()))))
  val q = Module(new ReplaceableQueueV2(UInt(fullAddressBits.W), fTableQueueEntries))

  val oldAddr = io.req.bits.addr
  val blkAddr = oldAddr(fullAddressBits - 1, offsetBits)
  val pageAddr = oldAddr(fullAddressBits - 1, pageOffsetBits)
  val blkOffset = oldAddr(pageOffsetBits - 1, offsetBits)

  //read fTable
  val hit = Wire(Bool())
  val readResult = Wire(fTableEntry())
  readResult := fTable(idx(pageAddr))
  hit := readResult.valid && tag(pageAddr) === readResult.tag
  val hitForMap = hit && readResult.bitMap(blkOffset)

  io.resp.valid := io.req.fire && (!hitForMap || io.from_bop)
  io.resp.bits := io.req.bits

  val wData = Wire(fTableEntry())
  val newBitMap = readResult.bitMap.zipWithIndex.map{ case (b, i) => Mux(i.asUInt === blkOffset, true.B, false.B) }
  
  wData.valid := true.B
  wData.tag := tag(pageAddr)
  wData.bitMap := newBitMap
  when(io.req.fire) {
    when(hit) {
      fTable(idx(pageAddr)).bitMap(blkOffset) := true.B
    } .otherwise {
      fTable(idx(pageAddr)) := wData
    }
  }

  q.io.enq.valid := io.req.fire && !hitForMap
  q.io.enq.bits := io.req.bits.addr
  q.io.deq.ready := q.io.full && q.io.enq.fire

  val evictAddr = q.io.deq.bits
  val evictPageAddr = evictAddr(fullAddressBits - 1, pageOffsetBits)
  val evictBlkOffset = evictAddr(pageOffsetBits - 1, offsetBits)
  val evictBlkAddr = evictAddr(fullAddressBits - 1, offsetBits)
  val readEvict = Wire(fTableEntry())
  val hitEvict = Wire(Bool())
  val conflict = io.req.fire && blkAddr === evictBlkAddr
  readEvict := fTable(idx(evictPageAddr))
  hitEvict := q.io.deq.fire && readEvict.valid && tag(evictPageAddr) === readEvict.tag && readEvict.bitMap(evictBlkOffset) && !conflict
  when(hitEvict) {
    fTable(idx(evictPageAddr)).bitMap(evictBlkOffset) := false.B
  }

  /*
  val evictAddr = io.evict.bits.addr
  val evictPageAddr = evictAddr(fullAddressBits - 1, pageOffsetBits)
  val evictBlkOffset = evictAddr(pageOffsetBits - 1, offsetBits)
  val evictBlkAddr = evictAddr(fullAddressBits - 1, offsetBits)
  val readEvict = Wire(fTableEntry())
  val hitEvict = Wire(Bool())
  val conflict = io.req.fire && blkAddr === evictBlkAddr
  readEvict := fTable(idx(evictPageAddr))
  hitEvict := io.evict.valid && readEvict.valid && tag(evictPageAddr) === readEvict.tag && readEvict.bitMap(evictBlkOffset) && !conflict
  when(hitEvict) {
    fTable(idx(evictPageAddr)).bitMap(evictBlkOffset) := false.B
  }*/

  io.req.ready := true.B
  io.evict.ready := true.B
}

//Only used for hybrid spp and bop
class PrefetchBranchV2()(implicit p: Parameters) extends PrefetchBranchV2Module {
  val io = IO(new Bundle() {
    val train = Flipped(DecoupledIO(new PrefetchTrain))
    val req = DecoupledIO(new PrefetchReq)
    val resp = Flipped(DecoupledIO(new PrefetchResp))
    val evict = Flipped(DecoupledIO(new PrefetchEvict))
    val recv_addr = Flipped(ValidIO(UInt(64.W)))
  })

  val fTable = Module(new FilterV2)

  val spp = Module(new SignaturePathPrefetch()(p.alterPartial({
        case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(SPPParameters()))
  })))
  val bop = Module(new BestOffsetPrefetch()(p.alterPartial({
        case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(BOPParameters()))
  })))
  val sms = Module(new PrefetchReceiver()(p.alterPartial({
        case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(PrefetchReceiverParams()))
  })))

  val q_bop = Module(new ReplaceableQueueV2(chiselTypeOf(bop.io.req.bits), pTableQueueEntries))
  q_bop.io.enq <> bop.io.req
  q_bop.io.deq.ready := !sms.io.req.valid
  val bop_req = q_bop.io.deq.bits

  val q_spp = Module(new ReplaceableQueueV2(chiselTypeOf(spp.io.req.bits), pTableQueueEntries))
  q_spp.io.enq <> spp.io.req
  q_spp.io.deq.ready := !q_bop.io.deq.fire && !sms.io.req.valid
  val spp_req = q_spp.io.deq.bits

  spp.io.train.valid := io.train.valid
  spp.io.train.bits := io.train.bits

  val train_for_bop = Reg(new PrefetchTrain)
  val train_for_bop_valid = RegInit(false.B)
  
  when(io.train.valid && !bop.io.train.ready) {
    train_for_bop := io.train.bits
    train_for_bop_valid := true.B
  }
  bop.io.train.valid := io.train.valid || train_for_bop_valid
  bop.io.train.bits := Mux(io.train.valid, io.train.bits, train_for_bop)
  when(bop.io.train.fire && !io.train.valid) {
    train_for_bop_valid := false.B
  }

  bop.io.resp <> io.resp
  spp.io.resp.bits.tag := 0.U
  spp.io.resp.bits.set := 0.U
  spp.io.resp.valid := false.B

  spp.io.req.ready := true.B
  bop.io.req.ready := true.B

  sms.io.recv_addr.valid := io.recv_addr.valid
  sms.io.recv_addr.bits := io.recv_addr.bits
  sms.io.req.ready := true.B

  fTable.io.req.valid := q_spp.io.deq.fire || q_bop.io.deq.fire || sms.io.req.valid
  fTable.io.req.bits := Mux(sms.io.req.valid, sms.io.req.bits, 
                          Mux(q_bop.io.deq.fire, bop_req, spp_req))
  fTable.io.from_bop := bop.io.req.valid
  io.req <> fTable.io.resp

  fTable.io.evict.valid := io.evict.valid
  fTable.io.evict.bits := io.evict.bits
  io.evict.ready := fTable.io.evict.ready

  io.train.ready := true.B

  XSPerfAccumulate("sms_send2_queue", fTable.io.resp.fire && sms.io.req.valid)
  XSPerfAccumulate("bop_send2_queue", fTable.io.resp.fire && q_bop.io.deq.fire)
  XSPerfAccumulate("spp_send2_queue", fTable.io.resp.fire && q_spp.io.deq.fire)
}