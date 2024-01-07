package coupledL2.prefetch.MCLP

import org.chipsalliance.cde.config.Parameters
import chisel3._
import chisel3.util._
import freechips.rocketchip.tilelink._
import coupledL2._
import coupledL2.HasCoupledL2Parameters
import xs.utils.perf.HasPerfLogging
import xs.utils.{CircularShift,CircularQueuePtr,HasCircularQueuePtrHelper}
import xs.utils.SRAMQueue
import xs.utils.ParallelPriorityMux
import xs.utils.FastArbiter
import xs.utils.ParallelOperation
import xs.utils.HighestBit
import xs.utils.OneHot
import xs.utils.sram.SRAMTemplate
import coupledL2.PfSource
import prefetch.{PrefetchReq,PrefetchResp,PrefetchTrain,PrefetchEvict,PrefetchParameters,HasPrefetchParameters}
import prefetch.{AccessState,BestOffsetPrefetch,BOPParameters,PrefetchReceiver,PrefetchReceiverParams,PrefetchBundle}

/** multi confidence lookahead prefetch (MCLP)
 * @email huanghualiwood@163.com
 * @version v1.0.0
 * @date 2023-11-25
 * @param fTableEntries filterTable entries 
  
*/




case class MCLPPrefetchParams(
  fTableEntries: Int = 32,
  pTableQueueEntries: Int = 2
)
    extends PrefetchParameters {
  override val hasPrefetchBit: Boolean = true
  override val inflightEntries: Int = 32
}

trait HasMCLPPrefetcherParams extends HasCoupledL2Parameters {
  val hyperPrefetchParams = MCLPPrefetchParams()
  
  val blkAddrBits = fullAddressBits - offsetBits
  val pageAddrBits = fullAddressBits - pageOffsetBits
  val blkOffsetBits = pageOffsetBits - offsetBits
  val blkNums = 1<<blkOffsetBits //64

  val fTableEntries = hyperPrefetchParams.fTableEntries
  val fTagBits = pageAddrBits - log2Up(fTableEntries)
  val pTableQueueEntries = 2
  val fTableQueueEntries = 512

  def get_blockAddr(x:UInt) = x(fullAddressBits-1,offsetBits)
}

abstract class PrefetchBranchV2Module(implicit val p: Parameters) extends Module with HasMCLPPrefetcherParams
abstract class PrefetchBranchV2Bundle(implicit val p: Parameters) extends Bundle with HasMCLPPrefetcherParams

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

class Monitorbuffer[T <: Data](val gen: PrefetchReq,val entries:Int=16)(implicit val p: Parameters)
extends Module with HasCircularQueuePtrHelper with HasMCLPPrefetcherParams{
    val io = IO(new Bundle{
        val enq = Flipped(DecoupledIO(gen))
        val deq = DecoupledIO(gen)
        val used = Output(UInt(log2Up(entries).W))
        val toFilter = DecoupledIO(gen)
        val fromFilter = Flipped(ValidIO(new Bundle {
            val needDrop = Bool()
        }))
    })
    val enq_num = 1
    val deq_num = 1
    class MonitorbufferPtr(implicit p: Parameters) extends CircularQueuePtr[MonitorbufferPtr](entries){}
    val enqPtr = RegInit(0.U.asTypeOf(new MonitorbufferPtr))
    val deqPtr = RegInit(0.U.asTypeOf(new MonitorbufferPtr))

    val skip_deq = WireInit(false.B)
    
    def entry_map[T](fn: Int => T) = (0 until entries).map(fn)
    val entries_valid = RegInit(VecInit(Seq.fill(entries)(false.B)))
    val entries_data = RegInit(VecInit(Seq.fill(entries)(0.U.asTypeOf(gen))))


    val empty = WireInit(isEmpty(enq_ptr = enqPtr, deq_ptr = deqPtr));dontTouch(empty)
    val full  = WireInit(isFull(enq_ptr = enqPtr, deq_ptr = deqPtr));dontTouch(full)

    when(io.enq.valid) {
        enqPtr := enqPtr + 1.U
        when(full && !io.deq.ready) {
            deqPtr := deqPtr + 1.U
        }

        for(i <- 0 until entries){
            when(i.U === enqPtr.value){
                entries_valid(i) := true.B
                entries_data(i) := io.enq.bits
            }
        }
    }
    when(!empty && (io.deq.fire||skip_deq)){
        for(i <- 0 until entries){
            when(i.U === deqPtr.value){
                entries_valid(i) := false.B
            }
        }
        deqPtr := deqPtr + 1.U
    }
    // --------------------------------------------------------------------------------
    // dequeue operation
    // --------------------------------------------------------------------------------
    // 1. firstly qurry filterTable is existing overlapped prefetchReq
    // 2. if existed, directly throw out and dequeue

    val s_idle :: s_qurryFilter :: Nil = Enum(2)
    val state = RegInit(s_idle)
    val (counterValue, counterWrap) = Counter(!empty, 8)
    
    switch(state){
        is(s_idle){
            when(counterWrap){
                state := s_qurryFilter
            }
        }
        is(s_qurryFilter){
            when(io.fromFilter.valid){
                state := s_idle
            }
        }
    }
    skip_deq := io.fromFilter.valid && io.fromFilter.bits.needDrop

    io.toFilter.valid := state === s_qurryFilter && !io.fromFilter.valid
    io.toFilter.bits := entries_data(deqPtr.value)

    io.enq.ready := true.B

    io.deq.valid := io.fromFilter.valid && !io.fromFilter.bits.needDrop && io.deq.ready
    io.deq.bits := entries_data(deqPtr.value)
    io.used := distanceBetween(enqPtr, deqPtr)
}

/** Producer - drives (outputs) valid and bits, inputs ready.
  * @param gen The type of data to enqueue
  */
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
  
}
class FilterTable(parentName:String = "Unknown")(implicit p: Parameters) extends PrefetchBranchV2Module with HasPerfLogging{
  val io = IO(new Bundle() {
    val from_pfQ = Flipped(DecoupledIO(new PrefetchReq))
    val evict = Flipped(DecoupledIO(new PrefetchEvict))
    val from_mlfq1 = Flipped(DecoupledIO(new PrefetchReq))
    val queryResp_mlfq1 = ValidIO(new Bundle {
      val needDrop = Bool()
    })
    val from_sppHintQ = Flipped(DecoupledIO(new PrefetchReq))
    val queryTrain = Flipped(DecoupledIO(new PrefetchTrain))
    val out_trainRedirect = DecoupledIO(new PrefetchTrain)
    val out_mlfq0 = DecoupledIO(new PrefetchReq)
    val out_mlfq1 = DecoupledIO(new PrefetchReq)
    val out_mlfq2 = DecoupledIO(new PrefetchReq)
    val out_hintllc = ValidIO(new PrefetchReq)
  })
  def idx(addr:      UInt) = addr(log2Up(fTableEntries) - 1, 0)
  def tag(addr:      UInt) = addr(pageAddrBits - 1, log2Up(fTableEntries))

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

  def getVecState(isHit:Bool, originV:UInt, trigerId:UInt) = originV | trigerId
  def checkOne(v:UInt) = v === BOP || v === SPP
  def checkTwo(v:UInt) = v === COMMON
  def hasMyself(v:UInt,originV:UInt) = (v & originV) === v
  def hasMerged(v:UInt,originV:UInt) = v =/= originV
  def is_SPPchase(v:UInt,originV:UInt) = hasMyself(v,SPP) && (originV === BOP || originV === (BOP | SMS))
}
  val dupNums = 2

  val req_dups = RegInit(VecInit(Seq.fill(dupNums)(0.U.asTypeOf(Valid(new PrefetchReq)))))

  val req_issue = WireInit(0.U.asTypeOf(DecoupledIO(new PrefetchReq())));dontTouch(req_issue)
  dontTouch(io)
  def trainRespToPrefetchReq(x:DecoupledIO[PrefetchTrain]) = {
    val out = WireInit(0.U.asTypeOf(DecoupledIO(new PrefetchReq())))
    out.valid := x.valid
    out.bits.tag := x.bits.tag
    out.bits.set := x.bits.set
    out.bits.source := x.bits.source
    out.bits.needT := x.bits.needT
    out.bits.pfVec := x.bits.pfVec
    x.ready := out.ready
    out 
  }
  def get_redirectTrain(x:PrefetchReq, redirect_vec:UInt, longest_blkoff: UInt) = {
    val out = WireInit(0.U.asTypeOf(new PrefetchTrain()));dontTouch(out)
    val addr = x.addr + (longest_blkoff << offsetBits.U)
    // out.tag := parseFullAddress(addr)._1
    // out.set := parseFullAddress(addr)._2
    out.tag := x.tag
    out.set := x.set
    out.source := x.source
    out.needT := x.needT
    out.state := AccessState.PREFETCH_HIT
    out.pfVec := redirect_vec
    out
  }
  object ParallelMax {
    def apply[T <: Data](x: Seq[(T, UInt)]): UInt = {
      ParallelOperation(x, (a: (T, UInt), b: (T, UInt)) => {
        val maxV = WireInit(a._1.asUInt)
        val maxIndex = WireInit(a._2)
        when(a._1.asUInt < b._1.asUInt) {
          maxV := b._1
          maxIndex := b._2
        }
        (maxV.asTypeOf(x.head._1), maxIndex)
      })._2
    }
  }
  def find_highest_blkOff(entry: Vec[UInt]): UInt = {
    val highIndex = WireInit(0.U(blkOffsetBits.W)).suggestName("highIndex");
    highIndex := ParallelMax.apply(entry.zipWithIndex.map(x => (x._1 =/= PfSource.NONE, x._2.asUInt)))
    highIndex
  }

  fastArb(Seq(io.from_pfQ,io.from_mlfq1,io.from_sppHintQ,trainRespToPrefetchReq(io.queryTrain)),req_issue)

  val s1_frompfQ = RegNext(io.from_pfQ.fire)
  val s1_from_mlfq1 = RegNext(io.from_mlfq1.fire)
  val s1_from_sppHintQ = RegNext(io.from_sppHintQ.fire)
  val s1_queryTrain = RegNext(io.queryTrain.fire)

  // val req_hint2llc = RegNext(io.from_sppHintQ,false.B)
  req_dups.foreach(x =>  {
    x.valid := req_issue.valid
    x.bits := req_issue.bits
  })
  req_issue.ready := true.B
  val dupOffsetBits = log2Up(fTableEntries/dupNums)
  val dupBits = log2Up(dupNums)
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
  val consensusTable = RegInit(VecInit(Seq.fill(fTableEntries)(0.U.asTypeOf(fTableEntry()))))
  // val consensusTable = Mem(fTableEntries,fTableEntry())
  // val q = Module(new Queue(UInt(fullAddressBits.W), fTableQueueEntries, flow = false, pipe = true)) //TODO: opimize timing
  val evict_q = Module(new SRAMQueue(UInt(blkAddrBits.W),entries = fTableQueueEntries, flow = true, 
    hasMbist = cacheParams.hasMbist, hasClkGate=enableClockGate, hasShareBus = cacheParams.hasShareBus, parentName=parentName+"filterDelayQ"))

  val hit = WireInit(VecInit.fill(dupNums)(false.B))
  val readResult = WireInit(VecInit.fill(dupNums)(0.U.asTypeOf(fTableEntry())));dontTouch(readResult)
  val hitForMap_filtedpfVec = WireInit(VecInit.fill(dupNums)(0.U(PfSource.bits.W)));dontTouch(hitForMap_filtedpfVec)
  val hitForMap_bitVec = WireInit(VecInit.fill(dupNums)(VecInit.fill(blkNums)(false.B)));dontTouch(hitForMap_bitVec)
  val hitForMap_needDrop = WireInit(VecInit.fill(dupNums)(false.B));dontTouch(hitForMap_needDrop)
  val can_send2_mlfq1 = WireInit(VecInit.fill(dupNums)(false.B));dontTouch(can_send2_mlfq1)
  val can_send2_mlfq2 = WireInit(VecInit.fill(dupNums)(false.B));dontTouch(can_send2_mlfq2)
  val anchored_longest_blkOff = WireInit(VecInit.fill(dupNums)(0.U(blkOffsetBits.W)));dontTouch(anchored_longest_blkOff)
  val next_VecState = WireInit(VecInit.fill(dupNums)(0.U(PfVectorConst.bits.W)))

  val wBitMap = WireInit(VecInit.fill(dupNums)(VecInit.fill(blkNums)(0.U(FitlerVecState.bits.W))));dontTouch(wBitMap)
  val wData = WireInit(VecInit.fill(dupNums)(0.U.asTypeOf(fTableEntry())))

  val dup_offset = req_dups(0).bits.set(dupOffsetBits-1+dupBits,dupOffsetBits-1)


  for(i <- 0 until(dupNums)) {
    when(req_dups(i).bits.set(dupOffsetBits-1+dupBits-1,dupOffsetBits-1) === i.U(dupBits.W)) {
      val oldAddr = req_dups(i).bits.addr
      val pageAddr = WireInit(oldAddr(fullAddressBits - 1, pageOffsetBits));dontTouch(pageAddr)
      val blkOffset = WireInit(oldAddr(pageOffsetBits - 1, offsetBits));dontTouch(blkOffset)

      //read cTable
      readResult(i) := consensusTable(idx(pageAddr))
      val trigerId = req_dups(i).bits.pfVec
      hit(i) := readResult(i).valid && tag(pageAddr) === readResult(i).tag

      val anchored_cVec = readResult(i).cVec
      val anchored_value = readResult(i).cVec(blkOffset)
      hitForMap_needDrop(i) := hit(i) && FitlerVecState.hasMerged(req_dups(i).bits.pfVec, anchored_value)
      next_VecState(i) := Mux(hit(i),FitlerVecState.getVecState(true.B, originV = anchored_value, trigerId = req_dups(i).bits.pfVec),req_dups(i).bits.pfVec)
      
      for (j <- 0 until readResult(i).cVec.length){
        when(hit(i)){
            wBitMap(i)(j) := Mux(j.asUInt === blkOffset, next_VecState(i), anchored_cVec(j))
            hitForMap_bitVec(i)(j) := anchored_cVec(j) =/= PfSource.NONE
            hitForMap_filtedpfVec(i) := readResult(i).cVec(blkOffset)
        }.otherwise{
            wBitMap(i)(j) := Mux(j.asUInt === blkOffset, next_VecState(i), PfSource.NONE)
            hitForMap_bitVec(i)(j) := false.B
            hitForMap_filtedpfVec(i) := PfSource.NONE
        }
      }
      anchored_longest_blkOff(i) := OneHot.OH1ToUInt(HighestBit(hitForMap_bitVec(i).asUInt,blkNums))

      // now only considering spp chase bop ,must hit one
      can_send2_mlfq2(i) := !hit(i) && FitlerVecState.is_SPPchase(req_dups(i).bits.pfVec,anchored_value) //TODO has more thing todo!!!
      // should filter when any other prefetchBitVec existed expected L1
      can_send2_mlfq1(i) := !hit(i) || anchored_value === PfSource.NONE //|| anchored_value === PfSource.SMS

      wData(i).valid := true.B
      wData(i).tag := tag(pageAddr)
      wData(i).cVec := wBitMap(i)
    }.otherwise{
      readResult(i) := 0.U.asTypeOf(fTableEntry())
    }
  }
  val widx = WireInit(idx(req_dups(dup_offset).bits.addr(fullAddressBits - 1, pageOffsetBits)(log2Up(fTableEntries)-1,0)));dontTouch(widx)
  when(req_dups(dup_offset).valid) {
      when(hit(dup_offset)){
        consensusTable(widx).cVec := wData(dup_offset).cVec
      }.otherwise{
        consensusTable(widx) := wData(dup_offset)
      }
      
  }

  io.queryResp_mlfq1.valid := s1_from_mlfq1
  io.queryResp_mlfq1.bits.needDrop := hitForMap_needDrop(dup_offset)

  io.out_mlfq0.valid := s1_frompfQ && can_send2_mlfq1.reduce(_ ||_ ) && req_dups(dup_offset).bits.is_l1pf
  io.out_mlfq0.bits := req_dups(dup_offset).bits

  io.out_mlfq1.valid := s1_frompfQ && can_send2_mlfq1.reduce(_ ||_ ) && !io.out_mlfq0.fire 
  io.out_mlfq1.bits := req_dups(dup_offset).bits

  io.out_mlfq2.valid := s1_frompfQ && can_send2_mlfq2.reduce(_ || _)
  io.out_mlfq2.bits := req_dups(dup_offset).bits
  io.out_mlfq2.bits.pfVec := next_VecState(dup_offset)

  // io.out_trainRedirect.valid := s1_queryTrain && ((req_dups(dup_offset).bits.pfVec === PfSource.BOP) || req_dups(dup_offset).bits.is_l1pf)
  io.out_trainRedirect.valid := s1_queryTrain
  io.out_trainRedirect.bits := get_redirectTrain(req_dups(dup_offset).bits, hitForMap_filtedpfVec(dup_offset),anchored_longest_blkOff(dup_offset))

  io.out_hintllc.valid := false.B//req_dups(1) && req_hint2llc
  io.out_hintllc.bits := 0.U.asTypeOf(io.out_hintllc.bits.cloneType) //req_dups(1)

  evict_q.io.enq.valid := req_dups(dup_offset).valid && s1_frompfQ && can_send2_mlfq1.reduce(_ ||_ ) // if spp2llc , don't enq
  evict_q.io.enq.bits := get_blockAddr(req_dups(dup_offset).bits.addr)

  val isqFull = evict_q.io.count === (fTableQueueEntries-1).U
  evict_q.io.deq.ready := isqFull;dontTouch(evict_q.io.deq.ready)

  // --------------------------------------------------------------------------------
  // evict operation
  // --------------------------------------------------------------------------------
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
  readEvict := consensusTable(idx(evictPageAddr))
  hitEvict := evict_q.io.deq.fire && readEvict.valid && tag(evictPageAddr) === readEvict.tag && !conflict

  when(hitEvict) {
    consensusTable(idx(evictPageAddr)).cVec(evictBlkOffset) := consensusTable(idx(evictPageAddr)).cVec(evictBlkOffset) & FitlerVecState.BOP
    // consensusTable(idx(evictPageAddr)).cVec(evictBlkOffset) := FitlerVecState.None //TODO: need further study
  }
  io.evict.ready := true.B
  
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

  io.from_pfQ.ready := true.B

  XSPerfAccumulate("hyper_filter_nums",s1_frompfQ && !(io.out_mlfq2.fire || io.out_mlfq1.fire || io.out_mlfq0.fire))
  XSPerfAccumulate("hyper_filter_input",s1_frompfQ)
  XSPerfAccumulate("hyper_filter_output",io.out_mlfq2.fire || io.out_mlfq1.fire)
  XSPerfAccumulate("hyper_filter_mlfq1",io.out_mlfq1.fire)
  XSPerfAccumulate("hyper_filter_mlfq1_sms",io.out_mlfq1.fire && io.out_mlfq1.bits.pfVec === FitlerVecState.SMS)
  XSPerfAccumulate("hyper_filter_mlfq1_bop",io.out_mlfq1.fire && io.out_mlfq1.bits.pfVec === FitlerVecState.BOP)
  XSPerfAccumulate("hyper_filter_mlfq1_spp",io.out_mlfq1.fire && io.out_mlfq1.bits.pfVec === FitlerVecState.SPP)
  XSPerfAccumulate("hyper_filter_mlfq2",io.out_mlfq2.fire)
  XSPerfAccumulate("hyper_filter_evict_fomMshr",io.evict.fire)
  XSPerfAccumulate("hyper_filter_evict_fromQ",hitEvict)
  XSPerfAccumulate("hyper_filter_trainRedirect",io.out_trainRedirect.fire)

}




/**************************************************************
 * signature path confidence prefetch algorithm
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
************************************************************/

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
  val bpTableEntries = 256

  val pageAddrBits = fullAddressBits - pageOffsetBits
  val blkOffsetBits = pageOffsetBits - offsetBits
  val pTagBits = signatureBits - log2Up(pTableEntries)
  val fTagBits = fullAddressBits - offsetBits - log2Up(fTableEntries)

  val ENABLE_BP = true
  val ENABLE_NL = false

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

  def strideMap4dma(a: SInt): UInt = {
    val out = WireInit(0.U(5.W))
    when(a < -16.S) {
      out := (0.U)(5, 0)
    }.elsewhen(-16.S <= a && a < 16.S) {
      out := (a + 16.S)(5, 0)
    }.otherwise {
      out := 31.U
    }
    out
  }

  // def makeSign(old_sig:UInt,new_delta:SInt)=(old_sig << 3) ^ new_delta.asUInt
  def makeSign(old_sig:UInt,new_delta:UInt)=(old_sig << 3) ^ new_delta.asUInt
}


abstract class SPPBundle(implicit val p: Parameters) extends Bundle with HasSPPParams
abstract class SPPModule(implicit val p: Parameters) extends Module with HasSPPParams with HasPerfLogging 

class SignatureTableReq(implicit p: Parameters) extends SPPBundle {
  val pageAddr = UInt(pageAddrBits.W)
  val blkOffset = UInt(blkOffsetBits.W)
  val needT = Bool()
  val source = UInt(sourceIdBits.W)
  val isBP = Bool()
  val fromGHR_shareBO = SInt(6.W)
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
  def idx(addr:      UInt) = hash1(addr) ^ hash2(addr)
  def tag(addr:      UInt) = addr(sTagBits + log2Up(sTableEntries) - 1, log2Up(sTableEntries))
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
    val tag = UInt(pageAddrBits.W)
    val parent_sig = Vec(1, UInt(signatureBits.W))
    val prePredicted_blkOffset = UInt(blkOffsetBits.W)
  }
  val bpTable = RegInit(VecInit(Seq.fill(bpTableEntries)(0.U.asTypeOf(breakPointEntry()))))

  // --------------------------------------------------------------------------------
  // stage 0
  // --------------------------------------------------------------------------------
  //1. read sTable
  //2. write bpTable
  val s0_valid = io.req.valid
  val s0_req = io.req.bits
  sTable.io.r.req.valid       := s0_valid
  sTable.io.r.req.bits.setIdx := idx(s0_req.pageAddr)

  when(io.s0_bp_update.valid){
    val bp_page = io.s0_bp_update.bits.pageAddr
    bpTable(idx(bp_page)).valid := true.B
    bpTable(idx(bp_page)).tag := bp_page
    for( i <- 0 until(io.s0_bp_update.bits.parent_sig.length)){
        bpTable(idx(bp_page)).parent_sig(i) := io.s0_bp_update.bits.parent_sig(i)
    }
    bpTable(idx(bp_page)).prePredicted_blkOffset := io.s0_bp_update.bits.offset
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
  val s1_bp_access_index = idx(s1_req.pageAddr)(4, 0)
  val s1_bp_hit = WireInit(false.B)
  val s1_bp_mask = WireInit(VecInit(Seq.fill(4)(false.B)))
  val s1_bp_prePredicted_blkOff = WireInit(0.U(blkOffsetBits.W))
  val s1_bp_matched_sig = WireInit(0.U(signatureBits.W))
  val rotate_sig = VecInit(Seq.fill(4)(0.U(signatureBits.W)));dontTouch(rotate_sig)
  for (i <- 0 until (4)) {
    rotate_sig(i) := CircularShift(bpTable(s1_bp_access_index).parent_sig.head).left(3 * i)
    s1_bp_mask(i) := rotate_sig(i) === s1_entryData.signature
  }
  
  s1_bp_hit := ENABLE_BP.asBool && s1_valid && bpTable(s1_bp_access_index).tag === s1_req.pageAddr && s1_bp_mask.reduce(_ || _)
  s1_bp_prePredicted_blkOff := bpTable(s1_bp_access_index).prePredicted_blkOffset
  //TODO: there should set offset for matchedIndex?
  val s1_bp_matchedIdx = WireInit(OneHot.OH1ToUInt(HighestBit(s1_bp_mask.asUInt,4)));dontTouch(s1_bp_matchedIdx)
  s1_bp_matched_sig := rotate_sig(s1_bp_matchedIdx)
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
  val s2_hit = s2_valid && s2_entryData.tag === tag(s2_req.pageAddr)
  // val s2_hit = RegNext(s1_hit,false.B)

  val s2_bp_hit = RegEnable(s1_bp_hit,s1_valid)
  val s2_bp_matched_sig = RegEnable(s1_bp_matched_sig,s1_valid)
  val s2_bp_prePredicted_blkOff = RegEnable(s1_bp_prePredicted_blkOff,s1_valid)
 
  val s2_oldSignature = Mux(s2_hit, s2_entryData.signature, 0.U)
  // used for prefetch hit traning and probe one delta
  val s2_probeDelta   = Mux(s2_req.isBP,s2_oldSignature.head(9).tail(6).asSInt,0.S)
  def get_latest_lastTrigerDelta(now:UInt,origin:UInt):SInt={
    val is_bigger = now > origin
    val out=Mux(is_bigger,(now-origin).asSInt,io.req.bits.fromGHR_shareBO+2.S)
    out
  }
  def get_biggest_blkAddr(now:UInt,origin:UInt):UInt={
    //should set in the same page
    val is_bigger = now > origin
    val out=Mux(is_bigger,now,origin)
    out
  }
  val s2_newDelta     = Mux(s2_hit, get_latest_lastTrigerDelta(s2_req.blkOffset,s2_entryData.lastBlockOff), 0.S) // should hold 0 when miss
  val s2_newBlkAddr   = get_biggest_blkAddr(s2_req.get_blkAddr,Cat(s2_req.pageAddr,s2_entryData.lastBlockOff))

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
  sTable.io.w.req.bits.setIdx := idx(s2_req.pageAddr)
  sTable.io.w.req.bits.data(0).valid := true.B
  sTable.io.w.req.bits.data(0).tag := tag(s2_req.pageAddr)
  //TODO: there should hold strideMap-> delta signal!!
  // sTable.io.w.req.bits.data(0).signature := makeSign(s2_oldSignature,s2_newDelta)
  sTable.io.w.req.bits.data(0).signature := get_predicted_sig(s2_oldSignature,s2_newDelta)
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
    io.resp.bits.block := (s2_newBlkAddr) + s2_bp_prePredicted_blkOff
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

  def idx(addr:      UInt) = addr(log2Up(pTableEntries) - 1, 0)
  def tag(addr:      UInt) = addr(signatureBits - 1, log2Up(pTableEntries))
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
      //-1 slowLookTable(s1_lookCount), use slowLook , relatively conservative query
      //-2 s1_lookCount,  medium level
      //-3 s0_lookCOunt >> 2, very aggressive
      //-4 Mux(q.io.empty, slowLookTable(s1_lookCount), s1_lookCount) ,considering receive queue used situation
    //4. calculate s0_current new data entry

  val s1_continue = WireInit(false.B)
  val s1_first_flag = RegInit(false.B)
  val s1_readResult = WireInit(0.U.asTypeOf(new pTableEntry))
  val s1_maxEntry = WireInit(0.U.asTypeOf(new DeltaEntry))
  val s1_current = WireInit(0.U.asTypeOf(new SignatureTableResp));dontTouch(s1_current)
  val s1_valid = WireInit(false.B)
  val s1_testOffset = WireInit(0.U((pageAddrBits + blkOffsetBits).W))
  val s1_lookCount = RegInit(0.U(lookCountBits.W))
  
  val s0_valid = WireInit((state === s_lookahead0 || state === s_lookahead) && ~s1_valid)
  val s0_current = WireInit(0.U.asTypeOf(new SignatureTableResp));dontTouch(s0_current)
  //| signature | delta | block |

  //forward hold dequeue data
  when(state === s_lookahead){
    s0_current.signature := makeSign(s1_current.signature,strideMap(s1_maxEntry.delta))
  }.otherwise{
    s0_current.signature := issueReq.signature
  }

  when(state === s_lookahead){
    s0_current.delta := s1_maxEntry.delta
    s0_current.block := s1_testOffset //TODO: need opimize?
    s0_current.isBP := false.B
  }.elsewhen(state === s_idle){
    s0_current := q.io.deq.bits
  }.otherwise{
    s0_current := issueReq
  }

  val s0_bp_update = WireInit(false.B)
  io.pt2st_bp.valid := ENABLE_BP.asBool &&  s0_bp_update
  io.pt2st_bp.bits.pageAddr := s0_current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits)
  io.pt2st_bp.bits.parent_sig(0) := s0_current.signature
  io.pt2st_bp.bits.offset := s0_current.block(blkOffsetBits - 1, 0)
  q.io.deq.ready := ~s0_valid

  def slowLookTable(lc: UInt): UInt = {
    Mux(lc >= 1.U && lc <= 4.U, (lc >> 1.U) + 1.U, lc)
  }
  //TODO: need to be optimized !!! some error here
  // val s0_miniCount = slowLookTable(s1_lookCount) // test1
  // val s0_miniCount = s1_lookCount // test2
  val s0_miniCount = Mux(q.io.empty, slowLookTable(s1_lookCount), s1_lookCount) // test3

  pTable.io.r.req.valid := q.io.deq.fire || s1_continue
  pTable.io.r.req.bits.setIdx := idx(s0_current.signature)
  // --------------------------------------------------------------------------------
  // stage 1
  // -------------------------------------------------------------------------------
  //1. calculate value for next update
  s1_valid := RegNext(s0_valid,false.B)
  s1_current := RegEnable(s0_current,s0_valid)
  s1_readResult := pTable.io.r.resp.data(0)
  val s1_lastDelta = WireInit(s1_current.delta)
  s1_maxEntry := s1_readResult.deltaEntries.reduce((a, b) => Mux(a.cDelta >= b.cDelta, a, b))
  //set output
  val s1_delta_list = s1_readResult.deltaEntries.map(x => Mux(x.cDelta > s0_miniCount.asUInt, x.delta, 0.S))
  val s1_delta_list_nl = s1_delta_list.map(_ => 1.S((blkOffsetBits + 1).W))
  val s1_delta_list_checked = s1_delta_list.map(x =>
    Mux((s1_current.block.asSInt + x).asUInt(pageAddrBits + blkOffsetBits - 1, blkOffsetBits) === s1_current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits),
      x, 0.S))
  val s1_hit = WireInit(s1_readResult.valid && tag(s1_current.signature) === s1_readResult.tag)

  when(state === s_lookahead0){
    s1_first_flag := true.B
  }.elsewhen(state === s_lookahead){
    s1_first_flag := false.B
  }

  s1_continue := s1_valid && s1_hit && state === s_lookahead

  val s1_count = WireInit(0.U(4.W));dontTouch(s1_count)
  val s1_exist = s1_readResult.deltaEntries.map(_.delta === s1_lastDelta).reduce(_ || _)
  val s1_temp = s1_readResult.deltaEntries.map(x => Mux(x.delta === s1_lastDelta, (new DeltaEntry).apply(s1_lastDelta, x.cDelta + 1.U), x))
  val s1_smallest: SInt = s1_readResult.deltaEntries.reduce((a, b) => Mux(a.cDelta < b.cDelta, a, b)).delta
  val s1_replaceIdx: UInt = s1_readResult.deltaEntries.indexWhere(a => a.delta === s1_smallest)
  //predict
  val s1_issued = s1_delta_list_checked.map(a => Mux(a =/= 0.S, 1.U, 0.U)).reduce(_ +& _)
  s1_testOffset := Mux(s1_issued =/= 0.U,(s1_current.block.asSInt + s1_maxEntry.delta).asUInt,s1_current.block)
  // val s1_testOffset = (current.block.asSInt + maxEntry.delta).asUInt
  //same page?
  val s1_samePage = (s1_testOffset(pageAddrBits + blkOffsetBits - 1, blkOffsetBits) === s1_current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits))
  enprefetch := s1_valid && s1_hit && s1_issued =/= 0.U && state === s_lookahead

  // --------------------------------------------------------------------------------
  // update paternTable 
  // --------------------------------------------------------------------------------
  //1. when leave lookahead0,hold needed writing data
  val s1_wdeltaEntries = WireInit(VecInit(Seq.fill(pTableDeltaEntries)(0.U.asTypeOf(new DeltaEntry()))))
  when(s1_valid && s1_hit) {
    when(s1_exist) {
      //counter overflow
      when(s1_readResult.count + 1.U === ((1.U << s1_count.getWidth).asUInt - 1.U)) {
        s1_wdeltaEntries := s1_temp.map(x => (new DeltaEntry).apply(x.delta, x.cDelta >> 1.asUInt))
      } .otherwise {
        s1_wdeltaEntries := s1_temp
      }
    } .otherwise {
      //to do replacement
      s1_wdeltaEntries := VecInit.tabulate(s1_readResult.deltaEntries.length) { i =>
        Mux((i.U === s1_replaceIdx), (new DeltaEntry).apply(s1_lastDelta, 1.U), s1_readResult.deltaEntries(i))
      }
    }
    s1_count := s1_wdeltaEntries.map(_.cDelta).reduce(_ + _) //todo: must be optimized!
    //to consider saturate here
  } .otherwise {
    s1_wdeltaEntries(0).delta := s1_lastDelta
    s1_wdeltaEntries(0).cDelta := 1.U
    s1_count := 1.U
  }

  //write pTable
  val write_hold = s1_valid && state === s_lookahead0
  pTable.io.w.req.valid := state === s_updateTable && !issueReq.isBP
  pTable.io.w.req.bits.setIdx := RegEnable(idx(s1_current.signature),write_hold)
  pTable.io.w.req.bits.data(0).valid := true.B
  pTable.io.w.req.bits.data(0).deltaEntries := RegEnable(s1_wdeltaEntries,write_hold)
  pTable.io.w.req.bits.data(0).count := RegEnable(s1_count,write_hold)
  pTable.io.w.req.bits.data(0).tag := RegEnable(tag(s1_current.signature),write_hold)

  io.resp.valid := enprefetch || enprefetchnl
  io.resp.bits.block := s1_current.block
  io.resp.bits.deltas := s1_delta_list_checked
  io.resp.bits.degree := s1_lookCount
  io.resp.bits.source := s1_current.source
  io.resp.bits.needT := s1_current.needT

  when(enprefetchnl) {
    io.resp.bits.deltas := s1_delta_list_nl
  }
  //FSM
  switch(state) {
    is(s_idle) {
      when(q.io.deq.fire) {
        state := s_lookahead0
      }
    }
    is(s_lookahead0) {
      when(s1_valid){
        state := s_lookahead
      }
    }
    is(s_lookahead) {
      when(s1_valid){
        when(s1_continue || s1_first_flag) {
          when(s1_issued =/= 0.U) {
            when(s1_samePage  && (s1_maxEntry.cDelta > s0_miniCount)) {
              s1_lookCount := s1_lookCount + 1.U
            } .otherwise {
              s1_lookCount := 0.U
              state := s_idle
            }
          }.otherwise {
            when(s1_lookCount >= 4.U){
              s0_bp_update := true.B
            }
            s1_lookCount := 0.U
            state := s_updateTable
          }
        } .otherwise {
          when(s1_lookCount <= 1.U) {
            val s1_testOffset = s1_current.block + 1.U
            when(s1_testOffset(pageAddrBits + blkOffsetBits - 1, blkOffsetBits) === s1_current.block(pageAddrBits + blkOffsetBits - 1, blkOffsetBits)) {
              enprefetchnl := ENABLE_NL.B
            }
          }
          s1_lookCount := 0.U
          state := s_updateTable
        }
      }
    }
    is(s_updateTable) {
      state := s_idle
    }
  }

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

  def idx(addr:      UInt) = addr(log2Up(fTableEntries) - 1, 0)
  def tag(addr:      UInt) = addr(fullAddressBits - offsetBits - 1, log2Up(fTableEntries))

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
  readResult := fTable(idx(prefetchBlock))
  hit := readResult.valid && tag(prefetchBlock) === readResult.tag

  when(enresp && !hit) {
    fTable(idx(prefetchBlock)).valid := true.B
    fTable(idx(prefetchBlock)).tag := tag(prefetchBlock)
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
    val from_ghr = Flipped(ValidIO(new Bundle {
        val deadCov_state = UInt(PfcovState.bits.W)
        val hitAcc_state = UInt(PfaccState.bits.W)
        val shareBO = SInt(6.W)
        val global_queue_used = (UInt(6.W))
    }))
  })
  println(s"pageAddrBits: ${pageAddrBits}")
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

  sTable.io.req.valid := io.train.valid // already filtered
  sTable.io.req.bits.pageAddr := pageAddr
  sTable.io.req.bits.blkOffset := blkOffset
  sTable.io.req.bits.needT := false.B//io.train.bits.needT
  sTable.io.req.bits.source := 0.U //io.train.bits.source
  sTable.io.req.bits.isBP := io.train.bits.state === AccessState.PREFETCH_HIT
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
  XSPerfAccumulate( "spp_recv_train", io.train.fire)
  XSPerfAccumulate( "spp_recv_st", sTable.io.resp.fire)
  XSPerfAccumulate( "spp_recv_pt", Mux(pTable.io.resp.fire, pTable.io.resp.bits.deltas.map(a => Mux(a =/= 0.S, 1.U, 0.U)).reduce(_ +& _), 0.U))
  XSPerfAccumulate( "spp_hintReq", io.hint_req.valid)
}

class MCLPPrefetcher(parentName:String = "Unknown")(implicit p: Parameters) extends PrefetchBranchV2Module with HasPerfLogging{
  val io = IO(new Bundle() {
    val train = Flipped(DecoupledIO(new PrefetchTrain))
    val req = DecoupledIO(new PrefetchReq)
    val resp = Flipped(DecoupledIO(new PrefetchResp))
    val evict = Flipped(DecoupledIO(new PrefetchEvict))
    val recv_addr = Flipped(ValidIO(UInt(64.W)))
    val hint2llc = ValidIO(new PrefetchReq)
    // val db_degree = Flipped(ValidIO(UInt(2.W)))
    // val queue_used = Input(UInt(6.W))
  })
  dontTouch(io)
  val trainRedircect = WireInit(0.U.asTypeOf(Decoupled(new PrefetchTrain)))
  val train_q = Module(new Queue(new PrefetchTrain, entries = 4, flow = true, pipe = false))
  val fTable = Module(new FilterTable(parentName + "ftable_"))

  val spp = Module(new SignaturePathPrefetch(parentName = parentName + "spp_")(p.alterPartial({
        case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(SPPParameters()))
  })))
  val bop = Module(new BestOffsetPrefetch()(p.alterPartial({
        case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(BOPParameters()))
  })))
  val sms = Module(new PrefetchReceiver()(p.alterPartial({
        case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(PrefetchReceiverParams()))
  })))

  dontTouch(train_q.io)
  train_q.io.enq <> io.train
  // --------------------------------------------------------------------------------
  // global counter 
  // --------------------------------------------------------------------------------
  // seperate eache prefetcher perf counter
  def get_perfState(perfCounter:UInt, allIssued:UInt, state: UInt)={
    when((perfCounter << 2) > allIssued + allIssued + allIssued) {
      state := 3.U
    } .elsewhen((perfCounter << 1) > allIssued) {
      state := 2.U
    } .elsewhen((perfCounter << 2) > allIssued) {
      state := 1.U
    } .otherwise {
      state := 0.U
    }
  }
  class globalCounter extends  PrefetchBundle{
    val l1pf_hitAcc = UInt(8.W)
    val l1pf_issued = UInt(8.W)
    val l2pf_hitAcc = UInt(8.W)
    val l2pf_issued = UInt(8.W)
    val bop_hitAcc = UInt(8.W)
    val bop_issued = UInt(8.W)
    val spp_hitAcc = UInt(8.W)
    val spp_issued = UInt(8.W)
    val shareBO = SInt(6.W)

    val l1pf_hitAccState = UInt(PfaccState.bits.W)
    val l2pf_hitAccState = UInt(PfaccState.bits.W) 
  }
  val ghr = RegInit(0.U.asTypeOf(new  globalCounter()));dontTouch(ghr)
  val ghr_last = RegInit(0.U.asTypeOf(new  globalCounter()));dontTouch(ghr_last)
  val ghrCounter = Counter(true.B, 2048)
  val ghr_roundReset = WireInit(false.B);dontTouch(ghr_roundReset)
  val ghr_roundCnt = ghrCounter._1
  ghr_roundReset := ghrCounter._2
  val bop_roundMax = 50
  val shareBO_reset = ghr_roundCnt === (bop_roundMax*2).U

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
  val ghrTrain = Mux(trainRedircect.valid,trainRedircect.bits,train_q.io.deq.bits)
  when((train_q.io.deq.fire && train_q.io.deq.bits.state === AccessState.PREFETCH_HIT)||trainRedircect.valid){
    when(ghrTrain.is_l1pf){
      ghr.l1pf_hitAcc := ghr.l1pf_hitAcc + 1.U
    }
    when(ghrTrain.is_l2pf){
      ghr.l2pf_hitAcc := ghr.l2pf_hitAcc + 1.U
    }
    when(ghrTrain.hasBOP){
      ghr.bop_hitAcc := ghr.bop_hitAcc + 1.U
    }
    when(ghrTrain.hasSPP){
      ghr.spp_hitAcc := ghr.spp_hitAcc + 1.U
    }
  }
  when(io.req.fire){
    when(io.req.bits.is_l1pf){
      ghr.l1pf_issued := ghr.l1pf_issued + 1.U
    }
    when(io.req.bits.is_l2pf){
      ghr.l2pf_issued := ghr.l2pf_issued + 1.U
    }
    when(io.req.bits.hasBOP){
      ghr.bop_issued := ghr.bop_issued + 1.U
    }
    when(io.req.bits.hasSPP){
      ghr.spp_issued := ghr.spp_issued + 1.U
    }
  }

  when(ghr_roundReset){
    ghr := 0.U.asTypeOf(new globalCounter())
    ghr_last := ghr
    get_perfState(ghr.l1pf_hitAcc,ghr.l1pf_issued,ghr.l1pf_hitAccState) 
    get_perfState(ghr.l2pf_hitAcc,ghr.l2pf_issued,ghr.l2pf_hitAccState) 
  }

  when(shareBO_reset){
    ghr.shareBO := bop.io.shareBO
  }

  XSPerfHistogram("prefetch_dead_block", deadPfEviction, ghr_roundReset, 0, 200, 10)
  XSPerfHistogram("prefetch_dead_ratio", pf_deadCov_state, ghr_roundReset, 0, 4, 1)
  // XSPerfHistogram("prefetch_hit_block", pfHitacc, ghr_roundReset, 0, 200, 10)
  // XSPerfHistogram("prefetch_hit_ratio", pf_hitAcc_state, ghr_roundReset, 0, 4, 1)

  // --------------------------------------------------------------------------------
  // multi prefetch buffer Queue
  // --------------------------------------------------------------------------------
  val q_bop = Module(new ReplaceableQueueV2(new PrefetchReq, 4))
  val q_spp = Module(new Queue(new PrefetchReq, 4, flow = true, pipe = false))
  val q_sms = Module(new ReplaceableQueueV2(new PrefetchReq, 16))

  // --------------------------------------------------------------------------------
  // multi-level feedback Queue
  // --------------------------------------------------------------------------------
  // | MLFQ_1 | ->
  // | MLFQ_2 | -->
  // | MLFQ_3 | ---> firstly
  // val MLFQ_1 = Module(new Queue(new PrefetchReq, 32, flow = false, pipe = false))
  // val MLFQ_2 = Module(new Queue(new PrefetchReq, 16, flow = false, pipe = false))
  val MLFQ_0 = Module(new ReplaceableQueueV2(new PrefetchReq, 32))
  val MLFQ_1 = Module(new Monitorbuffer(new PrefetchReq, 32))
  val MLFQ_2 = Module(new ReplaceableQueueV2(new PrefetchReq, 8))
  val MLFQ_3 = Module(new Queue(new PrefetchReq, 4,  flow = true,  pipe = false))
  // dontTouch(MLFQ_1.io.used)
  // dontTouch(MLFQ_2.io.used)

  MLFQ_3.io.enq.valid := false.B
  MLFQ_3.io.enq.bits := 0.U.asTypeOf(new PrefetchReq)

  dontTouch(io.req)
  io.req.valid := MLFQ_3.io.deq.valid || MLFQ_2.io.deq.valid || MLFQ_1.io.deq.valid
  io.req.bits := ParallelPriorityMux(
    Seq(
      MLFQ_3.io.deq.valid -> MLFQ_3.io.deq.bits,
      MLFQ_2.io.deq.valid -> MLFQ_2.io.deq.bits,
      MLFQ_1.io.deq.valid -> MLFQ_1.io.deq.bits,
      MLFQ_0.io.deq.valid -> MLFQ_0.io.deq.bits,
    )
  )
  MLFQ_3.io.deq.ready := io.req.ready
  MLFQ_2.io.deq.ready := io.req.ready && !MLFQ_3.io.deq.valid
  MLFQ_1.io.deq.ready := io.req.ready && !MLFQ_3.io.deq.valid && !MLFQ_2.io.deq.valid
  MLFQ_0.io.deq.ready := io.req.ready && !MLFQ_3.io.deq.valid && !MLFQ_2.io.deq.valid && !MLFQ_1.io.deq.valid
  // --------------------------------------------------------------------------------
  // stage 0 
  // --------------------------------------------------------------------------------
  // | q_sms | q_bop | q_spp |
  q_bop.io.enq <> bop.io.req
  q_sms.io.enq <> sms.io.req
  q_spp.io.enq <> spp.io.req

  val fTable_req = WireInit(0.U.asTypeOf(new PrefetchReq))
  fTable_req := ParallelPriorityMux(
    Seq(
      q_spp.io.deq.valid -> q_spp.io.deq.bits,
      q_bop.io.deq.valid -> q_bop.io.deq.bits,
      q_sms.io.deq.valid -> q_sms.io.deq.bits
    )
  )
  // fastArb(Seq(q_bop.io.deq,q_spp.io.deq,q_sms.io.deq),fTable.io.from_pfQ)
  // val (counterValue_MLFQ, counterWrap_MLFQ) = Counter(!q_bop.io.count === 0.U, 8)
  q_spp.io.deq.ready := true.B
  q_bop.io.deq.ready := !q_spp.io.deq.valid
  q_sms.io.deq.ready := !q_bop.io.deq.valid && !q_spp.io.deq.valid

  fTable.io.from_mlfq1.valid := false.B
  fTable.io.from_mlfq1.bits := 0.U.asTypeOf(fTable.io.from_mlfq1.bits.cloneType)

  fTable.io.from_pfQ.valid := q_bop.io.deq.fire || q_spp.io.deq.fire || q_sms.io.deq.fire
  fTable.io.from_pfQ.bits := fTable_req
  fTable.io.from_pfQ.ready := DontCare


  fTable.io.from_mlfq1 <> MLFQ_1.io.toFilter
  MLFQ_1.io.fromFilter <> fTable.io.queryResp_mlfq1

  //directly flow 
  fTable.io.from_sppHintQ <> spp.io.hint_req
  MLFQ_0.io.enq <> fTable.io.out_mlfq0
  MLFQ_1.io.enq <> fTable.io.out_mlfq1
  MLFQ_2.io.enq <> fTable.io.out_mlfq2
  

  // --------------------------------------------------------------------------------
  // train diverter queue
  // --------------------------------------------------------------------------------
  //TODO: is bop needed DEMAND_HIT train?
  // train_bop_q.io.enq.valid := false.B
  trainRedircect <> fTable.io.out_trainRedirect
  val train_bop_q = Module(new Queue(new PrefetchTrain, entries = 2, flow = true, pipe = false))
  val train_spp_q = Module(new Queue(new PrefetchTrain, entries = 2, flow = true, pipe = false))
  // train_bop_q.io.enq.valid := false.B
  // train_bop_q.io.enq.valid := train_q.io.deq.valid 
  train_bop_q.io.enq.valid :=(train_q.io.deq.valid && (train_q.io.deq.bits.hasBOP || train_q.io.deq.bits.hasSMS) && (train_q.io.deq.bits.state === AccessState.MISS)) || 
  (trainRedircect.valid && (trainRedircect.bits.hasBOP || trainRedircect.bits.hasSMS))
  train_bop_q.io.enq.bits := Mux(trainRedircect.valid,trainRedircect.bits,train_q.io.deq.bits)

  // train_spp_q.io.enq.valid := false.B
  // train_spp_q.io.enq.valid := train_q.io.deq.valid 
  train_spp_q.io.enq.valid := (train_q.io.deq.valid && train_q.io.deq.bits.hasSPP && (train_q.io.deq.bits.state === AccessState.MISS)) || 
  (trainRedircect.valid)//&& (trainRedircect.bits.hasSPP))
  train_spp_q.io.enq.bits := Mux(trainRedircect.valid,trainRedircect.bits,train_q.io.deq.bits)

  fTable.io.queryTrain.valid := train_q.io.deq.valid && train_q.io.deq.bits.state === AccessState.PREFETCH_HIT
  fTable.io.queryTrain.bits := train_q.io.deq.bits
  train_q.io.deq.ready := true.B

  trainRedircect.ready := true.B;dontTouch(trainRedircect)
  bop.io.train.valid := train_bop_q.io.deq.valid
  bop.io.train.bits := train_bop_q.io.deq.bits
  train_bop_q.io.deq.ready := bop.io.train.ready

  bop.io.resp.valid := io.resp.valid //&& io.resp.bits.hasBOP
  bop.io.resp.bits := io.resp.bits
  io.resp.ready := bop.io.resp.ready

  spp.io.train.valid := train_spp_q.io.deq.valid
  spp.io.train.bits := train_spp_q.io.deq.bits
  train_spp_q.io.deq.ready := spp.io.train.ready

  spp.io.resp.valid := false.B
  spp.io.resp.bits.tag := 0.U
  spp.io.resp.bits.set := 0.U
  spp.io.resp.bits.pfVec := DontCare
  
  // --------------------------------------------------------------------------------
  // stage 1
  // --------------------------------------------------------------------------------

  spp.io.req.ready := true.B
  bop.io.req.ready := true.B

  sms.io.recv_addr.valid := io.recv_addr.valid
  sms.io.recv_addr.bits := io.recv_addr.bits
  sms.io.req.ready := true.B

  // io.hint2llc := fTable.io.hint2llc;dontTouch(io.hint2llc)
  io.hint2llc := 0.U.asTypeOf(Valid(new PrefetchReq))
  fTable.io.evict.valid := io.evict.valid
  fTable.io.evict.bits := io.evict.bits
  io.evict.ready := fTable.io.evict.ready

  // fTable.io.from_bop := bop.io.req.valid
  dontTouch(io.train.bits)
  io.train.ready := true.B
  spp.io.from_ghr.valid := ghr_roundReset
  spp.io.from_ghr.bits.deadCov_state := pf_deadCov_state
  spp.io.from_ghr.bits.hitAcc_state := ghr.l2pf_hitAccState
  spp.io.from_ghr.bits.shareBO := ghr.shareBO
  spp.io.from_ghr.bits.global_queue_used := MLFQ_1.io.used


  XSPerfAccumulate("spp_recv_train", train_spp_q.io.deq.fire)
  XSPerfAccumulate("bop_send2_queue", q_bop.io.enq.fire)
  XSPerfAccumulate("sms_send2_queue", q_sms.io.enq.fire)
  XSPerfAccumulate("spp_send2_queue", q_spp.io.enq.fire)
  XSPerfAccumulate("mlfq0_enq", MLFQ_1.io.enq.fire)
  XSPerfAccumulate("mlfq1_enq", MLFQ_1.io.enq.fire)
  XSPerfAccumulate("mlfq2_enq", MLFQ_2.io.enq.fire)
  XSPerfAccumulate("mlfq0_deq", MLFQ_1.io.deq.fire)
  XSPerfAccumulate("mlfq1_deq", MLFQ_1.io.deq.fire)
  XSPerfAccumulate("mlfq2_deq", MLFQ_2.io.deq.fire)
}