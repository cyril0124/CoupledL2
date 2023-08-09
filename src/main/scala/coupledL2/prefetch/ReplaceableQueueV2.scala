package coupledL2.utils

import chisel3._
import chisel3.util._
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

  //XSPerfHistogram(cacheParams, "nrWorkingPfQueueEntries", 
  //  PopCount(valids), true.B, 0, inflightEntries, 1)
}