package coupledL3

import chisel3._
import chisel3.util._
import chipsalliance.rocketchip.config.Parameters
import coupledL3.utils._


class FIFOArbiter[T <: Data](val gen: T, val n: Int, val entries: Int = 5) extends Module {
  val io = IO(new ArbiterIO(gen, n))
  io.chosen <> DontCare

  val arb = Module(new Arbiter(gen, n))

  if(entries != 0) {
    val buffers = Seq.fill(n)(Module(new Queue(gen, entries, flow = true)))

    io.in.zipWithIndex.foreach{ 
      case(in, i) => 
        assert(!(in.valid && !in.ready), "FIFOArbiter cannot unready!")
        in <> buffers(i).io.enq
    }

    arb.io.in.zipWithIndex.foreach{ case (in, i) => in <> buffers(i).io.deq }
    io.out <> arb.io.out

  } else {
    arb.io.in <> io.in
    io.out <> arb.io.out
    io.chosen := arb.io.chosen
  }
}