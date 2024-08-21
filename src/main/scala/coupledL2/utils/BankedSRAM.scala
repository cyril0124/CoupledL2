package coupledL2.utils

import chisel3._
import chisel3.util._
import org.chipsalliance.cde.config.Parameters
import xs.utils.mbist.MbistPipeline
import xs.utils.sram._


// divide SRAM into n banks
// use lower-bits of setIdx to select bank
// allow parallel accesses to different banks
class BankedSRAM[T <: Data]
(
  gen: T, sets: Int, ways: Int, n: Int = 1,
  shouldReset: Boolean = false, holdRead: Boolean = false,
  singlePort: Boolean = false, bypassWrite: Boolean = false,
  multicycle: Int = 1,
  hasMbist: Boolean = false,
  foundry:  String = "Unknown",
  sramInst: String = "STANDARD"
)(implicit p:Parameters) extends Module {
  val io = IO(new Bundle() {
    val r = Flipped(new SRAMReadBus(gen, sets, ways))
    val w = Flipped(new SRAMWriteBus(gen, sets, ways))
  })

  private val innerSet = sets / n
  private val bankBits = log2Ceil(n)
  private val innerSetBits = log2Up(sets) - bankBits
  private val r_setIdx = io.r.req.bits.setIdx.head(innerSetBits)
  private val r_bankSel = if(n == 1) 0.U else io.r.req.bits.setIdx(bankBits - 1, 0)
  private val w_setIdx = io.w.req.bits.setIdx.head(innerSetBits)
  private val w_bankSel = if(n == 1) 0.U else io.w.req.bits.setIdx(bankBits - 1, 0)

  val banks = (0 until n).map{ i =>
    val ren = if(n == 1) true.B else i.U === r_bankSel
    val wen = if(n == 1) true.B else i.U === w_bankSel
    val sram = Module(new SRAMTemplate(
      gen = gen,
      set = innerSet,
      way = ways,
      shouldReset = shouldReset, holdRead = holdRead,
      singlePort = singlePort, bypassWrite = bypassWrite,
      multicycle = multicycle,
      hasMbist = hasMbist,
      foundry = foundry,
      sramInst = sramInst
    ))
    sram.io.r.req.valid := io.r.req.valid && ren
    sram.io.r.req.bits.apply(r_setIdx)
    sram.io.w.req.valid := io.w.req.valid && wen
    sram.io.w.req.bits.apply(io.w.req.bits.data, w_setIdx, io.w.req.bits.waymask.getOrElse(1.U))
    sram
  }
  private val mbistPl = MbistPipeline.PlaceMbistPipeline(1, place = hasMbist)
  // resp data sel
  private val renBd = Wire(Valid(UInt(n.W)))
  renBd.valid := io.r.req.fire
  renBd.bits := UIntToOH(r_bankSel)
  private val renBdFinal = Pipe(renBd, multicycle)
  io.r.req.ready := Cat(banks.map(s => s.io.r.req.ready).reverse)(r_bankSel)
  io.r.resp.data := Mux1H(renBdFinal.bits & Fill(n, renBdFinal.valid), banks.map(_.io.r.resp.data))
  io.w.req.ready := Cat(banks.map(_.io.w.req.ready).reverse)(w_bankSel)
}
