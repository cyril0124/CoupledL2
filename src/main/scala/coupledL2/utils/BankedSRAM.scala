package coupledL2.utils

import chisel3._
import chisel3.util._
import org.chipsalliance.cde.config.Parameters
import xs.utils.mbist.MBISTPipeline
import xs.utils.sram._


// divide SRAM into n banks
// use lower-bits of setIdx to select bank
// allow parallel accesses to different banks
class BankedSRAM[T <: Data]
(
  gen: T, sets: Int, ways: Int, n: Int = 1,
  shouldReset: Boolean = false, holdRead: Boolean = false,
  singlePort: Boolean = false, bypassWrite: Boolean = false,
  clk_div_by_2: Boolean = false,
  enableClockGate: Boolean = false,
  hasMbist: Boolean = false, hasShareBus: Boolean = false,
  parentName:String = "Unknown"
)(implicit p:Parameters) extends Module {
  val io = IO(new Bundle() {
    val r = Flipped(new SRAMReadBus(gen, sets, ways))
    val w = Flipped(new SRAMWriteBus(gen, sets, ways))
  })

  val innerSet = sets / n
  val bankBits = log2Ceil(n)
  val innerSetBits = log2Up(sets) - bankBits
  val r_setIdx = io.r.req.bits.setIdx.head(innerSetBits)
  val r_bankSel = if(n == 1) 0.U else io.r.req.bits.setIdx(bankBits - 1, 0)
  val w_setIdx = io.w.req.bits.setIdx.head(innerSetBits)
  val w_bankSel = if(n == 1) 0.U else io.w.req.bits.setIdx(bankBits - 1, 0)

  val banks = (0 until n).map{ i =>
    val ren = if(n == 1) true.B else i.U === r_bankSel
    val wen = if(n == 1) true.B else i.U === w_bankSel
    val sram = Module(new SRAMTemplate(
      gen, innerSet, ways,
      shouldReset = shouldReset, holdRead = holdRead,
      singlePort = singlePort, bypassWrite = bypassWrite,
      clk_div_by_2 = clk_div_by_2,
      hasMbist = hasMbist,
      hasShareBus = hasShareBus,
      hasClkGate = enableClockGate,
      parentName = parentName + s"bank${i}_"
    ))
    sram.io.r.req.valid := io.r.req.valid && ren
    sram.io.r.req.bits.apply(r_setIdx)
    sram.io.w.req.valid := io.w.req.valid && wen
    sram.io.w.req.bits.apply(io.w.req.bits.data, w_setIdx, io.w.req.bits.waymask.getOrElse(1.U))
    sram
  }

  val mbistPl = MBISTPipeline.PlaceMbistPipeline(1,
    s"${parentName}_mbistPipe",
    hasMbist && hasShareBus
  )

  // resp data sel
  val ren_sel_0 = UIntToOH(r_bankSel)
  val ren_sel_1 = RegNext(ren_sel_0, 0.U.asTypeOf(ren_sel_0))
  val ren_sel = if(clk_div_by_2){
    RegNext(ren_sel_1, 0.U.asTypeOf(ren_sel_0))
  } else ren_sel_1
  // resp data valid
  val resp_data_valid_0 = Mux1H(ren_sel_0, banks.map(_.io.r.req.fire))
  val resp_data_valid_1 = RegNext(resp_data_valid_0, false.B)
  val resp_data_valid = if(clk_div_by_2){
    RegNext(resp_data_valid_1, false.B)
  } else resp_data_valid_1

  // only one read/write
  // assert({PopCount(ren_vec) <= 1.U})
  // assert({PopCount(Cat(banks.map(_.io.r.req.fire))) <= 1.U})

  // block read when there is write request of the same bank
  io.r.req.ready := Cat(banks.map(s => s.io.r.req.ready && !s.io.w.req.valid).reverse)(r_bankSel)
  // TODO: r.ready low when w.valid is also guaranteed in SRAMTemplate
  val r_resp_data = WireInit(0.U.asTypeOf(io.r.resp.data))
  when(resp_data_valid){
    r_resp_data := Mux1H(ren_sel, banks.map(_.io.r.resp.data))
  }
  io.r.resp.data := r_resp_data

  io.w.req.ready := Cat(banks.map(_.io.w.req.ready).reverse)(w_bankSel)

}
