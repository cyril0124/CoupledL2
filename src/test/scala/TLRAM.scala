
package coupledL2

import circt.stage.{ChiselStage, FirtoolOption}
import chisel3.stage.ChiselGeneratorAnnotation
import chisel3._
import chisel3.util._
import org.chipsalliance.cde.config.Parameters
import org.chipsalliance.cde.config._
import chisel3.experimental.ExtModule
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tilelink.TLMessages._
import freechips.rocketchip.tilelink.TLPermissions._
import freechips.rocketchip.diplomacy._
import freechips.rocketchip.util._
import freechips.rocketchip.util.property
import xs.utils
import xs.utils.{MaskExpand, Pipeline, RegNextN}

// class RAMHelper(memByte: BigInt) extends ExtModule with HasExtModuleInline {
//   val DataBits = 64

//   val clk   = IO(Input(Clock()))
//   val en    = IO(Input(Bool()))
//   val rIdx  = IO(Input(UInt(DataBits.W)))
//   val rdata = IO(Output(UInt(DataBits.W)))
//   val wIdx  = IO(Input(UInt(DataBits.W)))
//   val wdata = IO(Input(UInt(DataBits.W)))
//   val wmask = IO(Input(UInt(DataBits.W)))
//   val wen   = IO(Input(Bool()))

//   val verilogLines = Seq(
//     """  module RAMHelper(""",
//     """    input         clk,""",
//     """    input         en,""",
//     """    input  [63:0] rIdx,""",
//     """    output [63:0] rdata,""",
//     """    input  [63:0] wIdx,""",
//     """    input  [63:0] wdata,""",
//     """    input  [63:0] wmask,""",
//     """    input         wen""",
//     """  );""",
//     """  import "DPI-C" function void ram_write_helper (""",
//     """    input  longint    wIdx,""",
//     """    input  longint    wdata,""",
//     """    input  longint    wmask,""",
//     """    input  bit        wen""",
//     """  );""",
//     "",
//     """  import "DPI-C" function longint ram_read_helper (""",
//     """    input  bit        en,""",
//     """    input  longint    rIdx""",
//     """  );""",
//     "",
//     "",
//     """    assign rdata = ram_read_helper(en, rIdx);""",
//     "",
//     """    always @(posedge clk) begin""",
//     """      ram_write_helper(wIdx, wdata, wmask, wen && en);""",
//     """    end""",
//     "",
//     """  endmodule"""
//   )

//   setInline(s"$desiredName.v", verilogLines.mkString("\n"))
// }

class TLRAMErrors(val params: ECCParams, val addrBits: Int) extends Bundle with CanHaveErrors {
  val correctable   = (params.code.canCorrect && params.notifyErrors).option(Valid(UInt(addrBits.W)))
  val uncorrectable = (params.code.canDetect  && params.notifyErrors).option(Valid(UInt(addrBits.W)))
}

class TLRAM(
    address: AddressSet,
    cacheable: Boolean = true,
    executable: Boolean = true,
    atomics: Boolean = false,
    // banks: Int = 1,
    beatBytes: Int = 4, // 32
    ecc: ECCParams = ECCParams(),
    sramReg: Boolean = false, // drive SRAM data output directly into a register => 1 cycle longer response
    val devName: Option[String] = None,
    val dtsCompat: Option[Seq[String]] = None,
    val devOverride: Option[Device with DeviceRegName] = None
  )(implicit p: Parameters) extends DiplomaticSRAM(address, beatBytes, devName, dtsCompat, devOverride)
{
  val eccBytes = ecc.bytes
  val code = ecc.code
  require (eccBytes  >= 1 && isPow2(eccBytes))
  require (beatBytes >= 1 && isPow2(beatBytes))
  require (eccBytes <= beatBytes, s"TLRAM eccBytes (${eccBytes}) > beatBytes (${beatBytes}). Use a WidthWidget=>Fragmenter=>SRAM if you need high density and narrow ECC; it will do bursts efficiently")

  val node = TLManagerNode(Seq(TLSlavePortParameters.v1(
    Seq(TLSlaveParameters.v1(
      address            = List(address),
      resources          = resources,
      regionType         = if (cacheable) RegionType.UNCACHED else RegionType.IDEMPOTENT,
      executable         = executable,
      supportsGet        = TransferSizes(1, beatBytes),
      supportsPutPartial = TransferSizes(1, beatBytes),
      supportsPutFull    = TransferSizes(1, beatBytes),
      supportsArithmetic = if (atomics) TransferSizes(1, beatBytes) else TransferSizes.none,
      supportsLogical    = if (atomics) TransferSizes(1, beatBytes) else TransferSizes.none,
      fifoId             = Some(0))), // requests are handled in order
    beatBytes  = beatBytes,
    minLatency = 1))) // no bypass needed for this device

  val notifyNode = ecc.notifyErrors.option(BundleBridgeSource(() => new TLRAMErrors(ecc, log2Ceil(address.max)).cloneType))

  private val outer = this

  lazy val module = new Impl
  // class Impl extends LazyModuleImp(this) with HasJustOneSeqMem {
  class Impl extends LazyModuleImp(this) {
    val (in, edge) = node.in(0)

    val indexBits = (outer.address.mask & ~(beatBytes-1)).bitCount
    val width = code.width(eccBytes*8)
    val lanes = beatBytes/eccBytes 
    println(s"[TLRAM] width: ${width} lanes:${lanes} indexBits:${indexBits} beatBytes:${beatBytes} eccBytes:${eccBytes}")
    val eccCode = Some(ecc.code)
    val address = outer.address
    val laneDataBits = eccBytes * 8

    /* This block has a three-stage pipeline
     * Stage A is the combinational request from TileLink A channel
     * Stage R corresponds to an accepted request
     * Stage D registers the result of an SRAM read (if any)
     *
     * The TileLink D channel response comes from
     *   - stage D for corected reads or AMOs
     *   - stage R for everything else
     *   - However, to increase maximum operating frequency, the
     *     stage R responses can be configured to come from stage D
     *
     * For sub-ECC granule writes and atomic operations:
     *   - stage A sets up the read for the old data value
     *   - stage R is used to gather the result from SRAM to registers
     *   - stage D corrects ECC, applies the ALU, and sets up SRAM write
     *
     * For super-ECC granule writes:
     *   - stage A sets up the write
     *
     * For reads:
     *   - stage A sets up the read
     *   - stage R drives the uncorrected data with valid based on ECC validity
     *   - stage D sets up the correction, if any
     *
     * When stage D needs to perform a write (AMO, sub-ECC write, or ECC correction):
     *   - there is a WaW or WaR hazard vs. the operation in stage R
     *     - for sub-ECC writes and atomics, we ensure stage R has a bubble
     *     - for ECC correction, we cause stage R to be replayed (and reject stage A twice)
     *   - there is a structural hazard competing with stage A for SRAM access
     *     - stage D always wins (stage A is rejected)
     *   - on ECC correction, there is a structural hazard competing with stage R for the response channel
     *     - stage D always wins (stage R is replayed)
     */

    // D stage registers from R
    val d_full      = RegInit(false.B)
    val d_respond   = Reg(Bool())
    val d_opcode    = Reg(UInt(3.W))
    val d_param     = Reg(UInt(3.W))
    val d_size      = Reg(UInt(edge.bundle.sizeBits.W))
    val d_source    = Reg(UInt(edge.bundle.sourceBits.W))
    val d_read      = Reg(Bool())
    val d_atomic    = Reg(Bool())
    val d_sublane   = Reg(Bool())
    val d_address   = Reg(UInt(edge.bundle.addressBits.W))
    val d_mask      = Reg(UInt(beatBytes.W))
    val d_rmw_data  = Reg(UInt((8*beatBytes).W))
    val d_poison    = Reg(Bool())
    val d_raw_data  = Reg(Vec(lanes, Bits(width.W)))

    // R stage registers from A
    val r_full      = RegInit(false.B)
    val r_opcode    = Reg(UInt(3.W))
    val r_param     = Reg(UInt(3.W))
    val r_size      = Reg(UInt(edge.bundle.sizeBits.W))
    val r_source    = Reg(UInt(edge.bundle.sourceBits.W))
    val r_read      = Reg(Bool())
    val r_atomic    = Reg(Bool())
    val r_sublane   = Reg(Bool())
    val r_address   = Reg(UInt(edge.bundle.addressBits.W))
    val r_mask      = Reg(UInt(beatBytes.W))
    val r_rmw_data  = Reg(UInt((8*beatBytes).W))
    val r_poison    = Reg(Bool())
    val r_raw_data  = Wire(Vec(lanes, Bits(width.W)))

    // Decode raw SRAM output
    val d_decoded       = d_raw_data.map(lane => code.decode(lane))
    val d_corrected     = Cat(d_decoded.map(_.corrected).reverse)
    val d_uncorrected   = Cat(d_decoded.map(_.uncorrected).reverse)
    val d_correctable   = d_decoded.map(_.correctable)
    val d_uncorrectable = d_decoded.map(_.uncorrectable)
    val d_need_fix      = d_correctable.reduce(_ || _)
    val d_lanes         = Cat(Seq.tabulate(lanes) { i => d_mask(eccBytes*(i+1)-1, eccBytes*i).orR }.reverse)
    val d_lane_error    = Cat(d_uncorrectable.reverse) & d_lanes
    val d_error         = d_lane_error.orR

    val r_decoded       = r_raw_data.map(lane => code.decode(lane))
    val r_corrected     = Cat(r_decoded.map(_.corrected).reverse)
    val r_uncorrected   = Cat(r_decoded.map(_.uncorrected).reverse)
    val r_correctable   = r_decoded.map(_.correctable)
    val r_uncorrectable = r_decoded.map(_.uncorrectable)
    val r_need_fix      = r_correctable.reduce(_ || _)
    val r_lanes         = Cat(Seq.tabulate(lanes) { i => r_mask(eccBytes*(i+1)-1, eccBytes*i).orR }.reverse)
    val r_lane_error    = Cat(r_uncorrectable.reverse) & r_lanes
    val r_error         = r_lane_error.orR

    // Out-of-band notification of any faults
    notifyNode.foreach { nnode =>
      nnode.bundle.correctable.foreach { c =>
        c.valid := d_need_fix && d_full && (d_atomic || d_read || d_sublane)
        c.bits  := d_address
      }
      nnode.bundle.uncorrectable.foreach { u =>
        u.valid := d_error && d_full && (d_atomic || d_read || d_sublane)
        u.bits  := d_address
      }
    }

    // What does D-stage want to write-back?
    // Make an ALU if we need one
    val d_updated = if (atomics) {
      val alu = Module(new Atomics(edge.bundle))
      alu.io.write     := false.B
      alu.io.a.opcode  := d_opcode
      alu.io.a.param   := d_param
      alu.io.a.size    := d_size
      alu.io.a.source  := 0.U
      alu.io.a.address := 0.U
      alu.io.a.data    := d_rmw_data
      alu.io.a.mask    := d_mask
      alu.io.a.corrupt := false.B
      alu.io.data_in   := d_corrected
      alu.io.data_out
    } else {
      Cat(Seq.tabulate(beatBytes) { i =>
        val upd = d_mask(i) && !d_read
        val rmw = d_rmw_data (8*(i+1)-1, 8*i)
        val fix = d_corrected(8*(i+1)-1, 8*i) // safe to use, because D-stage write-back always wins arbitration
        Mux(upd, rmw, fix)
      }.reverse)
    }

    // Stage D always wins control of the response channel
    val d_win = d_full && d_respond
    val d_mux = if (sramReg) true.B else d_win
    val out_aad = Mux(d_mux, d_read || d_atomic, r_read || r_atomic)
    in.d.bits.opcode  := Mux(out_aad, TLMessages.AccessAckData, TLMessages.AccessAck)
    in.d.bits.param   := 0.U
    in.d.bits.size    := Mux(d_mux, d_size,   r_size)
    in.d.bits.source  := Mux(d_mux, d_source, r_source)
    in.d.bits.sink    := 0.U
    in.d.bits.denied  := false.B
    in.d.bits.data    := Mux(d_mux, d_corrected, r_uncorrected)
    in.d.bits.corrupt := Mux(d_mux, d_error, r_error) && out_aad

    val mem_active_valid = Seq(property.CoverBoolean(in.d.valid, Seq("mem_active")))
    val data_error = Seq(
      property.CoverBoolean(!d_need_fix && !d_error , Seq("no_data_error")),
      property.CoverBoolean(d_need_fix && !in.d.bits.corrupt, Seq("data_correctable_error_not_reported")),
      property.CoverBoolean(d_error && in.d.bits.corrupt, Seq("data_uncorrectable_error_reported")))

    val error_cross_covers = new property.CrossProperty(Seq(mem_active_valid, data_error), Seq(), "Ecc Covers")
    property.cover(error_cross_covers)

    // Does the D stage want to perform a write?
    // It's important this reduce to false.B when eccBytes=1 && atomics=false && canCorrect=false
    val d_wb = d_full && (d_sublane || d_atomic || (d_read && d_need_fix))
    // Formulate an R response unless there is a data output fix to perform
    // It's important this reduce to false.B for sramReg and true.B for !code.canCorrect
    val r_respond = !sramReg.B && (!r_need_fix || !(r_read || r_atomic))
    // Resolve WaW and WaR hazard when D performs an update (only happens on ECC correction)
    // It's important this reduce to false.B unless code.canDetect
    val r_replay = RegNext(r_full && d_full && d_read && d_need_fix)
    // r_full && d_wb => read ecc fault (we insert a buble for atomic/sublane)
    assert (!(r_full && d_wb) || (d_full && d_read && d_need_fix))

    // Pipeline control
    in.d.valid := (d_full && d_respond) || (r_full && r_respond && !d_wb && !r_replay)
    val d_ready = !d_respond || in.d.ready
    val r_ready = !d_wb && !r_replay && (!d_full || d_ready) && (!r_respond || (!d_win && in.d.ready))
    in.a.ready := !(d_full && d_wb) && (!r_full || r_ready) && (!r_full || !(r_atomic || r_sublane))

    val a_sublane = if (eccBytes == 1) false.B else
      in.a.bits.opcode === TLMessages.PutPartialData ||
      in.a.bits.size < log2Ceil(eccBytes).U
    val a_atomic = if (!atomics) false.B else
      in.a.bits.opcode === TLMessages.ArithmeticData ||
      in.a.bits.opcode === TLMessages.LogicalData
    val a_read = in.a.bits.opcode === TLMessages.Get

    // Forward pipeline stage from R to D
    when (d_ready) { d_full := false.B }
    when (r_full && r_ready) {
      d_full     := true.B
      d_respond  := !r_respond
      d_opcode   := r_opcode
      d_param    := r_param
      d_size     := r_size
      d_source   := r_source
      d_read     := r_read
      d_atomic   := r_atomic
      d_sublane  := r_sublane
      d_address  := r_address
      d_mask     := r_mask
      d_rmw_data := r_rmw_data
      d_poison   := r_poison
      d_raw_data := r_raw_data
    }

    // Forward pipeline stage from A to R
    when (r_ready) { r_full := false.B }
    when (in.a.fire) {
      r_full     := true.B
      r_sublane  := a_sublane
      r_opcode   := in.a.bits.opcode
      r_param    := in.a.bits.param
      r_size     := in.a.bits.size
      r_source   := in.a.bits.source
      r_read     := a_read
      r_atomic   := a_atomic
      r_sublane  := a_sublane
      r_address  := in.a.bits.address
      r_poison   := in.a.bits.corrupt
      r_mask     := in.a.bits.mask
      when (!a_read) { r_rmw_data := in.a.bits.data }
    }

    // Split data into eccBytes-sized chunks:
    val a_data = VecInit(Seq.tabulate(lanes) { i => in.a.bits.data(eccBytes*8*(i+1)-1, eccBytes*8*i) })
    val r_data = VecInit(Seq.tabulate(lanes) { i => r_rmw_data(eccBytes*8*(i+1)-1, eccBytes*8*i) })
    val d_data = VecInit(Seq.tabulate(lanes) { i => d_updated(8*eccBytes*(i+1)-1, 8*eccBytes*i) })

    // Which data chunks get poisoned
    val a_poisonv = VecInit(Seq.fill(lanes) { in.a.bits.corrupt })
    val r_poisonv = VecInit(Seq.fill(lanes) { r_poison })
    val d_poisonv = VecInit(Seq.tabulate(lanes) { i =>
      val upd = d_mask(eccBytes*(i+1)-1, eccBytes*i)
      (!upd.andR && d_uncorrectable(i)) || d_poison // sub-lane writes should not correct uncorrectable
    })

    val a_lanes = Cat(Seq.tabulate(lanes) { i => in.a.bits.mask(eccBytes*(i+1)-1, eccBytes*i).orR }.reverse)

    // SRAM arbitration
    val a_fire = in.a.fire
    val a_ren = a_read || a_atomic || a_sublane
    val r_ren = r_read || r_atomic || r_sublane
    val wen = d_wb || Mux(r_replay, !r_ren, a_fire && !a_ren) // val d_wb = d_full && (d_sublane || d_atomic || (d_read && d_need_fix))
    val ren = !wen && (a_fire || r_replay) // help Chisel infer a RW-port

    val addr   = Mux(d_wb, d_address, Mux(r_replay, r_address, in.a.bits.address))
    val sel    = Mux(d_wb, d_lanes,   Mux(r_replay, r_lanes,   a_lanes))
    val dat    = Mux(d_wb, d_data,    Mux(r_replay, r_data,    a_data))
    val poison = Mux(d_wb, d_poisonv, Mux(r_replay, r_poisonv, a_poisonv))
    val coded  = VecInit((dat zip poison) map { case (d, p) =>
      if (code.canDetect) code.encode(d, p) else code.encode(d)
    })

    val index = Cat(mask.zip((addr >> log2Ceil(beatBytes)).asBools).filter(_._1).map(_._2).reverse)
    // r_raw_data := mem.read(index, ren) holdUnless RegNext(ren)
    // when (wen) { mem.write(index, coded, sel.asBools) }

    // when(RegNext(!reset.asBool && (ren || wen))) {
    //   printf("[TLRAM] addr:0x%x\tindex:0x%x\n", addr, index)
    // }

    val split = beatBytes / 8 // for beatByte = 32-byte ==> split = 4
    val bankByte = 64 // 64-bit
    r_raw_data := RegNext({
      val mems = (0 until split).map {_ => Module(new RAMHelper(bankByte))}
      mems.zipWithIndex map { case (mem, i) =>
        mem.clk   := clock
        mem.en    := !reset.asBool && (ren || wen)
        mem.rIdx  := (index << log2Up(split)) + i.U
        mem.wIdx  := (index << log2Up(split)) + i.U
        mem.wdata := coded.asUInt((i + 1) * 64 - 1, i * 64) // in.w.bits.data((i + 1) * 64 - 1, i * 64) // 0~63, 64~127
        mem.wmask := MaskExpand(sel).asUInt((i + 1) * 64 - 1, i * 64)
        mem.wen   := wen
      }
      val rdata = mems.map {mem => mem.rdata}
      Cat(rdata.reverse).asTypeOf(r_raw_data.cloneType)
    }) holdUnless RegNext(ren)

    // Tie off unused channels
    in.b.valid := false.B
    in.c.ready := true.B
    in.e.ready := true.B
  }
}


// class MemoryRequestHelper(requestType: Int)
//   extends ExtModule(Map("REQUEST_TYPE" -> requestType))
//     with HasExtModuleInline
// {
//   val clock     = IO(Input(Clock()))
//   val reset     = IO(Input(Reset()))
//   val io = IO(new Bundle {
//     val req = Flipped(ValidIO(new Bundle {
//       val addr = UInt(64.W)
//       val id   = UInt(32.W)
//     }))
//     val response = Output(Bool())
//   })

//   val verilogLines = Seq(
//     "import \"DPI-C\" function bit memory_request (",
//     "  input longint address,",
//     "  input int id,",
//     "  input bit isWrite",
//     ");",
//     "",
//     "module MemoryRequestHelper #(",
//     "  parameter REQUEST_TYPE",
//     ")(",
//     "  input             clock,",
//     "  input             reset,",
//     "  input             io_req_valid,",
//     "  input      [63:0] io_req_bits_addr,",
//     "  input      [31:0] io_req_bits_id,",
//     "  output reg        io_response",
//     ");",
//     "",
//     "always @(posedge clock or posedge reset) begin",
//     "  if (reset) begin",
//     "    io_response <= 1'b0;",
//     "  end",
//     "  else if (io_req_valid) begin",
//     "    io_response <= memory_request(io_req_bits_addr, io_req_bits_id, REQUEST_TYPE);",
//     "  end",
//     "  else begin",
//     "    io_response <= 1'b0;",
//     "  end",
//     "end",
//     "",
//     "endmodule"
//   )
//   setInline(s"$desiredName.v", verilogLines.mkString("\n"))
// }

// class MemoryResponseHelper(requestType: Int)
//   extends ExtModule(Map("REQUEST_TYPE" -> requestType))
//     with HasExtModuleInline
// {
//   val clock    = IO(Input(Clock()))
//   val reset    = IO(Input(Reset()))
//   val enable   = IO(Input(Bool()))
//   val response = IO(Output(UInt(64.W)))

//   val verilogLines = Seq(
//     "import \"DPI-C\" function longint memory_response (",
//     "  input bit isWrite",
//     ");",
//     "",
//     "module MemoryResponseHelper #(",
//     "  parameter REQUEST_TYPE",
//     ")(",
//     "  input             clock,",
//     "  input             reset,",
//     "  input             enable,",
//     "  output reg [63:0] response",
//     ");",
//     "",
//     "always @(posedge clock or posedge reset) begin",
//     "  if (reset) begin",
//     "    response <= 64'b0;",
//     "  end",
//     "  else if (!reset && enable) begin",
//     "    response <= memory_response(REQUEST_TYPE);",
//     "  end",
//     " else begin",
//     "    response <= 64'b0;",
//     "  end",
//     "end",
//     "",
//     "endmodule"
//   )
//   setInline(s"$desiredName.v", verilogLines.mkString("\n"))
// }


// trait MemoryHelper { this: Module =>
//   private def requestType(isWrite: Boolean): Int = if (isWrite) 1 else 0
//   private def request(valid: Bool, addr: UInt, id: UInt, isWrite: Boolean): Bool = {
//     val helper = Module(new MemoryRequestHelper(requestType(isWrite)))
//     helper.clock := clock
//     helper.reset := reset
//     helper.io.req.valid := valid
//     helper.io.req.bits.addr := addr
//     helper.io.req.bits.id := id
//     helper.io.response
//   }
//   protected def readRequest(valid: Bool, addr: UInt, id: UInt): Bool =
//     request(valid, addr, id, false)
//   protected def writeRequest(valid: Bool, addr: UInt, id: UInt): Bool =
//     request(valid, addr, id, true)
//   private def response(enable: Bool, isWrite: Boolean): (Bool, UInt) = {
//     val helper = Module(new MemoryResponseHelper(requestType(isWrite)))
//     helper.clock := clock
//     helper.reset := reset
//     helper.enable := enable
//     (helper.response(32), helper.response(31, 0))
//   }
//   protected def readResponse(enable: Bool): (Bool, UInt) =
//     response(enable, false)
//   protected def writeResponse(enable: Bool): (Bool, UInt) =
//     response(enable, true)
// }

class TLRAM_WithDRAMSim3(
    address: AddressSet,
    cacheable: Boolean = true,
    executable: Boolean = true,
    atomics: Boolean = false,
    beatBytes: Int = 4, // 32
    ecc: ECCParams = ECCParams(),
    sramReg: Boolean = false, // drive SRAM data output directly into a register => 1 cycle longer response
    val devName: Option[String] = None,
    val dtsCompat: Option[Seq[String]] = None,
    val devOverride: Option[Device with DeviceRegName] = None
  )(implicit p: Parameters) extends DiplomaticSRAM(address, beatBytes, devName, dtsCompat, devOverride)
{
  val eccBytes = ecc.bytes
  val code = ecc.code
  require (eccBytes  >= 1 && isPow2(eccBytes))
  require (beatBytes >= 1 && isPow2(beatBytes))
  require (eccBytes <= beatBytes, s"TLRAM eccBytes (${eccBytes}) > beatBytes (${beatBytes}). Use a WidthWidget=>Fragmenter=>SRAM if you need high density and narrow ECC; it will do bursts efficiently")

  val node = TLManagerNode(Seq(TLSlavePortParameters.v1(
    Seq(TLSlaveParameters.v1(
      address            = List(address),
      resources          = resources,
      regionType         = RegionType.CACHED,
      executable         = executable,
      supportsAcquireT   = TransferSizes(1, 64),
      supportsAcquireB   = TransferSizes(1, 64),
      fifoId             = None)), // requests are handled in order
    beatBytes  = beatBytes,
    endSinkId = 32,
    minLatency = 1))) // no bypass needed for this device

  val notifyNode = ecc.notifyErrors.option(BundleBridgeSource(() => new TLRAMErrors(ecc, log2Ceil(address.max)).cloneType))

  private val outer = this

  lazy val module = new Impl
  class Impl extends LazyModuleImp(this) with MemoryHelper {
    val (in, edge) = node.in(0)
    dontTouch(in)

    // internal parameters
    val blockBytes = 64
    val splitBytes = 8
    val split = blockBytes / splitBytes
    val nrBeat = blockBytes / beatBytes
    require(nrBeat == 2)
    
    // data width of each ramHelper is 64-bit ==> 8 Bytes
    val ramHelper = Seq.fill(split)(Module(new RAMHelper(8)))

    // memorys for the outstanding request
    val maxOutstanding = 1 << in.a.bits.source.getWidth
    val rdAddrMem = Mem(maxOutstanding, UInt(in.a.bits.address.getWidth.W))
    val wrAddrMem = Mem(maxOutstanding, UInt(in.a.bits.address.getWidth.W))

    // always receive e 
    in.e.ready := true.B

    // edge counters
    val (a_first, a_last, a_done, a_count) = edge.count(in.a)
    val (c_first, c_last, c_done, c_count) = edge.count(in.c)
    val (_, _, d_done, d_count) = edge.count(in.d)

    // channel d counter
    val d_first, d_last = WireInit(false.B)
    val d_counter = RegInit(false.B)

    when(in.d.fire) {
      d_counter := ~d_counter
    }
    d_first := ~d_counter
    d_last := d_counter

    dontTouch(a_first)
    dontTouch(a_last)
    dontTouch(c_first)
    dontTouch(c_last)
    dontTouch(d_first)
    dontTouch(d_last)


    val isAcquireBlock = in.a.bits.opcode === AcquireBlock
    val isAcquirePerm = in.a.bits.opcode === AcquirePerm
    val isAcquire = isAcquireBlock || isAcquirePerm
    val isGet = in.a.bits.opcode === Get
    val isReleaseData = in.c.bits.opcode === ReleaseData
    val isRelease = in.c.bits.opcode === Release
    val isPutFullData = in.a.bits.opcode === PutFullData
    val isPutPartialData = in.a.bits.opcode === PutPartialData
    val isPut = isPutFullData || isPutPartialData
    assert((in.a.valid && (isAcquireBlock || isAcquirePerm || isGet || isPut) ) || !in.a.valid)

    // TODO: Release
    assert(!(in.a.bits.opcode === AcquirePerm && in.a.fire))
    assert(!(in.c.bits.opcode === Release && in.a.fire))
    assert(!(in.a.fire && (in.a.bits.param =/= NtoT && in.a.bits.param =/= NtoB)))
    assert(!(in.c.fire && in.c.bits.param =/= TtoN))
    
    val ren = (isAcquire || isGet) && in.a.fire && a_first
    val wen = (isReleaseData && in.c.fire && c_first) || (isPut && in.a.fire && a_first)
    val en = ren || wen
    val rAddr = Mux(ren, in.a.bits.address, RegEnable(in.a.bits.address, in.a.fire && a_first))
    val rSourceId = Mux(ren, in.a.bits.source, RegEnable(in.a.bits.source, in.a.fire && a_first))
    val wAddr = Mux(wen, in.c.bits.address, RegEnable(in.c.bits.address, in.c.fire && c_first))
    val wSourceId = Mux(wen, in.c.bits.source, RegEnable(in.c.bits.source, in.c.fire && c_first))
    assert(!(ren && wen))


    // save read address, this is used for d resp
    val readReqCounter = RegInit(0.U(log2Ceil(maxOutstanding).W))
    val writeReqCounter = RegInit(0.U(log2Ceil(maxOutstanding).W))
    dontTouch(readReqCounter)
    dontTouch(writeReqCounter)

    val isA = in.a.fire && a_first
    val isC = in.c.fire && c_first
    val isD = in.d.fire && d_first

    // accumulate request counter
    when(isA && isD && in.d.bits.opcode === GrantData) {
      // do nothing
    }.elsewhen(isC && isD && in.d.bits.opcode === ReleaseAck) {
      // do nothing
    }.elsewhen(in.a.fire && a_first) {
      assert(!in.c.fire)

      when(ren && a_first) {
        readReqCounter := readReqCounter + 1.U
        assert(readReqCounter < maxOutstanding.U)
      }
    }.elsewhen(in.c.fire && c_first) {
      assert(!in.a.fire)

      when(wen && c_first) {
        writeReqCounter := writeReqCounter + 1.U
        assert(readReqCounter < maxOutstanding.U)
      }
    }.elsewhen(in.d.fire && d_first) {
      when(in.d.bits.opcode === GrantData) {
        readReqCounter := readReqCounter - 1.U
        assert(readReqCounter > 0.U)
      }
      when(in.d.bits.opcode === ReleaseAck) {
        writeReqCounter := writeReqCounter - 1.U
        assert(writeReqCounter > 0.U)
      }
    }

    when(in.a.fire && a_first) {
      val idx = in.a.bits.source
      rdAddrMem.write(idx, in.a.bits.address)
    }

    when(in.c.fire && c_first) {
      val idx = in.c.bits.source
      wrAddrMem.write(idx, in.c.bits.address)
    }

    
    // check whether DRAM could accept the incoming request
    val readReady, writeReady = WireInit(false.B)
    val readReqNotAccept, writeReqNotAccept = RegInit(false.B)
    val pendingReadNeedReq = !readReady && readReqNotAccept
    val pendingWriteNeedReq = !writeReady && writeReqNotAccept
    readReady := readRequest(ren && !readReady || pendingReadNeedReq, rAddr, rSourceId)
    writeReady := writeRequest(wen && !writeReady || pendingWriteNeedReq, wAddr, wSourceId)

    in.a.ready := !readReqNotAccept
    in.c.ready := !writeReqNotAccept

    when(in.a.fire && a_first) {
      readReqNotAccept := true.B
    }.elsewhen(readReady) {
      readReqNotAccept := false.B
    }
    when(in.c.fire && c_first) {
      writeReqNotAccept := true.B
    }.elsewhen(writeReady) {
      writeReqNotAccept := false.B
    }

    dontTouch(readReady)
    dontTouch(writeReady)

    // deal with dramsim3 respond
    val hasReadReq = readReqCounter =/= 0.U
    val hasWriteReq = writeReqCounter =/= 0.U
    val enableReadResp, enableWriteResp = WireInit(false.B)
    dontTouch(hasReadReq)
    dontTouch(hasWriteReq)
    dontTouch(enableReadResp)
    dontTouch(enableWriteResp)

    val (readRespValid, readRespId) = readResponse(enableReadResp)
    val (writeRespValid, writeRespId) = writeResponse(enableWriteResp)
    assert(!(readRespValid && writeRespValid))
    dontTouch(readRespValid)
    dontTouch(writeRespValid)
    dontTouch(readRespId)
    dontTouch(writeRespId)

    val readRespValidReg = RegInit(false.B)
    val readRespIdReg = RegInit(0.U(in.d.bits.source.getWidth.W))
    enableReadResp := !(readRespValid || readRespValidReg)
    when(readRespValid && !readRespValidReg && (!in.d.fire && d_first || in.d.fire && !d_last)) {
      readRespValidReg := true.B
      readRespIdReg := readRespId
    }.elsewhen(!readRespValid && readRespValidReg && in.d.fire && d_last) {
      readRespValidReg := false.B
    }

    val writeRespValidReg = RegInit(false.B)
    val writeRespIdReg = RegInit(0.U(in.d.bits.source.getWidth.W))
    enableWriteResp := !(writeRespValid || writeRespValidReg)
    when(writeRespValid && !writeRespValidReg && !in.d.fire && d_first) {
      writeRespValidReg := true.B
      writeRespIdReg := writeRespId
    }.elsewhen(!writeRespValid && writeRespValidReg && in.d.fire && d_last) {
      writeRespValidReg := false.B
    }

    val isAcquireRespValid = readRespValid || readRespValidReg
    val isReleaseRespValid = writeRespValid || writeRespValidReg
    dontTouch(isAcquireRespValid)
    dontTouch(isReleaseRespValid)
    in.d.valid := isAcquireRespValid || isReleaseRespValid
    in.d.bits := DontCare
    in.d.bits.opcode := Mux(isAcquireRespValid, GrantData, ReleaseAck)
    in.d.bits.param := Mux(isAcquireRespValid, toT, DontCare)
    in.d.bits.size := log2Ceil(blockBytes).U
    in.d.bits.source := Mux(isAcquireRespValid, Mux(readRespValid, readRespId, readRespIdReg), Mux(writeRespValid, writeRespId, writeRespIdReg))

    // interact with ramHelper
    val rdAddrFromMem = rdAddrMem.read(Mux(readRespValid, readRespId, readRespIdReg))
    dontTouch(rdAddrFromMem)
    val addr = Mux(wen && c_last, in.c.bits.address, rdAddrFromMem)
    val index = Cat(mask.zip((addr >> log2Ceil(beatBytes)).asBools).filter(_._1).map(_._2).reverse)
    val wdata = Cat(RegEnable(in.c.bits.data, in.c.fire && c_first), in.c.bits.data)
    ramHelper.zipWithIndex map { case (mem, i) =>
      mem.clk := clock
      mem.en := !reset.asBool && (isAcquireRespValid && in.d.fire || wen && in.c.fire)
      mem.rIdx := (index << log2Up(split)) + i.U
      mem.wIdx := (index << log2Up(split)) + i.U

      mem.wdata := wdata((i + 1) * 64 - 1, i * 64)
      mem.wmask := MaskExpand("b11111111".U)
      mem.wen := wen
    }
    val rdata_1 = Cat(ramHelper.map( mem => mem.rdata ).reverse).asUInt
    val rdata_2 = rdata_1.asTypeOf(Vec(nrBeat, UInt(beatBytes.W)))
    in.d.bits.data := rdata_2(d_last)
  }
}


object TLRAM
{
  def apply(
    address: AddressSet,
    cacheable: Boolean = true,
    executable: Boolean = true,
    atomics: Boolean = false,
    beatBytes: Int = 32,
    ecc: ECCParams = ECCParams(),
    sramReg: Boolean = false,
    devName: Option[String] = None,
    dynamicLatency: Boolean = false
  )(implicit p: Parameters): TLInwardNode =
  {
    val ram = if(!dynamicLatency) {
      LazyModule(new TLRAM(address, cacheable, executable, atomics, beatBytes, ecc, sramReg, devName)).node
    } else {
      LazyModule(new TLRAM_WithDRAMSim3(address, cacheable, executable, atomics, beatBytes, ecc, sramReg, devName)).node
    }
    ram
  }
}

class TestTopTLRAM()(implicit p: Parameters) extends LazyModule {
  
  val blockBytes = 64
  val beatBytes = 32

  val client = TLClientNode(Seq(
      TLMasterPortParameters.v2(
        masters = Seq(
          TLMasterParameters.v1(
            name = "client",
            sourceId = IdRange(0, 32),
            supportsProbe = TransferSizes(64)
          )
        ),
        channelBytes = TLChannelBeatBytes(32),
      )
  ))

  val ram = TLRAM(AddressSet(0, 0xffffffffffL), beatBytes = 32, dynamicLatency = true)

  val mem_xbar = TLXbar()

  // ram :=
  //   mem_xbar :=*
  //   TLXbar() :=*
  //   TLFragmenter(32, 64) :=*
  //   TLBuffer.chainNode(2) :=*
  //   TLCacheCork() :=
  //   client

  ram := TLDelayer(0.2) := TLBuffer.chainNode(2) := TLDelayer(0.2) := client

  lazy val module = new Impl
  class Impl extends LazyModuleImp(this) {
    val io = IO(new Bundle{
      val test = Input(Bool())
    })

    client.makeIOs()(ValName("master_port"))

    dontTouch(io)
  }

}

object TestTopTLRAM extends App
{
    println("hello from TestTopTLRAM")

    val config = new Config(Parameters.empty)
    
    // EnableMonitors DisableMonitors
    val top = DisableMonitors(p => LazyModule(new TestTopTLRAM()(p)))(config)

    (new ChiselStage).execute(Array("--target", "verilog") ++ args, Seq(
      FirtoolOption("-O=release"),
      FirtoolOption("--disable-all-randomization"),
      FirtoolOption("--disable-annotation-unknown"),
      FirtoolOption("--strip-debug-info"),
      FirtoolOption("--lower-memories"),
      FirtoolOption("--lowering-options=noAlwaysComb," +
        " disallowPortDeclSharing, disallowLocalVariables," +
        " emittedLineLength=120, explicitBitcast, locationInfoStyle=plain," +
      " disallowExpressionInliningInPorts, disallowMuxInlining"),
      ChiselGeneratorAnnotation(() => top.module),
    ))
}