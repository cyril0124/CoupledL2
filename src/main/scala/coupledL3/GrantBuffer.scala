package coupledL3

import chisel3._
import chisel3.util._
import utility._
import chipsalliance.rocketchip.config.Parameters
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tilelink.TLMessages._

class InflightGrantEntry(implicit p: Parameters) extends L3Bundle {
  val set   = UInt(setBits.W)
  val tag   = UInt(tagBits.W)
  val sink  = UInt(mshrBits.W)
}

class GrantBuffer(implicit p: Parameters) extends L3Module {
    val io = IO(new Bundle() {
        val d_task = Flipped(DecoupledIO(new Bundle() {
            val task = new TaskBundle()
            val data = new DSBlock()
        }))
        val d = DecoupledIO(new TLBundleD(edgeIn.bundle))
        val e = Flipped(DecoupledIO(new TLBundleE(edgeIn.bundle)))
        val e_resp = Output(new RespBundle)

        val fromReqArb = Input(new Bundle() {
            val status_s1 = new PipeEntranceStatus
        })

        val pipeStatusVec = Flipped(Vec(5, ValidIO(new PipeStatus)))
        val toReqArb = Output(new Bundle() {
            val blockSinkReqEntrance = new BlockInfo()
            val blockMSHRReqEntrance = Bool()
        })
        val grantStatus  = Output(Vec(grantQueueEntries, new GrantStatus))
    })

    class GrantQueueEntry(implicit p: Parameters) extends L3Bundle {
        val task = new TaskBundle()
        val data = new DSBlock()
        val insertIdx = UInt(log2Ceil(grantQueueEntries).W)
    }
    val inflightGrantBuf = RegInit(VecInit(Seq.fill(grantQueueEntries){ 0.U.asTypeOf(Valid(new InflightGrantEntry)) }))
    val inflightGrantBufValidVec = VecInit(inflightGrantBuf.map(_.valid))
    val inflightGrantBufFull = inflightGrantBufValidVec.asUInt.andR

    val grantQueue = Module(new Queue(new GrantQueueEntry, grantQueueEntries, pipe = true, flow = false))
    grantQueue.io.enq.bits.task <> io.d_task.bits.task
    grantQueue.io.enq.bits.data <> io.d_task.bits.data
    grantQueue.io.enq.valid := io.d_task.valid && !inflightGrantBufFull
    io.d_task.ready := grantQueue.io.enq.ready && !inflightGrantBufFull

    val beatValids = RegInit(VecInit.tabulate(grantQueueEntries, beatSize)((_, _) => false.B))
    val blockValids = VecInit(beatValids.map(_.asUInt.orR)).asUInt
    val full = blockValids.andR

    val insertIdx = PriorityEncoder(~blockValids)
    grantQueue.io.enq.bits.insertIdx := insertIdx
    when(io.d_task.fire) {
        beatValids(insertIdx).foreach(_ := true.B)
    }


    val inflightGrantBufInsertIdx = PriorityEncoder(~inflightGrantBufValidVec.asUInt)
    when (io.d_task.fire && io.d_task.bits.task.opcode(2, 1) === Grant(2, 1)) {
        // choose an empty entry
        val entry = inflightGrantBuf(inflightGrantBufInsertIdx)
        entry.valid := true.B
        entry.bits.set   := io.d_task.bits.task.set
        entry.bits.tag   := io.d_task.bits.task.tag
        entry.bits.sink  := io.d_task.bits.task.mshrId
    }
    when (io.e.fire) {
        // compare sink to clear buffer
        val sinkMatchVec = inflightGrantBuf.map(g => g.valid && g.bits.sink === io.e.bits.sink)
        assert(PopCount(sinkMatchVec) === 1.U, "GrantBuf: there must be one and only one match, sink:%d", io.e.bits.sink)
        val bufIdx = OHToUInt(sinkMatchVec)
        inflightGrantBuf(bufIdx).valid := false.B
    }

    io.grantStatus zip inflightGrantBuf foreach {
        case (g, i) =>
        g.valid := i.valid
        g.tag    := i.bits.tag
        g.set    := i.bits.set
    }



    def toTLBundleD(task: TaskBundle, data: UInt = 0.U) = {
        val d = Wire(new TLBundleD(edgeIn.bundle))
        d := DontCare
        d.opcode := task.opcode
        d.param := task.param
        d.size := offsetBits.U
        d.source := task.sourceId
        d.sink := task.mshrId
        d.denied := false.B
        d.data := data
        // d.corrupt := false.B
        d.denied := task.denied
        d.corrupt := task.denied || task.corrupt
        d
    }

    def getBeat(data: UInt, beatsOH: UInt): (UInt, UInt) = {
        // get one beat from data according to beatsOH
        require(data.getWidth == (blockBytes * 8))
        require(beatsOH.getWidth == beatSize)
        // next beat
        val next_beat = ParallelPriorityMux(beatsOH, data.asTypeOf(Vec(beatSize, UInt((beatBytes * 8).W))))
        val selOH = PriorityEncoderOH(beatsOH)
        // remaining beats that haven't been sent out
        val next_beatsOH = beatsOH & ~selOH
        (next_beat, next_beatsOH)
    }


    // handle capacity conflict of GrantBuffer
    // count the number of valid blocks + those in pipe that might use GrantBuf
    // so that GrantBuffer will not exceed capacity
    // val noSpaceForSinkReq = PopCount(Cat(VecInit(io.pipeStatusVec.tail.map { case s =>
    //     s.valid && (s.bits.fromA || s.bits.fromC)
    // }).asUInt, blockValids)) >= mshrsAll.U
    // val noSpaceForMSHRReq = PopCount(Cat(VecInit(io.pipeStatusVec.map { case s =>
    //     s.valid && s.bits.fromA
    // }).asUInt, blockValids)) >= mshrsAll.U

    // io.toReqArb.blockSinkReqEntrance.blockA_s1 := noSpaceForSinkReq
    // io.toReqArb.blockSinkReqEntrance.blockB_s1 := Cat(inflightGrantBuf.map(g => g.valid &&
    //     g.bits.set === io.fromReqArb.status_s1.b_set && g.bits.tag === io.fromReqArb.status_s1.b_tag)).orR
    // //TODO: or should we still Stall B req?
    // // A-replace related rprobe is handled in SourceB
    // io.toReqArb.blockSinkReqEntrance.blockC_s1 := noSpaceForSinkReq
    // io.toReqArb.blockMSHRReqEntrance := noSpaceForMSHRReq

    io.toReqArb.blockSinkReqEntrance.blockA_s1 := false.B
    io.toReqArb.blockSinkReqEntrance.blockB_s1 := false.B
    io.toReqArb.blockSinkReqEntrance.blockC_s1 := false.B
    io.toReqArb.blockMSHRReqEntrance := false.B



    val hasData = grantQueue.io.deq.bits.task.opcode(0)
    val i = grantQueue.io.deq.bits.insertIdx

    io.d.valid := grantQueue.io.deq.valid
    grantQueue.io.deq.ready := io.d.ready && Mux(hasData, PopCount(Cat(beatValids(i))) === 1.U, Cat(beatValids(i)).andR)

    val (beat, next_beatsOH) = getBeat(grantQueue.io.deq.bits.data.data, beatValids(i).asUInt)
    io.d.bits := toTLBundleD(grantQueue.io.deq.bits.task, beat)

    when(io.d.fire) {
        when (hasData) {
            beatValids(i) := VecInit(next_beatsOH.asBools)
        }.otherwise {
            beatValids(i).foreach(_ := false.B)
        }
    }


    io.e.ready := true.B
    io.e_resp := DontCare
    io.e_resp.valid := io.e.valid
    io.e_resp.mshrId := io.e.bits.sink
    io.e_resp.respInfo := DontCare
    io.e_resp.respInfo.opcode := GrantAck
    io.e_resp.respInfo.last := true.B
}