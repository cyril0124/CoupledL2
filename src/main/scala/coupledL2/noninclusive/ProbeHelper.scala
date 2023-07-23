package coupledL2.noninclusive

import chisel3._
import chisel3.util._
import coupledL2._
import chipsalliance.rocketchip.config.Parameters
import freechips.rocketchip.tilelink.TLMessages._
import freechips.rocketchip.tilelink.TLPermissions._

class ProbeHelper(entries: Int = 5, enqDelay: Int = 1)(implicit p: Parameters) extends L2Module {
  val io = IO(new Bundle() {
    val clientDirResult = Flipped(Valid(new ClientDirResult()))
    val task = DecoupledIO(new TaskBundle)
    val full = Output(Bool())
    val dirConflict = Output(Bool())
  })

  val queue = Module(new Queue(new TaskBundle, entries = entries, pipe = false, flow = false))

  io.full := queue.io.count >= (entries - enqDelay).U

  val dir = io.clientDirResult.bits
  val replacerInfo = io.clientDirResult.bits.replacerInfo
  val probeTask = Wire(new TaskBundle)

  // addr without bankIdx
  val addr = Cat(dir.tag, dir.set(dir.clientSetBits - 1, 0))
  val set = addr(setBits - 1, 0)
  val tag = (addr >> setBits)(tagBits - 1, 0)

  probeTask := DontCare
  probeTask.fromProbeHelper := true.B
  probeTask.opcode := Probe
  probeTask.param := toN
  probeTask.channel := "b010".U
  probeTask.size := log2Up(blockBytes).U
  probeTask.sourceId := DontCare
  probeTask.tag := tag
  probeTask.set := set
  probeTask.off := 0.U
  probeTask.bufIdx := DontCare
  probeTask.needHint.foreach(_ := false.B)
  probeTask.alias.foreach(_ := 0.U)
  probeTask.needProbeAckData := true.B
  probeTask.wayMask := Fill(cacheParams.ways, "b1".U)
  probeTask.dirty := false.B // ignored

  val metaOccupied = dir.metas.zip(dir.hits).map { case (s, hit) => !hit && s.state =/= MetaData.INVALID }
  val dirConflict = !dir.tagMatch() && Cat(metaOccupied).orR()

  io.dirConflict := dirConflict // send to MainPipe

  val formA = replacerInfo.channel === 1.U
  val reqAcquire = formA && (replacerInfo.opcode === AcquirePerm || replacerInfo.opcode === AcquireBlock)

  queue.io.enq.valid := reqAcquire && io.clientDirResult.valid && dirConflict
  queue.io.enq.bits := probeTask
  when(queue.io.enq.valid){ assert(queue.io.enq.ready) }

  io.task <> queue.io.deq
}