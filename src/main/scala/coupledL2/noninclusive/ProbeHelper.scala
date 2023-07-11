package coupledL2.noninclusive

import chisel3._
import chisel3.util._
import coupledL2._
import chipsalliance.rocketchip.config.Parameters
import freechips.rocketchip.tilelink.TLMessages._
import freechips.rocketchip.tilelink.TLPermissions._

class ProbeHelper(entries: Int = 5, enqDelay: Int = 1)(implicit p: Parameters) extends L2Module {
  val io = IO(new Bundle() {
    val dirResult = Flipped(Valid(new ClientDirResult()))
    val task = DecoupledIO(new TaskBundle)
    val full = Output(Bool())
  })

  val queue = Module(new Queue(new TaskBundle, entries = entries, pipe = false, flow = false))

  io.full := queue.io.count >= (entries - enqDelay).U

  val dir = io.dirResult.bits
  val replacerInfo = io.dirResult.bits.replacerInfo
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
  probeTask.dirty := false.B // ignored

  val meta_hits = dir.metas.zip(dir.hits).map { case (s, hit) => !hit && s.state =/= MetaData.INVALID }
  val dir_conflict = !dir.tagMatch() && Cat(meta_hits).orR()

  val formA = replacerInfo.channel === 1.U
  val req_acquire = formA && (replacerInfo.opcode === AcquirePerm || replacerInfo.opcode === AcquireBlock)

  queue.io.enq.valid := req_acquire && io.dirResult.valid && dir_conflict
  queue.io.enq.bits := probeTask
  when(queue.io.enq.valid){ assert(queue.io.enq.ready) }

  io.task <> queue.io.deq
//  io.task.valid := false.B // TODO:
}