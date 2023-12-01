/** *************************************************************************************
 * Copyright (c) 2020-2021 Institute of Computing Technology, Chinese Academy of Sciences
 * Copyright (c) 2020-2021 Peng Cheng Laboratory
 *
 * XiangShan is licensed under Mulan PSL v2.
 * You can use this software according to the terms and conditions of the Mulan PSL v2.
 * You may obtain a copy of Mulan PSL v2 at:
 *          http://license.coscl.org.cn/MulanPSL2
 *
 * THIS SOFTWARE IS PROVIDED ON AN "AS IS" BASIS, WITHOUT WARRANTIES OF ANY KIND,
 * EITHER EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO NON-INFRINGEMENT,
 * MERCHANTABILITY OR FIT FOR A PARTICULAR PURPOSE.
 *
 * See the Mulan PSL v2 for more details.
 * *************************************************************************************
 */

package coupledL2

import chisel3._
import chisel3.util._
import org.chipsalliance.cde.config.Parameters
import coupledL2.utils._
import java.util.ResourceBundle
import xs.utils.sram.SRAMTemplate

// read with block granularity
class MSHRBufRead(implicit p: Parameters) extends L2Bundle {
  val valid = Input(Bool())
  val id = Input(UInt(mshrBits.W))
  val ready = Output(Bool())
  val data = Output(new DSBlock)
  val corrupt = Output(Bool())
}

// write with beat granularity
class MSHRBufWrite(implicit p: Parameters) extends L2Bundle {
  val valid_dups = Input(Vec(mshrsAll, Bool()))
  val beat_sel = Input(UInt(beatSize.W))
  val data = Input(new DSBlock)
  val id = Input(UInt(mshrBits.W))
  val corrupt = Input(Bool())
  val ready = Output(Bool())
}

// TODO: should it have both r/w port?
// MSHR Buffer is used when MSHR needs to save data, so each buffer entry corresponds to an MSHR
class MSHRBuffer(wPorts: Int = 1)(implicit p: Parameters) extends L2Module {
  val io = IO(new Bundle() {
    val r = new MSHRBufRead()
    val w = Vec(wPorts, new MSHRBufWrite)
  })

  val buffer = RegInit(VecInit.tabulate(mshrsAll, beatSize)((_, _) => 0.U.asTypeOf(new DSBeat())))
  val valids = RegInit(VecInit.tabulate(mshrsAll, beatSize)((_, _) => false.B))


  io.w.foreach {
    case w =>
      when (w.valid_dups.reduce(_||_)) {
        w.beat_sel.asBools.zipWithIndex.foreach {
          case (sel, i) =>
            when (sel) { valids(w.id)(i) := true.B }
        }
      }
  }

  when (io.r.valid) {
    valids(io.r.id).foreach(_ := false.B)
  }

  buffer.zipWithIndex.foreach {
    case (block, i) =>
      val wens = VecInit(io.w.map(w => w.valid_dups(i) && w.id === i.U)).asUInt
      if(cacheParams.enableAssert)  assert(PopCount(wens) <= 2.U, "triple write to the same MSHR buffer entry")

      val w_beat_sel = PriorityMux(wens, io.w.map(_.beat_sel))
      val w_data = PriorityMux(wens, io.w.map(_.data))
      val ren = io.r.valid && io.r.id === i.U
      block.zipWithIndex.foreach {
        case (entry, j) =>
          when(wens.orR && w_beat_sel(j)) {
            entry := w_data.data((j + 1) * beatBytes * 8 - 1, j * beatBytes * 8).asTypeOf(new DSBeat)
          }
      }
  }

  io.r.ready := true.B
  io.w.foreach(_.ready := true.B)

  io.r.data.data := RegNext(buffer(io.r.id).asUInt)

  if(dataEccEnable) {
    val corrupts = RegInit(VecInit.tabulate(mshrsAll, beatSize)((_, _) => false.B))

    corrupts.zipWithIndex.foreach{ case(beats, i) => 
      val wens_corrupt = VecInit(io.w.map(w => w.valid_dups(i) && w.id === i.U)).asUInt

      val w_corrupt = PriorityMux(wens_corrupt, io.w.map(_.corrupt))
      require(beats.getWidth == beatSize, s"${beats.getWidth} =/= ${beatSize}")
      
      when(wens_corrupt.orR) {
        beats.foreach( _ := w_corrupt )
      }
    }

    io.r.corrupt := RegNext(corrupts(io.r.id).reduce(_||_))
  } else {
    io.r.corrupt := false.B
  }
}
