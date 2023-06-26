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
import chipsalliance.rocketchip.config.Parameters
import coupledL2.utils._
import xs.utils.sram._

// read with block granularity
class LookupBufRead(implicit p: Parameters) extends L2Bundle {
  val valid = Input(Bool())
  val id = Input(UInt(lookupBufBits.W))
  val data = Output(new DSBlock)
  val corrupt = Output(Bool())
}

// write with beat granularity
class LookupBufWrite(implicit p: Parameters) extends L2Bundle {
  val valid = Input(Bool())
  val id = Input(UInt(lookupBufBits.W))
  val beat_sel = Input(UInt(beatSize.W))
  val data = Input(new DSBlock)
  val corrupt = Input(Bool())
}


class LookupBuffer(entries: Int = 16)(implicit p: Parameters) extends L2Module {
  val io = IO(new Bundle{
    val r = new LookupBufRead()
    val w = new LookupBufWrite()
    val full = Output(Bool())
  })


  val buffer = Seq.fill(entries) {
    Seq.fill(beatSize) {
      Module(new SRAMTemplate(new DSBeat(), set = 1, way = 1, singlePort = true, hasMbist = false, hasClkGate = false))
    }
  }
  val valids = RegInit(VecInit(Seq.fill(entries) {
    VecInit(Seq.fill(beatSize)(false.B))
  }))
  val corrupts = RegInit(VecInit(Seq.fill(entries) {
    VecInit(Seq.fill(beatSize)(false.B))
  }))

  io.full := Cat(valids.map( e => Cat(e).andR )).andR()


  when(io.w.valid) {
    io.w.beat_sel.asBools.zipWithIndex.foreach {
      case (sel, i) =>
        when(sel) {
          valids(io.w.id)(i) := true.B
        }
    }
  }

  when(io.r.valid) {
    valids(io.r.id).foreach(_ := false.B)

    if (dataEccEnable) {
      corrupts.zipWithIndex.foreach {
        case (beats, i) =>
          require(beats.getWidth == beatSize, s"${beats.getWidth} =/= ${beatSize}")

          when(io.r.id === i.U) {
            beats.asTypeOf(Vec(beatSize, Bool())).foreach(_ := false.B)
          }
      }
    }
  }


  buffer.zipWithIndex.foreach{
    case (buf, i) =>
      buf.zipWithIndex.foreach{
        case (entry, j) =>
          entry.io.w.req.valid := io.w.valid && io.w.beat_sel(j)
          entry.io.w.req.bits.apply(
            data = io.w.data.data((j + 1) * beatBytes * 8 - 1, j * beatBytes * 8).asTypeOf(new DSBeat),
            setIdx = 0.U,
            waymask = 1.U
          )
          entry.io.r.req.valid := io.r.valid
          entry.io.r.req.bits.apply(0.U)
      }
  }


  val ridReg = RegNext(io.r.id, 0.U.asTypeOf(io.r.id))
  io.r.data.data := VecInit(buffer.map {
    case block => VecInit(block.map(_.io.r.resp.data.asUInt)).asUInt
  })(ridReg)

  if (dataEccEnable) {
    io.r.corrupt := VecInit(corrupts.map(entry => entry.reduce(_ || _)))(ridReg)
  } else {
    io.r.corrupt := false.B
  }
}