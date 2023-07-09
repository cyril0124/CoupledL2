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
import java.util.ResourceBundle
import xs.utils.sram._

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
  val valid = Input(Bool())
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

  val buffer = Seq.fill(mshrsAll) {
    Seq.fill(beatSize) {
      Module(new SRAMTemplate(new DSBeat(), set = 1, way = 1, singlePort = true, hasMbist = false, hasClkGate = false))
    }
  }
  val valids = RegInit(VecInit(Seq.fill(mshrsAll) {
    VecInit(Seq.fill(beatSize)(false.B))
  }))
  val corrupts = RegInit(VecInit(Seq.fill(mshrsAll) {
    VecInit(Seq.fill(beatSize)(false.B))
  }))

  io.w.foreach {
    case w =>
      when (w.valid) {
        w.beat_sel.asBools.zipWithIndex.foreach {
          case (sel, i) =>
            when (sel) { valids(w.id)(i) := true.B }
        }
      }
  }

  when (io.r.valid) {
    // TODO: When the acquireperm is sent and grant is received, refillBuf does not contain data.
    //  Therefore, refill buffer should be blocked from being read.

    // assert(valids(io.r.id).asUInt.andR, "[%d] attempt to read an invalid entry", io.r.id)
    valids(io.r.id).foreach(_ := false.B)
    if(dataEccEnable) {
      corrupts.zipWithIndex.foreach{ case(beats, i) => 
        require(beats.getWidth == beatSize, s"${beats.getWidth} =/= ${beatSize}")
        
        when(io.r.id === i.U) {
          beats.asTypeOf(Vec(beatSize, Bool())).foreach( _ := false.B ) 
        }
      }
    }
  }

  buffer.zipWithIndex.foreach {
    case (block, i) =>
      val wens = VecInit(io.w.map(w => w.valid && w.id === i.U)).asUInt
      assert(PopCount(wens) <= 1.U, "multiple write to the same MSHR buffer entry wens:0x%x", wens)

      val w_beat_sel = PriorityMux(wens, io.w.map(_.beat_sel))
      val w_data = PriorityMux(wens, io.w.map(_.data))
      val w_corrupt = PriorityMux(wens, io.w.map(_.corrupt))
      val ren = io.r.valid && io.r.id === i.U
      block.zipWithIndex.foreach {
        case (entry, j) =>
          entry.io.w.req.valid := wens.orR && w_beat_sel(j)
          entry.io.w.req.bits.apply(
            data = w_data.data((j + 1) * beatBytes * 8 - 1, j * beatBytes * 8).asTypeOf(new DSBeat),
            setIdx = 0.U,
            waymask = 1.U
          )
          entry.io.r.req.valid := ren
          entry.io.r.req.bits.apply(0.U)

          if(dataEccEnable) corrupts(i)(j) := w_corrupt
      }
  }

  io.r.ready := true.B
  io.w.foreach(_.ready := true.B)

  val ridReg = RegNext(io.r.id, 0.U.asTypeOf(io.r.id))
  io.r.data.data := VecInit(buffer.map {
    case block => VecInit(block.map(_.io.r.resp.data.asUInt)).asUInt
  })(ridReg)
  
  if(dataEccEnable) {
    io.r.corrupt := VecInit( corrupts.map( entry => entry.reduce(_ || _) ) )(ridReg)
  } else {
    io.r.corrupt := false.B
  }
}
