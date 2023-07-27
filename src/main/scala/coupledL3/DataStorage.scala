/** *************************************************************************************
 * Copyright (c) 2020-2021 Institute of Computing Technology, Chinese Academy of Sciences
 * Copyright (c) 2020-2021 Peng Cheng Laboratory
 *
 * XiangShan is licensed under Mulan PSL v2.
 * You can use this software according to the terms and conditions of the Mulan PSL v2.
 * You may obtain a copy of Mulan PSL v2 at:
 * http://license.coscl.org.cn/MulanPSL2
 *
 * THIS SOFTWARE IS PROVIDED ON AN "AS IS" BASIS, WITHOUT WARRANTIES OF ANY KIND,
 * EITHER EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO NON-INFRINGEMENT,
 * MERCHANTABILITY OR FIT FOR A PARTICULAR PURPOSE.
 *
 * See the Mulan PSL v2 for more details.
 * *************************************************************************************
 */

package coupledL3

import chisel3._
import chisel3.util._
// import coupledL3.utils.SRAMTemplate
import xs.utils.sram.SRAMTemplate
import xs.utils.Code
import utility.RegNextN
import chipsalliance.rocketchip.config.Parameters
import firrtl.Utils
import xs.utils.Decoding
import java.awt.image.DataBuffer

class DSRequest(implicit p: Parameters) extends L3Bundle {
  val way = UInt(wayBits.W)
  val set = UInt(setBits.W)
  val wen = Bool()
}

class DSBeat(implicit p: Parameters) extends L3Bundle {
  val data = UInt((beatBytes * 8).W)
}

class DSBlock(implicit p: Parameters) extends L3Bundle {
  val data = UInt((blockBytes * 8).W)
}

class DataStorage(implicit p: Parameters) extends L3Module with DontCareInnerLogic {
  val io = IO(new Bundle() {
    // there is only 1 read or write request in the same cycle,
    // so only 1 req port is necessary
    val req = Flipped(ValidIO(new DSRequest))
    val rdata = Output(new DSBlock)
    val wdata = Input(new DSBlock)
    val error = Output(Bool())
  })

  // Seperate the whole block of data into several banks, each bank contains 8 bytes(64-bit).
  // For every bank, we attach ECC protection bits.
  require(blockBytes % 8 == 0)
  val bankBytes = 8
  val banks = blockBytes / bankBytes // 64 / 8 = 8

  def dataCode: Code = Code.fromString(dataEccCode)
  val dataEccBits = dataCode.width(bankBytes * 8) - bankBytes * 8
  println(s"Data ECC bits:$dataEccBits")

  val dataEccArray = if (dataEccBits > 0) {
    Some(
      Module(new SRAMTemplate(
        gen = Vec(banks, UInt((dataEccBits).W)), 
        set = blocks,
        singlePort = true,
        hasMbist = false,
        hasClkGate = enableClockGate
      ))
    )
  } else None


  val array = Module(new SRAMTemplate(
    gen = new DSBlock,
    set = blocks,
    way = 1,
    singlePort = true,
    hasMbist = false,
    hasClkGate = enableClockGate
  ))

  array.io.r <> DontCare
  array.io.w <> DontCare

  val arrayIdx = Cat(io.req.bits.way, io.req.bits.set)
  val wen = io.req.valid && io.req.bits.wen
  val ren = io.req.valid && !io.req.bits.wen
  array.io.w.apply(wen, io.wdata, arrayIdx, 1.U)
  array.io.r.apply(ren, arrayIdx)

  // io.rdata := RegNextN(array.io.r.resp.data(0), sramLatency - 1)

  if (dataEccBits > 0) {
    val bankWrDataVec = io.wdata.asTypeOf(Vec(banks, UInt((bankBytes*8).W)))
    
    val dataEccRdData = Wire(Vec(banks, UInt((dataEccBits).W)))
    val dataEccWrData = Cat( (0 until banks).map{ bank => 
                                val t = dataCode.encode(bankWrDataVec(bank))
                                require(t.asUInt.getWidth == (dataEccBits + bankBytes * 8))
                                t.head(dataEccBits)
                              }.reverse
                            ).asTypeOf( Vec(banks, UInt((dataEccBits).W)) )
    dataEccArray.get.io.w.apply(wen, dataEccWrData, arrayIdx, 1.U)
    dataEccArray.get.io.r.apply(ren, arrayIdx)

    // We have only one way
    dataEccRdData := RegNextN(dataEccArray.get.io.r.resp.data(0), sramLatency - 1).asTypeOf(Vec(banks, UInt((dataEccBits).W)))

    val rdDataRaw = RegNextN(array.io.r.resp.data(0), sramLatency - 1) // DSBlock
    val rdData = rdDataRaw.data.asTypeOf(Vec(banks, UInt((bankBytes*8).W)))
    val dataEccErrVec = dataEccRdData.zip(rdData).map{ case(e, d) => 
                            dataCode.decode(e ## d).error
                        }
    val dataEccCorrVec = dataEccRdData.zip(rdData).map{ case(e, d) => 
                                    dataCode.decode(e ## d).correctable
                          }
    val corrDataVec = dataEccRdData.zip(rdData).map{ case(e, d) => 
                          dataCode.decode(e ## d).corrected
                      }
    require(Cat(corrDataVec).asUInt.getWidth == rdDataRaw.data.asUInt.getWidth, s"${Cat(corrDataVec).asUInt.getWidth} =/= ${rdDataRaw.data.asUInt.getWidth}")
    
    def toDSBlock(x: Seq[UInt]): DSBlock = {
      val dsBlock = Wire(new DSBlock)
      dsBlock.data := Cat(x.reverse)
      dsBlock
    }

    io.error := Cat(Cat(dataEccErrVec) & ~Cat(dataEccCorrVec)).orR
    io.rdata := toDSBlock(corrDataVec)
  } else {
    io.error := false.B
    io.rdata := RegNextN(array.io.r.resp.data(0), sramLatency - 1)
  }

  assert(RegNext(!io.error), "For now, we won't ECC error happen in DataStorage...")
}
