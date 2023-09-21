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

package coupledL2

import chisel3._
import chisel3.util._
import xs.utils.sram.SRAMTemplate
import utility.RegNextN
import chipsalliance.rocketchip.config.Parameters
import coupledL2.utils.BankedSRAM
import xs.utils.Code

class DSRequest(implicit p: Parameters) extends L2Bundle {
  val way = UInt(wayBits.W)
  val set = UInt(setBits.W)
  val wen = Bool()
}

class DSBeat(implicit p: Parameters) extends L2Bundle {
  val data = UInt((beatBytes * 8).W)
}

class DSBlock(implicit p: Parameters) extends L2Bundle {
  val data = UInt((blockBytes * 8).W)
}

class DataStorage(implicit p: Parameters) extends L2Module {
  val io = IO(new Bundle() {
    // there is only 1 read or write request in the same cycle,
    // so only 1 req port is necessary
    val req = Flipped(ValidIO(new DSRequest))
    val rdata = Output(new DSBlock)
    val wdata = Input(new DSBlock)
    val error = Output(Bool()) // TODO: ECC
  })

  val array  = Module(new BankedSRAM(new DSBlock, blocks, 1, cacheParams.dsNBanks, singlePort = true, enableClockGate = enableClockGate))

  // read
  val arrayIdx = Cat(io.req.bits.way, io.req.bits.set)
  val ren = io.req.valid && !io.req.bits.wen
  array.io.r.apply(ren, arrayIdx)

  // write
  val wReqReg = RegNext(io.req)
  val wDataReg = RegEnable(io.wdata, io.req.valid && io.req.bits.wen)
  val wArrayIdx = Cat(wReqReg.bits.way, wReqReg.bits.set)
  val wen = wReqReg.valid && wReqReg.bits.wen
  array.io.w.apply(wen, wDataReg, wArrayIdx, 1.U)

  val wrSameTime = ren && wen
  dontTouch(wrSameTime)
  assert(!wrSameTime, "Wraning: write and read same time, wReq_set:%d wReq_way:%d rReq_set:%d rReq_way:%d\n", wReqReg.bits.set, wReqReg.bits.way, io.req.bits.set, io.req.bits.way)

  // Seperate the whole block of data into several banksECC, each bank contains 8 bytes(64-bit).
  // For every bank, we attach ECC protection bits.
  require(blockBytes % 8 == 0)
  val bankBytes = 32
  val banksECC = blockBytes / bankBytes // 64 / 32 = 2

  def dataCode: Code = Code.fromString(dataEccCode)
  val dataEccBits = dataCode.width(bankBytes * 8) - bankBytes * 8
  println(s"Data ECC bits:$dataEccBits Banks: $banksECC Blocks: $blocks")

  val dataEccArray = if (dataEccBits > 0) {
    Some(
      Module(new BankedSRAM(Vec(banksECC, UInt((dataEccBits).W)), blocks, 1, cacheParams.dsNBanks, singlePort = true, hasMbist = false, enableClockGate = enableClockGate))
    )
  } else None

  if (dataEccBits > 0) {
    val bankWrDataVec = io.wdata.asTypeOf(Vec(banksECC, UInt((bankBytes*8).W)))
    
    val dataEccRdData = Wire(Vec(banksECC, UInt((dataEccBits).W)))
    val dataEccWrData = Cat( (0 until banksECC).map{ bank => 
                                val t = dataCode.encode(bankWrDataVec(bank))
                                require(t.asUInt.getWidth == (dataEccBits + bankBytes * 8))
                                t.head(dataEccBits)
                              }.reverse
                            ).asTypeOf( Vec(banksECC, UInt((dataEccBits).W)) )
    dataEccArray.get.io.w.apply(wen, dataEccWrData, arrayIdx, 1.U)
    dataEccArray.get.io.r.apply(ren, arrayIdx)

    // We have only one way
    dataEccRdData := RegNextN(dataEccArray.get.io.r.resp.data(0), sramLatency - 1).asTypeOf(Vec(banksECC, UInt((dataEccBits).W)))

    val rdDataRaw = RegNextN(array.io.r.resp.data(0), sramLatency - 1) // DSBlock
    val rdData = rdDataRaw.data.asTypeOf(Vec(banksECC, UInt((bankBytes*8).W)))
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

    io.error := false.B // TODO: ECC: Cat(Cat(dataEccErrVec) & ~Cat(dataEccCorrVec)).orR
//    io.rdata := RegNextN(array.io.r.resp.data(0), sramLatency - 1) // TODO: ECC: toDSBlock(corrDataVec)
    io.rdata := RegEnable(array.io.r.resp.data(0), RegNext(ren))
    // TODO: ECC
    // when(~reset.asBool) {
    //   assert(RegNext(!io.error), "For now, we won't ECC error happen in DataStorage...")
    // }
  } else {
    io.error := false.B
//    io.rdata := RegNextN(array.io.r.resp.data(0), sramLatency - 1)
    io.rdata := RegEnable(array.io.r.resp.data(0), RegNext(ren))
  }

}
