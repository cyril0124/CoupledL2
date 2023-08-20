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
import chisel3.util.log2Ceil
import freechips.rocketchip.diplomacy.BufferParams
import freechips.rocketchip.tilelink._
import freechips.rocketchip.util._
import chipsalliance.rocketchip.config.Field
import huancun.CacheParameters
import coupledL3.prefetch._
import MemReqSource._
import utility.ReqSourceKey

// General parameter key of CoupledL3
case object L3ParamKey extends Field[L3Param](L3Param())

// L1 Cache Params, used for TestTop generation
case class L2ClientParam
(
  name: String = "L20",
  sets: Int = 32,
  ways: Int = 8,
  blockBytes: Int = 64,
  aliasBitsOpt: Option[Int] = None,
) {
  val capacity = sets * ways * blockBytes
  val setBits = log2Ceil(sets)
  val offsetBits = log2Ceil(blockBytes)
  val needResolveAlias = aliasBitsOpt.nonEmpty
}

// Indicate alias bit of upper level cache
case object AliasKey extends ControlKey[UInt]("alias")
case class AliasField(width: Int) extends BundleField(AliasKey) {
  override def data: UInt = Output(UInt(width.W))
  override def default(x: UInt): Unit = {
    x := 0.U(width.W)
  }
}

// Indicate whether Hint is needed by upper level cache
// case object PrefetchKey extends ControlKey[Bool](name = "needHint")
// case class PrefetchField() extends BundleField(PrefetchKey) {
//   override def data: Bool = Output(Bool())
//   override def default(x: Bool): Unit = {
//     x := false.B
//   }
// }

// Indicate whether this block is dirty or not (only used in handle Release/ReleaseData)
// Now it only works for non-inclusive cache (ignored in inclusive cache)
case object DirtyKey extends ControlKey[Bool](name = "blockisdirty")

case class DirtyField() extends BundleField(DirtyKey) {
  override def data: Bool = Output(Bool())
  override def default(x: Bool): Unit = {
    x := true.B
  }
}

case class L3Param
(
  name: String = "L3",
  ways: Int = 4,
  sets: Int = 128,
  dirNBanks: Int = 4,
  dsNBanks: Int = 4,
  blockBytes: Int = 64,
  pageBytes: Int = 4096,
  channelBytes: TLChannelBeatBytes = TLChannelBeatBytes(32),
  clientCaches: Seq[CacheParameters] = Nil,
  replacement: String = "plru",
  mshrs: Int = 16,
  grantQueueEntries: Int = 8,
  enableClockGate: Boolean = true,
  dataEccCode: Option[String] = Some("secded"), // Option: "none", "identity", "parity", "sec", "secded"
  
  inclusionPolicy: String = "NINE", // inclusive, NINE(Non-inclusive Non-exclusive)
  releaseData: Int = 3,
  /* 0 for dirty alone
   * 1 for dirty and accessed
   * 2 for all except prefetch & !accessed
   * 3 for all
   */

  enableDebug: Boolean = true,
  enableHalfFreq: Boolean = false,

  // Client (these are set in Configs.scala in XiangShan)
  echoField: Seq[BundleFieldBase] = Nil,
  reqField: Seq[BundleFieldBase] = Nil, 
  respKey: Seq[BundleKeyBase] = Nil,
  // Manager
  // reqKey: Seq[BundleKeyBase] = Seq(AliasKey, PrefetchKey, ReqSourceKey),
  // reqKey: Seq[BundleKeyBase] = Seq(AliasKey, ReqSourceKey),
  reqKey: Seq[BundleKeyBase] = Seq(AliasKey),
  respField: Seq[BundleFieldBase] = Nil,

  innerBuf: TLBufferParams = TLBufferParams(),
  outerBuf: TLBufferParams = TLBufferParams(
    a = BufferParams.default,
    // b = BufferParams.default,
    b = BufferParams.none,
    c = BufferParams.none,
    d = BufferParams.default,
    e = BufferParams.default
  ),

  hartIds: Seq[Int] = Seq[Int](),
  // Prefetch
  prefetch: Option[PrefetchParameters] = None,
  // Performance analysis
  enablePerf: Boolean = true,
  // Monitor
  enableMonitor: Boolean = false,
  // TopDown
  elaboratedTopDown: Boolean = false
) {
  def toCacheParams: CacheParameters = CacheParameters(
    name = name,
    sets = sets,
    ways = ways,
    blockGranularity = log2Ceil(sets),
    blockBytes = blockBytes
  )
}

case object EdgeInKey extends Field[TLEdgeIn]

case object EdgeOutKey extends Field[TLEdgeOut]

case object BankBitsKey extends Field[Int]
