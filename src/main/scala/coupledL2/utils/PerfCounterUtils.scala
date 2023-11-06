/***************************************************************************************
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
***************************************************************************************/

package coupledL2.utils

import org.chipsalliance.cde.config.Parameters
import chisel3._

class PerfEvent extends Bundle {
  val value = UInt(6.W)
}

trait HasPerfEvents { this: RawModule =>
  val perfEvents: Seq[(String, UInt)]

  lazy val io_perf: Vec[PerfEvent] = IO(Output(Vec(perfEvents.length, new PerfEvent)))
  def generatePerfEvent(noRegNext: Option[Seq[Int]] = None): Unit = {
    for (((out, (name, counter)), i) <- io_perf.zip(perfEvents).zipWithIndex) {
      require(!name.contains("/"))
      out.value := RegNext(RegNext(counter))
      if (noRegNext.isDefined && noRegNext.get.contains(i)) {
        out.value := counter
      }
    }
  }
  def getPerfEvents: Seq[(String, UInt)] = {
    perfEvents.map(_._1).zip(io_perf).map(x => (x._1, x._2.value))
  }
  def getPerf: Vec[PerfEvent] = io_perf
}
