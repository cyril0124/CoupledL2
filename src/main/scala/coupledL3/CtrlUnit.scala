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

import chipsalliance.rocketchip.config.Parameters
import chisel3._
import chisel3.util._
import freechips.rocketchip.tilelink.{TLAdapterNode, TLRegisterNode}
import freechips.rocketchip.diplomacy.{AddressSet, LazyModule, LazyModuleImp, SimpleDevice}
import freechips.rocketchip.regmapper._

// CtrlUnit deal with CBO.INVAL、CBO.CLEAN、CBO.FLUS  CBO.ZERO
class CtrlUnit(val node: TLAdapterNode)(implicit p: Parameters)
  extends LazyModule with HasCoupledL3Parameters {
  val ctlnode = TLRegisterNode(
    address = Seq(AddressSet(cacheParams.ctrl.get.address, 0xffff)), // 寄存器的基地址
    device = new SimpleDevice("cache-controller", Nil),
    beatBytes = 8,
    concurrency = 1
  )
  val num_cores = cacheParams.ctrl.get.numCores
  val device = new SimpleDevice("L3CacheCtrl", Seq("xiangshan,cache_ctrl"))
  lazy val module = new CtrlUnitImp(this)
}

class CtrlUnitImp(wrapper: CtrlUnit)(implicit p: Parameters)  extends LazyModuleImp(wrapper) {
  val cacheParams = wrapper.p(L3ParamKey)

  val io_req = IO(DecoupledIO(new CtrlReq()))
  val req = io_req

  val node = wrapper.node
  val ctlnode = wrapper.ctlnode

  // valid & ready
  val cmd_in_valid = RegInit(false.B)
  val cmd_in_ready = WireInit(false.B)
  val cmd_out_valid = RegInit(false.B)
  val cmd_out_ready = WireInit(false.B)
  when(cmd_out_ready) {
    cmd_out_valid := false.B
  }
  when(cmd_in_ready) {
    cmd_in_valid := false.B
  }

  // reg
  val ctl_tag = RegInit(0.U(64.W))
  val ctl_set = RegInit(0.U(64.W))
  val ctl_way = RegInit(0.U(64.W))
  val ctl_cmd = RegInit(0.U(64.W))

  // reg map
  ctlnode.regmap(
    0x00 -> Seq(RegField.w(64, RegWriteFn((ivalid, oready, data) => {
      when(ivalid) {
        cmd_in_valid := true.B
      }
      when(oready) {
        cmd_out_ready := true.B
      }
      when(ivalid && !cmd_in_valid) {
        ctl_cmd := data
      }
      (!cmd_in_valid, cmd_out_valid)
    }))),
//    0x00 -> Seq(RegField(64, ctl_cmd)),
    0x08 -> Seq(RegField(64, ctl_tag)),
    0x10 -> Seq(RegField(64, ctl_set)),
    0x18 -> Seq(RegField(64, ctl_way)),
  )

  // req
  req.valid := cmd_in_valid
  cmd_in_ready := req.ready
  req.bits.cmd := ctl_cmd
  req.bits.tag := ctl_tag
  req.bits.set := ctl_set
  req.bits.way := ctl_way
  when(req.fire()){
    cmd_out_valid := true.B
  }

//  // req -> C task
//  val ctrlTask = Wire(new TaskBundle)
//  ctrlTask := DontCare
//  ctrlTask.fromCtrlUnit := true.B
//  ctrlTask.set := req.bits.set
//  ctrlTask.tag := req.bits.tag
//  ctrlTask.off := 0.U
//  ctrlTask.opcode := Release
//  ctrlTask.param := req.bits.cmd
//  ctrlTask.channel := "b100".U
//  ctrlTask.size := log2Up(cacheParams.blockBytes).U
//  ctrlTask.sourceId := DontCare
//  ctrlTask.bufIdx := DontCare
//  ctrlTask.needHint.foreach(_ := false.B)
//  ctrlTask.alias.foreach(_ := 0.U)
//  ctrlTask.needProbeAckData := false.B
//  ctrlTask.wayMask := Fill(cacheParams.ways, "b1".U)
//  ctrlTask.dirty := false.B // ignored
//
//  // toReqArb
//  req.ready := toReqArb.ready
//  toReqArb.valid := req.valid
//  toReqArb.bits := ctrlTask
}


class CtrlReq() extends Bundle {
  val cmd = UInt(8.W)
  val set = UInt(64.W)
  val tag = UInt(64.W)
  val way = UInt(64.W)
}


//object CacheCMD {
//  def CMD_R_S_TAG = 0.U(8.W)
//  def CMD_R_C_TAG = 1.U(8.W)
//  def CMD_R_DATA = 2.U(8.W)
//  def CMD_R_S_DIR = 3.U(8.W)
//  def CMD_R_C_DIR = 4.U(8.W)
//  def CMD_W_S_TAG = 5.U(8.W)
//  def CMD_W_C_TAG = 6.U(8.W)
//  def CMD_W_DATA = 7.U(8.W)
//  def CMD_W_S_DIR = 8.U(8.W)
//  def CMD_W_C_DIR = 9.U(8.W)
//  def CMD_CMO_INV = (0 + 16).U(8.W)
//  def CMD_CMO_CLEAN = (1 + 16).U(8.W)
//  def CMD_CMO_FLUSH = (2 + 16).U(8.W)
//}

// CBO.INVAL CBO.CLEAN、CBO.FLUS  CBO.ZERO
object CMO{
  /*
    Invalidates the cache line.
    Does not write the data back to the memory.
   */
  def CBO_INVAL = 0.U
  /*
    Clears the cache line’s dirty state.
    Keeps the cache line’s valid state.
    If the cache line is valid and dirty, data is written back to the memory.
   */
  def CBO_CLEAN = 1.U
  /*
    Invalidates the cache line.
    Writes the data back to the memory if the cache line is valid and dirty; otherwise, ignores the data.
   */
  def CBO_FLUS = 2.U
  /*
    set data block zero
   */
  def CBO_ZERO = 3.U

  def needT(isCmo: Bool ,cmo: UInt): Bool = {
    isCmo && (cmo === CBO_CLEAN || cmo === CBO_ZERO)
  }
}