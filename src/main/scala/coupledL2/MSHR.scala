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
import coupledL2.MetaData._
import utility.{ParallelLookUp, ParallelPriorityMux}
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tilelink.TLMessages._
import freechips.rocketchip.tilelink.TLPermissions._
import chipsalliance.rocketchip.config.Parameters
import coupledL2.prefetch.PrefetchTrain
import coupledL2.utils.XSPerfAccumulate

class MSHRTasks(implicit p: Parameters) extends L2Bundle {
  // outer
  val source_a = DecoupledIO(new SourceAReq) // To AcquireUnit  // TODO: no need to use decoupled handshake
  val source_b = DecoupledIO(new SourceBReq)
  val mainpipe = DecoupledIO(new TaskBundle) // To Mainpipe (SourceC or SourceD)
  // val prefetchTrain = prefetchOpt.map(_ => DecoupledIO(new PrefetchTrain)) // To prefetcher
}

class MSHRResps(implicit p: Parameters) extends L2Bundle {
  val sink_c = Flipped(ValidIO(new RespInfoBundle))
  val sink_d = Flipped(ValidIO(new RespInfoBundle))
  val sink_e = Flipped(ValidIO(new RespInfoBundle))
  // make sure that Acquire is sent after Release,
  // so resp from SourceC is needed to initiate Acquire
  val source_c = Flipped(ValidIO(new RespInfoBundle))
}

class MSHR(implicit p: Parameters) extends L2Module {
  val io = IO(new Bundle() {
    val id = Input(UInt(mshrBits.W))
    val status = ValidIO(new MSHRStatus)
    val toReqBuf = ValidIO(new MSHRBlockAInfo)
    val alloc = Flipped(ValidIO(new MSHRRequest))
    val tasks = new MSHRTasks()
    val resps = new MSHRResps()
    val nestedwb = Input(new NestedWriteback)
    val nestedwbData = Output(Bool())
  })

  val initState = Wire(new FSMState())
  val state = RegInit(new FSMState(), initState)
  initState.elements.foreach(_._2 := true.B)
  val dirResult = RegInit(0.U.asTypeOf(new DirResult()))

  val gotT = RegInit(false.B) // TODO: L3 might return T even though L2 wants B
  val gotDirty = RegInit(false.B)
  val gotGrantData = RegInit(false.B)

  val probeDirty = RegInit(false.B)
  val probeGotN = RegInit(false.B)

  // nested C info
  val nestedRelease = RegInit(false.B)
  val nestedReleaseClientOH = RegInit(0.U(clientBits.W))

  val timer = RegInit(0.U(64.W)) // for performance analysis

  /* MSHR Allocation */
  val status_reg = RegInit(0.U.asTypeOf(Valid(new MSHRStatus())))
  val req        = status_reg.bits
  val reqClientOH = getClientBitOH(req.source)
  val clientsExceptReqClientOH = dirResult.meta.clients & ~reqClientOH 
  val meta       = dirResult.meta
  
  assert(PopCount(reqClientOH) <= 1.U)

  when(io.alloc.valid) {
    status_reg.valid := true.B
    state       := io.alloc.bits.state
    dirResult   := io.alloc.bits.dirResult
    val msTask   = io.alloc.bits.task
    req.channel := msTask.channel
    req.tag     := msTask.tag
    req.set     := msTask.set
    req.off     := msTask.off
    req.way     := msTask.way
    req.opcode  := msTask.opcode
    req.param   := msTask.param
    req.size    := msTask.size
    req.source  := msTask.sourceId
    req.needProbeAckData := msTask.needProbeAckData
    req.alias.foreach(_  := msTask.alias.getOrElse(0.U))
    req.aliasTask.foreach(_ := msTask.aliasTask.getOrElse(false.B))
    req.pbIdx   := msTask.pbIdx
    req.fromL2pft.foreach(_ := msTask.fromL2pft.get)
    req.reqSource := msTask.reqSource
    gotT        := false.B
    gotDirty    := false.B
    gotGrantData := false.B
    probeDirty  := false.B
    probeGotN   := false.B
    nestedRelease     := false.B
    nestedReleaseClientOH := 0.U
    timer       := 1.U
  }

  /* ======== Enchantment ======== */
  val meta_pft = meta.prefetch.getOrElse(false.B)
  val meta_no_client = !meta.clients.orR

  val req_needT = needT(req.opcode, req.param) // Put / Acquire.NtoT / Acquire.BtoT / Hint.prefetch_write
  val req_acquire = req.opcode === AcquireBlock && req.fromA || req.opcode === AcquirePerm // AcquireBlock and Probe share the same opcode
  val req_acquirePerm = req.opcode === AcquirePerm
  val req_putfull = req.opcode === PutFullData
  val req_put = req.opcode === PutFullData || req.opcode === PutPartialData
  val req_get = req.opcode === Get
  val req_prefetch = req.opcode === Hint
  val req_promoteT = (req_acquire || req_get || req_prefetch) && Mux(dirResult.hit, meta_no_client && meta.state === TIP, gotT)

  /* ======== Task allocation ======== */
  // Theoretically, data to be released is saved in ReleaseBuffer, so Acquire can be sent as soon as req enters mshr
  io.tasks.source_a.valid := !state.s_acquire && state.s_release && state.w_release_sent
  if(cacheParams.name == "l3") {
    io.tasks.source_b.valid := (!state.s_pprobe || !state.s_rprobe) && io.tasks.source_b.bits.clients.orR
  } else {
    io.tasks.source_b.valid := !state.s_pprobe || !state.s_rprobe
  }
  val mp_release_valid = !state.s_release && state.w_rprobeacklast
  val mp_probeack_valid = !state.s_probeack && state.w_pprobeacklast
  val mp_grant_valid = !state.s_refill && state.w_grantlast && state.w_rprobeacklast && state.s_release && !req_put// [Alias] grant after rprobe done
  val mp_put_wb_valid = !state.s_put_wb && state.w_rprobeacklast && state.w_releaseack && state.w_pprobeacklast && state.w_grantlast && state.s_release // && state.s_refill
  io.tasks.mainpipe.valid := mp_release_valid || mp_probeack_valid || mp_grant_valid || mp_put_wb_valid
  // io.tasks.prefetchTrain.foreach(t => t.valid := !state.s_triggerprefetch.getOrElse(true.B))

  if(cacheParams.name == "l3") {
    when(status_reg.valid) {
      assert(!mp_probeack_valid, s"L3 will not schedule probe ack task! mshrId:%d set:0x%x tag:0x%x", io.id, status_reg.bits.set, status_reg.bits.tag)
    }
  }

  
  /* ======== Deal with clients ======== */
  val probeClientsOH = Mux(dirResult.hit, dirResult.meta.clients & ~reqClientOH, dirResult.meta.clients)
  val clientValid = !(req_get && (!dirResult.hit || meta_no_client || probeGotN))
  val newClientsOH = reqClientOH & Fill(clientBits, clientValid)
  val oldClientsOH = RegInit(0.U(clientBits.W))

  when(io.alloc.fire) { 
    oldClientsOH := Mux(io.alloc.bits.dirResult.hit, io.alloc.bits.dirResult.meta.clients, 0.U(clientBits.W))
  }

  when(io.tasks.source_b.fire && io.tasks.source_b.bits.param === toN) { // Only Probe.toN can remove old client bit
    oldClientsOH := oldClientsOH & ~io.tasks.source_b.bits.clients
  }

  val mergedClientsOH = oldClientsOH & ~nestedReleaseClientOH | newClientsOH

  dontTouch(reqClientOH)
  dontTouch(clientValid)
  dontTouch(newClientsOH)
  dontTouch(oldClientsOH)
  dontTouch(mergedClientsOH)


  val a_task = {
    val oa = io.tasks.source_a.bits
    oa := DontCare
    oa.tag := req.tag
    oa.set := req.set
    oa.off := req.off
    oa.source := io.id
    if (cacheParams.name == "l3") {
      oa.opcode := Mux(
          req_putfull,
          AcquirePerm,
          // Get or AcquireBlock or PutPartialData
          AcquireBlock
      )
    } else {
      oa.opcode := Mux(
        req_acquirePerm,
        req.opcode,
        Mux(
          req_putfull,
          AcquirePerm,
          // Get or AcquireBlock or PutPartialData
          AcquireBlock
        )
      )
    }
//    oa.param := Mux(
//      req_put,
//      req.param,
//      Mux(req_needT, Mux(dirResult.hit, BtoT, NtoT), NtoB)
//    )
    if(cacheParams.name == "l3") {
      oa.param := Mux(req_needT || req_putfull, Mux(dirResult.hit, BtoT, NtoT), NtoT)

      when (io.tasks.source_a.valid) {
        assert(oa.param === NtoT, s"unexpected oa.param: %d req_needT: %d dirResult.hit: %d set: 0x%x tag: 0x%x", oa.param, req_needT, dirResult.hit, status_reg.bits.set, status_reg.bits.tag)
      }
    } else {
      oa.param := Mux(req_needT || req_putfull, Mux(dirResult.hit, BtoT, NtoT), NtoB)
    }
    oa.size := req.size
    oa.pbIdx := req.pbIdx
    oa.reqSource := req.reqSource
    oa
  }

  val b_task = {
    val ob = io.tasks.source_b.bits
    ob := DontCare
    ob.tag := dirResult.tag
    ob.set := dirResult.set
    ob.off := 0.U
    ob.opcode := Probe
    // ob.param := Mux(!state.s_pprobe, req.param, toN)
    if(cacheParams.name == "l3") {
      assert(state.s_pprobe)

      ob.param := Mux(
        !state.s_pprobe, // TODO: remove
        req.param,
        Mux(
          req_get && dirResult.hit && meta.state === TRUNK || req_acquire && dirResult.hit && !req_needT,
          toB,
          toN
        )
      )
    } else {
      ob.param := Mux(
        !state.s_pprobe,
        req.param,
        Mux(
          req_get && dirResult.hit && meta.state === TRUNK,
          toB,
          toN
        )
      )
    }
    ob.alias.foreach(_ := meta.alias.getOrElse(0.U))
    if(cacheParams.name == "l3") {
      ob.clients := Mux(dirResult.hit, clientsExceptReqClientOH, dirResult.meta.clients)
    } else {
      ob.clients := dirResult.meta.clients
    }
    ob
  }

  val mp_release, mp_probeack, mp_grant, mp_put_wb = Wire(new TaskBundle)
  val mp_release_task = {
    mp_release := DontCare
    mp_release.channel := req.channel
    mp_release.tag := dirResult.tag
    mp_release.set := req.set
    mp_release.off := 0.U
    mp_release.alias.foreach(_ := 0.U)
    // if dirty, we must ReleaseData
    // if accessed, we ReleaseData to keep the data in L3, for future access to be faster
    // [Access] TODO: consider use a counter
    mp_release.opcode := {
      cacheParams.releaseData match {
        case 0 => Mux(meta.dirty && meta.state =/= INVALID || probeDirty, ReleaseData, Release)
        case 1 => Mux(meta.dirty && meta.state =/= INVALID || probeDirty || meta.accessed, ReleaseData, Release)
        case 2 => Mux(meta.prefetch.getOrElse(false.B) && !meta.accessed, Release, ReleaseData) //TODO: has problem with this
        case 3 => ReleaseData // best performance with HuanCun-L3
      }
    }
    mp_release.param := Mux(isT(meta.state), TtoN, BtoN)
    mp_release.mshrTask := true.B
    mp_release.mshrId := io.id
    mp_release.aliasTask.foreach(_ := false.B)
    mp_release.useProbeData := true.B // read ReleaseBuf when useProbeData && opcode(0) is true
    mp_release.way := req.way
    mp_release.dirty := meta.dirty && meta.state =/= INVALID || probeDirty
    mp_release.metaWen := true.B
    mp_release.meta := MetaEntry()
    mp_release.tagWen := false.B
    mp_release.dsWen := false.B
    mp_release
  }

  val mp_probeack_task = { // accept probe and need resp(probeack)
    mp_probeack := DontCare
    mp_probeack.channel := req.channel
    mp_probeack.tag := req.tag
    mp_probeack.set := req.set
    mp_probeack.off := req.off
    mp_probeack.opcode := Mux(
      meta.dirty && isT(meta.state) || probeDirty || req.needProbeAckData,
      ProbeAckData,
      ProbeAck
    )
    mp_probeack.param := ParallelLookUp(
      Cat(isT(meta.state), req.param(bdWidth - 1, 0)),
      Seq(
        Cat(false.B, toN) -> BtoN,
        Cat(false.B, toB) -> BtoB, // TODO: make sure that this req will not enter mshr in this situation
        Cat(true.B, toN) -> TtoN,
        Cat(true.B, toB) -> TtoB
      )
    )
    mp_probeack.mshrTask := true.B
    mp_probeack.mshrId := io.id
    mp_probeack.aliasTask.foreach(_ := false.B)
    mp_probeack.useProbeData := true.B // read ReleaseBuf when useProbeData && opcode(0) is true
    mp_probeack.way := req.way
    mp_probeack.dirty := meta.dirty && meta.state =/= INVALID || probeDirty
    mp_probeack.meta := MetaEntry(
      dirty = false.B,
      state = Mux(
        req.param === toN,
        INVALID,
        Mux(
          req.param === toB,
          BRANCH,
          meta.state
        )
      ),
      clients = Fill(clientBits, !probeGotN),
      alias = meta.alias, //[Alias] Keep alias bits unchanged
      prefetch = req.param =/= toN && meta_pft,
      accessed = req.param =/= toN && meta.accessed
    )
    mp_probeack.metaWen := true.B
    mp_probeack.tagWen := false.B
    mp_probeack.dsWen := req.param =/= toN && probeDirty
    mp_probeack
  }

  val mp_grant_task    = { // mp_grant_task will serve AcquriePrem/AcquireBlock, Get, Hint
    val reqClientNotExist = ~Cat(meta.clients & reqClientOH).orR
    mp_grant := DontCare
    mp_grant.channel := req.channel
    mp_grant.tag := req.tag
    mp_grant.set := req.set
    mp_grant.off := req.off
    mp_grant.sourceId := req.source
    if(cacheParams.name == "l3") {
      // mp_grant.opcode := Mux( reqClientNotExist && req_acquire && dirResult.hit, GrantData, odOpGen(req.opcode))
      mp_grant.opcode := Mux( reqClientNotExist && req_acquire, GrantData, odOpGen(req.opcode))
    } else {
      require(clientBits == 1)
      mp_grant.opcode := odOpGen(req.opcode)
    }
    mp_grant.param := Mux(
      req_get || req_put || req_prefetch,
      0.U, // Get/Put -> AccessAckData/AccessAck
      MuxLookup( // Acquire -> Grant
        req.param,
        req.param,
        Seq(
          NtoB -> Mux(req_promoteT, toT, toB),
          BtoT -> toT,
          NtoT -> toT
        )
      )
    )
    mp_grant.mshrTask := true.B
    mp_grant.mshrId := io.id
    mp_grant.way := req.way
    // if it is a Get or Prefetch, then we must keep alias bits unchanged
    // in case future probes gets the wrong alias bits
    val aliasFinal = Mux(req_get || req_prefetch, meta.alias.getOrElse(0.U), req.alias.getOrElse(0.U))
    mp_grant.alias.foreach(_ := aliasFinal)
    mp_grant.aliasTask.foreach(_ := req.aliasTask.getOrElse(false.B))
    // [Alias] write probeData into DS for alias-caused Probe,
    // but not replacement-cased Probe
    mp_grant.useProbeData := dirResult.hit && ( req_get || probeDirty || nestedRelease ) || req.aliasTask.getOrElse(false.B)
    if(cacheParams.name == "l3") {
      mp_grant.selfHasData := dirResult.hit && !probeDirty && !nestedRelease
    }

    val new_meta = MetaEntry()
    new_meta.dirty := gotDirty || dirResult.hit && (meta.dirty || probeDirty)
    new_meta.alias.foreach(_ := aliasFinal)
    new_meta.prefetch.foreach(_ := req_prefetch || dirResult.hit && meta_pft)
    new_meta.accessed := req_acquire || req_get || req_put //[Access] TODO: check
    if(cacheParams.name == "l3") {
//      require(cacheParams.inclusionPolicy == "inclusive")

      new_meta.clients := Mux(
        req_prefetch,
        Mux(dirResult.hit, meta.clients, Fill(clientBits, false.B)),
        mergedClientsOH
      )

      new_meta.state := Mux(
        req_get,
        TIP,
        Mux(req_prefetch, TIP, Mux(meta_no_client || !dirResult.hit || req_needT || req_promoteT, TRUNK, TIP)),
      )

      when(status_reg.valid && mp_grant_valid && dirResult.hit) {
        assert(isT(meta.state))
      }
    } else { // L2
      new_meta.clients := Mux(
        req_prefetch,
        Mux(dirResult.hit, meta.clients, Fill(clientBits, false.B)),
        Fill(clientBits, !(req_get && (!dirResult.hit || meta_no_client || probeGotN)))
      )

      new_meta.state := Mux(
          req_get,
          Mux(
            dirResult.hit,
            Mux(isT(meta.state), TIP, BRANCH),
            Mux(req_promoteT, TIP, BRANCH)
          ),
          Mux(
            req_promoteT || req_needT,
            Mux(req_prefetch, TIP, TRUNK),
            BRANCH
          )
      )
    }
    mp_grant.meta := new_meta

    mp_grant.metaWen := !req_put
    mp_grant.tagWen := !dirResult.hit && !req_put

    mp_grant.dsWen := !dirResult.hit && !req_put && gotGrantData || probeDirty && (req_get || req.aliasTask.getOrElse(false.B)) || dirResult.hit && probeDirty
    mp_grant.fromL2pft.foreach(_ := req.fromL2pft.get)
    mp_grant.needHint.foreach(_ := false.B)
    mp_grant
  }

  val mp_put_wb_task = {
    mp_put_wb := DontCare
    mp_put_wb.mshrTask := true.B
    mp_put_wb.channel := req.channel
    mp_put_wb.tag := req.tag
    mp_put_wb.set := req.set
    mp_put_wb.off := req.off
    mp_put_wb.way := req.way
    mp_put_wb.opcode := req.opcode
    mp_put_wb.opcodeIsReq := true.B
    mp_put_wb.mshrId := io.id
    mp_put_wb.param := 0.U
//    mp_put_wb.reqSource := req.source
    mp_put_wb.sourceId := req.source
    mp_put_wb.pbIdx := req.pbIdx
    mp_put_wb.putHit := dirResult.hit
    mp_put_wb.useProbeData := dirResult.hit
    mp_put_wb.needProbeAckData := req.opcode === PutPartialData
    mp_put_wb.metaWen := true.B
    mp_put_wb.tagWen := !dirResult.hit
    mp_put_wb.meta := MetaEntry(
      dirty = true.B,
      state = TIP,
      clients = Fill(clientBits, false.B),
      alias = Some(req.alias.getOrElse(0.U)),
      prefetch = false.B,
      accessed = true.B //[Access] TODO: check
    )
//    mp_put_wb.dsWen := dirResult.hit && req_put
    mp_put_wb.dsWen := true.B
    mp_put_wb
  }

  io.tasks.mainpipe.bits := ParallelPriorityMux(
    Seq(
      mp_grant_valid    -> mp_grant,
      mp_release_valid  -> mp_release,
      mp_probeack_valid -> mp_probeack,
      mp_put_wb_valid   -> mp_put_wb
    )
  )
  io.tasks.mainpipe.bits.reqSource := req.reqSource

  // io.tasks.prefetchTrain.foreach {
  //   train =>
  //     train.bits.tag := req.tag
  //     train.bits.set := req.set
  //     train.bits.needT := req_needT
  //     train.bits.source := req.source
  // }

  /* ======== Task update ======== */
  when (io.tasks.source_a.fire) {
    state.s_acquire := true.B
  }
  when (io.tasks.source_b.fire) {
    state.s_pprobe := true.B
    state.s_rprobe := true.B
  }
  when (io.tasks.mainpipe.ready) {
    when (mp_grant_valid) {
      state.s_refill := true.B
    }.elsewhen (mp_release_valid) {
      state.s_release := true.B
      meta.state := INVALID
    }.elsewhen (mp_probeack_valid) {
      state.s_probeack := true.B
    }.elsewhen (mp_put_wb_valid) {
      state.s_refill := true.B
      state.s_put_wb := true.B
    }
  }
  // prefetchOpt.foreach {
  //   _ =>
  //     when (io.tasks.prefetchTrain.get.fire()) {
  //       state.s_triggerprefetch.get := true.B
  //     }
  // }

  /* ======== Refill response ======== */
  val c_resp = io.resps.sink_c
  val d_resp = io.resps.sink_d
  val e_resp = io.resps.sink_e

  dontTouch(io.resps.sink_c.bits.source)

  val probeAckDoneClient = RegInit(0.U(clientBits.W))
  val incomingProbeAckClient = WireInit(0.U(clientBits.W))

  dontTouch(incomingProbeAckClient)
  dontTouch(probeAckDoneClient)
  dontTouch(probeClientsOH)

  if(cacheParams.name == "l3") {
    // ! This is the last client sending probeack
    val probeackLast = ((probeAckDoneClient | incomingProbeAckClient) & ~nestedReleaseClientOH) === probeClientsOH || probeClientsOH === 0.U(clientBits.W)
    dontTouch(probeackLast)

    when(io.alloc.valid) {
      probeAckDoneClient := 0.U
    }

    when(c_resp.valid && io.status.bits.w_c_resp && io.status.valid) {
      incomingProbeAckClient := getClientBitOH(io.resps.sink_c.bits.source)
      when(c_resp.bits.opcode === ProbeAck || c_resp.bits.opcode === ProbeAckData) {
        probeAckDoneClient := probeAckDoneClient | incomingProbeAckClient
        state.w_rprobeackfirst := state.w_rprobeackfirst || probeackLast
        state.w_rprobeacklast := state.w_rprobeacklast || c_resp.bits.last && probeackLast
        state.w_pprobeackfirst := state.w_pprobeackfirst || probeackLast
        state.w_pprobeacklast := state.w_pprobeacklast || c_resp.bits.last && probeackLast
        state.w_pprobeack := state.w_pprobeack || (req.off === 0.U || c_resp.bits.last) && probeackLast
      }
      when(c_resp.bits.opcode === ProbeAckData) {
        probeDirty := true.B
      }
      when(isToN(c_resp.bits.param)) {
        probeGotN := true.B
      }
    }.elsewhen(c_resp.valid) { // Other probe sub request with same addr
      // TODO:
    }
  } else { // L2
    when(c_resp.valid) {
      when(c_resp.bits.opcode === ProbeAck || c_resp.bits.opcode === ProbeAckData) {
        state.w_rprobeackfirst := true.B
        state.w_rprobeacklast := state.w_rprobeacklast || c_resp.bits.last
        state.w_pprobeackfirst := true.B
        state.w_pprobeacklast := state.w_pprobeacklast || c_resp.bits.last
        state.w_pprobeack := state.w_pprobeack || req.off === 0.U || c_resp.bits.last
      }
      when(c_resp.bits.opcode === ProbeAckData) {
        probeDirty := true.B
      }
      when(isToN(c_resp.bits.param)) {
        probeGotN := true.B
      }
    }
  }

  when (d_resp.valid) {
    when(d_resp.bits.opcode === Grant || d_resp.bits.opcode === GrantData || d_resp.bits.opcode === AccessAck) {
      state.w_grantfirst := true.B
      state.w_grantlast := d_resp.bits.last
      state.w_grant := req.off === 0.U || d_resp.bits.last  // TODO? why offset?
    }
    when(d_resp.bits.opcode === Grant || d_resp.bits.opcode === GrantData) {
      gotT := d_resp.bits.param === toT
      gotDirty := gotDirty || d_resp.bits.dirty
    }
    when(d_resp.bits.opcode === GrantData) {
      gotGrantData := true.B
    }
    when(d_resp.bits.opcode === ReleaseAck) {
      state.w_releaseack := true.B
    }
  }

  when (e_resp.valid) {
    state.w_grantack := true.B
  }

  when (io.resps.source_c.valid) {
    state.w_release_sent := true.B
  }

  when (status_reg.valid) {
    timer := timer + 1.U
  }
  
  val no_schedule = state.s_refill && state.s_probeack// && state.s_triggerprefetch.getOrElse(true.B)
  val no_wait = state.w_rprobeacklast && state.w_pprobeacklast && state.w_grantlast && state.w_releaseack && state.w_grantack
  val will_free = no_schedule && no_wait
  when (will_free && status_reg.valid) {
    status_reg.valid := false.B
    timer := 0.U
  }

  io.status.valid := status_reg.valid
  io.status.bits <> status_reg.bits
  // For A reqs, we only concern about the tag to be replaced
  io.status.bits.tag := Mux(state.w_release_sent, req.tag, dirResult.tag) // s_release is low-as-valid
  io.status.bits.nestB := status_reg.valid && state.w_releaseack && state.w_rprobeacklast && state.w_pprobeacklast && !state.w_grantfirst
  // wait for resps, high as valid
  io.status.bits.w_c_resp := !state.w_rprobeacklast || !state.w_pprobeacklast || !state.w_pprobeack
  io.status.bits.w_d_resp := !state.w_grantlast || !state.w_grant || !state.w_releaseack
  io.status.bits.w_e_resp := !state.w_grantack
  io.status.bits.will_free := will_free
  io.status.bits.is_miss := !dirResult.hit
  io.status.bits.is_prefetch := req_prefetch

  io.toReqBuf.valid := status_reg.valid
  io.toReqBuf.bits.set := req.set
  io.toReqBuf.bits.way := req.way
  io.toReqBuf.bits.reqTag := req.tag
  io.toReqBuf.bits.needRelease := !state.w_release_sent
  io.toReqBuf.bits.metaTag := dirResult.tag
  io.toReqBuf.bits.willFree := will_free
  io.toReqBuf.bits.isAcqOrPrefetch := req_acquire || req_prefetch

  if(cacheParams.name == "l3") {
    // assert(!(c_resp.valid && !io.status.bits.w_c_resp))
  } else {
    assert(!(c_resp.valid && !io.status.bits.w_c_resp))
  }
  assert(!(d_resp.valid && !io.status.bits.w_d_resp))
  assert(!(e_resp.valid && !io.status.bits.w_e_resp))

  val nestedwb_match = status_reg.valid && meta.state =/= INVALID &&
    dirResult.set === io.nestedwb.set &&
    dirResult.tag === io.nestedwb.tag
  when (nestedwb_match) {
    when (io.nestedwb.b_toN) {
      dirResult.hit := false.B
    }
    when (io.nestedwb.b_toB) {
      meta.state := BRANCH
    }
    when (io.nestedwb.b_clr_dirty) {
      meta.dirty := false.B
    }
    when (io.nestedwb.c_set_dirty) {
      meta.dirty := true.B
    }
    when (io.nestedwb.c_toN) {
      nestedRelease := true.B
      // Update nested meta
      meta.clients := meta.clients & ~io.nestedwb.c_client
      nestedReleaseClientOH := nestedReleaseClientOH | io.nestedwb.c_client
    }
  }

  io.nestedwbData := nestedwb_match && io.nestedwb.c_set_dirty

  dontTouch(state)

  /* ======== Performance counters ======== */
  // time stamp
  // if (cacheParams.enablePerf) {
    val acquire_ts = RegEnable(timer, false.B, io.tasks.source_a.fire)
    val probe_ts = RegEnable(timer, false.B, io.tasks.source_b.fire)
    val release_ts = RegEnable(timer, false.B, !mp_grant_valid && mp_release_valid && io.tasks.mainpipe.ready)
    val acquire_period = IO(Output(UInt(64.W)))
    val probe_period = IO(Output(UInt(64.W)))
    val release_period = IO(Output(UInt(64.W)))
    acquire_period := timer - acquire_ts
    probe_period := timer - probe_ts
    release_period := timer - release_ts
  // }
}
