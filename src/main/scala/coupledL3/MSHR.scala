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
import coupledL3.MetaData._
import utility.ParallelMax
import utility.{ParallelLookUp, ParallelPriorityMux}
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tilelink.TLMessages._
import freechips.rocketchip.tilelink.TLPermissions._
import chipsalliance.rocketchip.config.Parameters
import coupledL3.prefetch.PrefetchTrain
import coupledL3.utils.XSPerfAccumulate

class MSHRTasks(implicit p: Parameters) extends L3Bundle {
  // outer
  val source_a = DecoupledIO(new SourceAReq) // To AcquireUnit  // TODO: no need to use decoupled handshake
  val source_b = DecoupledIO(new SourceBReq)
  val mainpipe = DecoupledIO(new TaskBundle) // To Mainpipe (SourceC or SourceD)
  // val prefetchTrain = prefetchOpt.map(_ => DecoupledIO(new PrefetchTrain)) // To prefetcher
}

class MSHRResps(implicit p: Parameters) extends L3Bundle {
  val sink_c = Flipped(ValidIO(new RespInfoBundle))
  val sink_d = Flipped(ValidIO(new RespInfoBundle))
  val sink_e = Flipped(ValidIO(new RespInfoBundle))
  // make sure that Acquire is sent after Release,
  // so resp from SourceC is needed to initiate Acquire
  val source_c = Flipped(ValidIO(new RespInfoBundle))
}

class MSHR(implicit p: Parameters) extends L3Module {
  val io = IO(new Bundle() {
    val id = Input(UInt(mshrBits.W))
    val status = ValidIO(new MSHRStatus)
    val toReqBuf = ValidIO(new MSHRBlockAInfo)
    val alloc = Flipped(ValidIO(new MSHRRequest))
    val tasks = new MSHRTasks()
    val resps = new MSHRResps()
    val nestedwb = Input(new NestedWriteback)
    val nestedwbData = Output(Bool())

    val probeHelperWakeup = Input(new ProbeHelperWakeupInfo) // Only for NINE

    val block = Input(Bool())
    val mshrTaskIsFire = Input(Bool())
  })

  val initState = Wire(new FSMState())
  val state = RegInit(new FSMState(), initState)
  initState.elements.foreach(_._2 := true.B)

  val dirResult = RegInit(0.U.asTypeOf(new DirResult()))
  val clientDirResult = RegInit(0.U.asTypeOf(new noninclusive.ClientDirResult))
  val hasClientHit = clientDirResult.hits.asUInt.orR


  val gotT = RegInit(false.B) // TODO: L3 might return T even though L3 wants B
  val gotDirty = RegInit(false.B)
  val gotGrantData = RegInit(false.B)

  val probeDirty = RegInit(false.B)
  val probeGotN = RegInit(false.B)
  val probeGotNtoNReg = RegInit(false.B)
  val probeGotNtoN = WireInit(false.B)

  //  nested B info
  val waitNestedB = RegInit(false.B) // L3 does not need
  val nestedProbeToN = RegInit(false.B)
  val nestedSourceIdB = RegInit(0.U(sourceIdBits.W))

  // nested C info
  val needWaitNestedC = RegInit(false.B)
  val waitNestedC = RegInit(false.B)
  val nestedReleaseToN = RegInit(false.B)
  val nestedSourceIdC = RegInit(0.U(sourceIdBits.W))
  val nestedReleaseNeedRelease = RegInit(false.B)
  val nestedReleaseClientOH = RegInit(0.U(clientBits.W))
  val nestedValid = WireInit(false.B)
  val nestedWbMatch = WireInit(false.B)

  val aNeedProbe = RegInit(false.B)
  val probeAckParamVec = RegInit(VecInit(Seq.fill(clientBits)(0.U.asTypeOf(chiselTypeOf(io.resps.sink_c.bits.param)))))
  val stateAfterProbe = RegInit(0.U(stateBits.W))

  val timer = RegInit(0.U(64.W)) // for performance analysis


  // --------------------------------------------------------------------------
  //  MSHR Allocation
  // --------------------------------------------------------------------------
  val status_reg = RegInit(0.U.asTypeOf(Valid(new MSHRStatus())))
  val req        = status_reg.bits
  val reqClient   = RegInit(0.U((log2Up(clientBits) + 1).W)) // Which client does this req come from?
  val reqClientOH = RegInit(0.U(clientBits.W))
  when(io.alloc.fire) {
    val regClientOHWire = getClientBitOH(io.alloc.bits.task.sourceId)
    reqClientOH := regClientOHWire
    reqClient := Mux(regClientOHWire === 0.U, Cat(1.U(1.W), 0.U(log2Up(clientBits).W)), OHToUInt(regClientOHWire)) // The highest bit of reqClient indicates that req comes from TL-UL node // TODO: consider DMA
  }

  val clientsExceptReqClientOH = clientDirResult.hits.asUInt & ~reqClientOH
  val meta       = dirResult.meta

  val highestState = ParallelMax(
    Seq(Mux(dirResult.hit, meta.state, INVALID)) ++
    clientDirResult.hits.zip(clientDirResult.metas).map{
      case(clientHit, clientMeta) => 
        Mux(clientHit, clientMeta.state, INVALID)
    }
  )
  val highestStateExceptReqClient = ParallelMax(
    Seq(Mux(dirResult.hit, meta.state, INVALID)) ++
    clientDirResult.metas.zipWithIndex.map{
      case (clientMeta, i) => 
        Mux(reqClientOH === UIntToOH(i.U, clientBits), INVALID, clientMeta.state)
    }
  )
  val highestClientState = ParallelMax(
    clientDirResult.hits.zip(clientDirResult.metas).map {
      case (clientHit, clientMeta) =>
        Mux(clientHit, clientMeta.state, INVALID)
    }
  )
  dontTouch(highestState)
  dontTouch(highestStateExceptReqClient)
  dontTouch(highestClientState)
  
  assert(PopCount(reqClientOH) <= 1.U)

  when(io.alloc.valid) {
    assert(status_reg.valid === false.B, "Trying to alloc a valid MSHR. mshr:%d", io.id)

    status_reg.valid := true.B
    state       := io.alloc.bits.state
    dirResult   := io.alloc.bits.dirResult
    clientDirResult := io.alloc.bits.clientDirResult.getOrElse(0.U.asTypeOf(new noninclusive.ClientDirResult))
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
    req.bufIdx  := msTask.bufIdx
    req.reqSource := msTask.reqSource
    req.fromProbeHelper := msTask.fromProbeHelper
    gotT        := false.B
    gotDirty    := false.B
    gotGrantData := false.B
    probeDirty  := false.B
    probeGotN   := false.B
    probeGotNtoNReg := false.B
    aNeedProbe := !io.alloc.bits.state.s_rprobe
    probeAckParamVec.foreach( _ := DontCare)
    stateAfterProbe := INVALID
    timer       := 1.U
  }


  // --------------------------------------------------------------------------
  //  Enchantment
  // --------------------------------------------------------------------------
  val meta_no_client = !clientDirResult.hits.asUInt.orR

  val req_needT = needT(req.opcode, req.param) // Put / Acquire.NtoT / Acquire.BtoT / Hint.prefetch_write
  val req_acquire = req.opcode === AcquireBlock && req.fromA || req.opcode === AcquirePerm // AcquireBlock and Probe share the same opcode
  val req_acquirePerm = req.opcode === AcquirePerm
  val req_putfull = req.opcode === PutFullData
  val req_put = req.opcode === PutFullData || req.opcode === PutPartialData
  val req_get = req.opcode === Get
  val req_prefetch = req.opcode === Hint
  val req_promoteT = (req_acquire || req_get || req_prefetch) && Mux(dirResult.hit, meta_no_client && meta.state === TIP || nestedReleaseToN, gotT)

  // self cache does not have the acquired block, but some other client owns the block
  val transmitFromOtherClient = !dirResult.hit && VecInit(clientDirResult.hits.zipWithIndex.map {
    case (clientHit, client) =>
      (req.opcode === Get || req_put || client.U =/= reqClient) && clientHit
  }).asUInt.orR

  // --------------------------------------------------------------------------
  //  Task allocation
  // --------------------------------------------------------------------------
  // Theoretically, data to be released is saved in ReleaseBuffer, so Acquire can be sent as soon as req enters mshr
  io.tasks.source_a.valid := !state.s_acquire && state.s_release && state.w_release_sent
  assert(!((!state.s_pprobe || !state.s_rprobe) && !io.tasks.source_b.bits.clients.orR && !req.fromProbeHelper), "Need schedule probe but without clients Set:0x%x Tag:0x%x mshr:%d fromProbeHelper:%d rprobe:%d pprobe:%d ob.param:%d", req.set, req.tag, io.id, req.fromProbeHelper, state.s_rprobe, state.s_pprobe, io.tasks.source_b.bits.param)
  io.tasks.source_b.valid := (!state.s_pprobe || !state.s_rprobe) && state.w_release_sent
    
  // val mp_release_valid = !state.s_release && state.w_rprobeacklast && state.w_pprobeacklast && !waitNestedC && !waitNestedB && !nestedValid // && state.w_probehelper_done // && !waitNestedC && !waitNestedB && !nestedValid
  val mp_release_valid = !state.s_release && state.w_pprobeacklast && !waitNestedC && !waitNestedB && !nestedValid && !needWaitNestedC
  val mp_releaseack_valid = !state.s_releaseack && state.w_release_sent
  val mp_probeack_valid = !state.s_probeack && state.w_pprobeacklast && !waitNestedC && !waitNestedB && !needWaitNestedC
  val mp_grant_valid = !state.s_refill && state.w_grantlast && state.w_rprobeacklast && state.s_release && state.w_probehelper_done && !req_put && !waitNestedC && !waitNestedB && !nestedValid && !needWaitNestedC
  val mp_put_wb_valid = !state.s_put_wb && state.w_rprobeacklast && state.w_releaseack && state.w_pprobeacklast && state.w_grantlast && state.s_release && !waitNestedC && !waitNestedB && !nestedValid && !needWaitNestedC// && state.s_refill
  io.tasks.mainpipe.valid := mp_release_valid || mp_probeack_valid || mp_releaseack_valid || mp_grant_valid && !io.block || mp_put_wb_valid


  def shrinkNextState(param: UInt): UInt = {
    assert(param =/= TtoT, "ProbeAck toT is not allowed in current design")
    Mux(param === TtoB || param === BtoB, BRANCH, INVALID)
  }

  
  // Deal with clients
  val clientValid = !(req_get && (!dirResult.hit || meta_no_client || probeGotN))


  // --------------------------------------------------------------------------
  //  MSHR send A task
  // --------------------------------------------------------------------------
  val a_task = {
    val oa = io.tasks.source_a.bits
    oa := DontCare
    oa.tag := req.tag
    oa.set := req.set
    oa.off := req.off
    oa.source := io.id
    oa.opcode := Mux(
        req_putfull,
        AcquirePerm,
        // Get or AcquireBlock or PutPartialData
        AcquireBlock
    )

    oa.param := Mux(req_needT || req_putfull, Mux(dirResult.hit, BtoT, NtoT), NtoT)

    oa.size := req.size
    oa.pbIdx := req.pbIdx
    oa.reqSource := req.reqSource
    oa
  }


  // --------------------------------------------------------------------------
  //  MSHR send B task
  // --------------------------------------------------------------------------
  val b_task = {
    val ob = io.tasks.source_b.bits
    ob := DontCare
    ob.tag := req.tag
    ob.set := req.set
    ob.off := 0.U
    ob.opcode := Probe
    when(!state.s_pprobe) {
      assert(req.fromProbeHelper)
    }
    ob.param := Mux(
      !state.s_pprobe, // only from ProbeHelper
      req.param,
      Mux(
        req_get && dirResult.hit && meta.state === TRUNK || req_acquire && !req_needT,
        toB,
        toN
      )
    )


    val temp_clientDirResultHits = clientDirResult.hits.asUInt
    dontTouch(temp_clientDirResultHits)

    ob.clients := Mux(
      req.fromProbeHelper,
      clientDirResult.hits.asUInt,
      clientsExceptReqClientOH
    )

    ob.needData := !dirResult.hit || dirResult.hit && dirResult.meta.state <= TRUNK

    ob
  }


  val mp_release, mp_releaseack, mp_probeack, mp_grant, mp_put_wb = Wire(new TaskBundle)
  // --------------------------------------------------------------------------
  //  MSHR send Release(C) task
  // --------------------------------------------------------------------------
  val mp_release_task = {
    mp_release := DontCare
    mp_release.channel := req.channel
    mp_release.tag := Mux(
                          req.fromProbeHelper, 
                          req.tag, // turn probeack into release
                          dirResult.tag
                        )
    mp_release.set := req.set
    mp_release.off := 0.U
    mp_release.alias.foreach(_ := 0.U)
    // if dirty, we must ReleaseData
    // if accessed, we ReleaseData to keep the data in L3, for future access to be faster
    mp_release.opcode := { // TODO: NINE Rlease or ReleaseData
      cacheParams.releaseData match {
        case 0 => Mux(meta.dirty && meta.state =/= INVALID || probeDirty, ReleaseData, Release)
//        case 1 => Mux(meta.dirty && meta.state =/= INVALID || probeDirty || meta.accessed, ReleaseData, Release)
//        case 2 => Mux(meta.prefetch.getOrElse(false.B) && !meta.accessed, Release, ReleaseData) //TODO: has problem with this
        case 3 => ReleaseData // best performance with HuanCun-L3
      } // TODO: NINE ProbeHelper turn into release use Release or ReleaseData?
    }
    mp_release.param := Mux(isT(meta.state), TtoN, BtoN)
    mp_release.mshrTask := true.B
    mp_release.sourceId := req.source
    mp_release.mshrId := io.id
    mp_release.aliasTask.foreach(_ := false.B)
    mp_release.useProbeData := true.B // read ReleaseBuf when useProbeData && opcode(0) is true
    mp_release.selfHasData := Mux(req.fromProbeHelper, probeGotNtoN, Mux(nestedProbeToN, true.B, req.fromA)) // For A dir miss and nested C dir hit
    mp_release.way := Mux(nestedReleaseNeedRelease, dirResult.way, req.way)
    mp_release.dirty := meta.dirty && meta.state =/= INVALID || probeDirty

    mp_release.fromProbeHelper := req.fromProbeHelper
    mp_release.clientSet := clientDirResult.set
    when(req.fromProbeHelper) { // turn probeack into release
      mp_release.meta := MetaEntry()
      mp_release.metaWen := false.B
      mp_release.tagWen := false.B
      mp_release.dsWen := false.B

      mp_release.clientWay := clientDirResult.way
      mp_release.clientMetaWen := false.B
      mp_release.clientTagWen := false.B // NINE directory is inclusive
    }.otherwise{
      mp_release.meta := MetaEntry()
      mp_release.metaWen := Mux(nestedProbeToN, true.B, !nestedReleaseNeedRelease)
      mp_release.tagWen := !dirResult.hit
      mp_release.dsWen := false.B

      mp_release.clientWay := clientDirResult.way
      mp_release.clientMetaWen := Mux(nestedProbeToN, false.B, !nestedReleaseNeedRelease)
      mp_release.clientMeta.foreach( meta => meta.state := INVALID )
      mp_release.clientTagWen := false.B // NINE directory is inclusive
    }
    mp_release
  }


  // --------------------------------------------------------------------------
  //  MSHR send ProbeAck/ProbeAckData
  // --------------------------------------------------------------------------
  val mp_probeack_task = { // accept probe and need resp(probeack)
    mp_probeack := DontCare
    mp_probeack.channel := req.channel
    mp_probeack.tag := req.tag
    mp_probeack.set := req.set
    mp_probeack.off := req.off
    mp_probeack.opcode := Mux(
      meta.dirty && !req.fromProbeHelper && isT(meta.state) || probeDirty || req.needProbeAckData,
      ProbeAckData,
      ProbeAck // ProbeHelper task will only resp with ProbeAck
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
      dirty = meta.dirty && meta.state =/= INVALID || probeDirty,
      state = Mux(
        req.param === toN,
        Mux(req.fromProbeHelper, Mux(nestedReleaseToN, dirResult.meta.state, stateAfterProbe), INVALID),
        Mux(
          req.param === toB,
          BRANCH,
          meta.state
        )
      ),
      clientStates = VecInit(Seq.fill(clientBits)(INVALID))
    )
    mp_probeack.metaWen := dirResult.hit // true.B
    mp_probeack.tagWen := false.B
//    mp_probeack.dsWen := req.param =/= toN && probeDirty
    mp_probeack.dsWen := highestClientState === TIP && probeDirty

    mp_probeack.clientMetaWen := req.fromProbeHelper
    mp_probeack.clientMeta.foreach( meta => meta.state := INVALID )
    mp_probeack.fromProbeHelper := req.fromProbeHelper

    mp_probeack.clientTagWen := false.B
    mp_probeack.clientSet := req.set
    mp_probeack.clientTag := req.tag
    mp_probeack.clientWay := clientDirResult.way

    mp_probeack
  }


  // --------------------------------------------------------------------------
  //  MSHR send ReleaseAck
  // --------------------------------------------------------------------------
  val mp_releaseack_task = {
    mp_releaseack := DontCare
    mp_releaseack.channel := req.channel
    mp_releaseack.tag := req.tag
    mp_releaseack.set := req.set
    mp_releaseack.off := 0.U
    mp_releaseack.alias.foreach(_ := 0.U)
    mp_releaseack.opcode := ReleaseAck
    mp_releaseack.param := 0.U
    mp_releaseack.mshrTask := true.B
    mp_releaseack.mshrId := io.id
    mp_releaseack.sourceId := req.source
    mp_releaseack.aliasTask.foreach(_ := false.B)
    mp_releaseack.bufIdx := req.bufIdx // index for SinkC buffer
    // mp_releaseack.useProbeData := true.B // read ReleaseBuf when useProbeData && opcode(0) is true
    
    mp_releaseack.metaWen := true.B

    val newSelfState = WireInit(0.U(stateBits.W))
    val newSelfClientState = WireInit(VecInit(Seq.fill(clientBits)(0.U(stateBits.W))))

    newSelfState := MuxLookup(
                      req.param,
                      meta.state,
                      Seq(
                        TtoT -> TRUNK,
                        TtoB -> TIP,
                        TtoN -> TIP,
                        BtoN -> BRANCH
                      )
                    )
    
    newSelfClientState.zipWithIndex.foreach{
      case (selfClientState, client) => 
        selfClientState := Mux(
                                reqClient === client.U, 
                                Mux(
                                  isToN(req.param), 
                                  INVALID, 
                                  Mux(
                                    isToB(req.param), 
                                    BRANCH, 
                                    dirResult.meta.clientStates(client)
                                  )
                                ),
                                INVALID 
                            )
    }

    mp_releaseack.meta := MetaEntry(
      dirty = true.B, // TODO: 
      state = newSelfState,
      clientStates = newSelfClientState
    )

    mp_releaseack.way := req.way
    mp_releaseack.tagWen := !dirResult.hit
    mp_releaseack.dsWen := true.B
    
    mp_releaseack.clientMetaWen := true.B
    mp_releaseack.clientMeta.zipWithIndex.foreach{
      case (clientMeta, client) => 
        when(reqClient === client.U) {
          clientMeta.state := Mux(isToN(req.param), INVALID, BRANCH)
        }.otherwise {
          clientMeta.state := clientDirResult.metas(client).state
        }
    } 
    mp_releaseack.clientWay := clientDirResult.way
    mp_releaseack.clientTagWen := false.B // NINE directory is inclusive
    mp_releaseack.clientTag := clientDirResult.tag
    mp_releaseack.clientSet := clientDirResult.set

    mp_releaseack
  }


  // --------------------------------------------------------------------------
  //  MSHR send Grant/GrantData
  // --------------------------------------------------------------------------
  val mp_grant_task    = { // mp_grant_task will serve AcquriePrem/AcquireBlock, Get, Hint
    mp_grant := DontCare
    mp_grant.channel := req.channel
    mp_grant.tag := req.tag
    mp_grant.set := req.set
    mp_grant.off := req.off
    mp_grant.sourceId := req.source
    mp_grant.opcode := odOpGen(req.opcode)
    mp_grant.param := Mux(
      req_get,
      0.U, // Get/Put -> AccessAckData/AccessAck
      MuxLookup( // Acquire -> Grant
        req.param,
        req.param,
        Seq(
          NtoB -> Mux(req_promoteT || nestedReleaseToN, toT, toB),
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
    mp_grant.aliasTask.foreach(_ := req.aliasTask.getOrElse(false.B))
    // [Alias] write probeData into DS for alias-caused Probe,
    // but not replacement-cased Probe
    mp_grant.useProbeData := dirResult.hit && ( req_get || probeDirty ) || // TODO: get
                             !dirResult.hit && probeDirty  ||
                            req.aliasTask.getOrElse(false.B) ||
                            dirResult.hit && nestedProbeToN
    mp_grant.selfHasData := dirResult.hit && !probeDirty && !nestedReleaseToN || nestedReleaseToN

    val newMeta = MetaEntry()
    val newClientMetas = WireInit(VecInit(Seq.fill(clientBits)(0.U.asTypeOf(new noninclusive.ClientMetaEntry))))
    newMeta.dirty := gotDirty || dirResult.hit && (meta.dirty || probeDirty)

    val selfClientStates = WireInit(0.U.asTypeOf(Vec(clientBits, UInt(stateBits.W))))
    selfClientStates.zipWithIndex.foreach{
      case(newSelfClientState, client) =>
        when(reqClient === client.U) {
          newSelfClientState := Mux(req_acquire,
            Mux(nestedReleaseToN, TIP, Mux(req_needT || req_promoteT, TIP, BRANCH)), // Acquire
            Mux(
              req.opcode === Get,
              Mux(clientDirResult.hits(client), BRANCH, INVALID), // Get
              Mux(clientDirResult.hits(client), clientDirResult.metas(client).state, INVALID) // Hint
            )
          )
        }.otherwise{
          val stateAfterProbe_1 = shrinkNextState(probeAckParamVec(client))
          val TODO_prefetch_1 = RegInit(0.U(stateBits.W))

          newSelfClientState := Mux(
            req_acquire,
            Mux( // Acquire
              req.param =/= NtoB || req_promoteT,
              INVALID,
              Mux(clientDirResult.hits(client) && aNeedProbe, stateAfterProbe_1, INVALID)
            ),
            Mux( // Get / Hint
              req.opcode === Get,
              Mux(clientDirResult.hits(client) && aNeedProbe, stateAfterProbe_1, INVALID), // Get
              TODO_prefetch_1// Mux(prefetch_miss_need_probe, Mux(req.param === PREFETCH_READ, perm_after_probe, INVALID), clientDirResult.metas(client).state)
            )
          )
        }
    }

    newMeta.clientStates := selfClientStates
    newMeta.state := Mux(
      req_needT,
      Mux(req_acquire, TRUNK, TIP), // Acquire.NtoT / Acquire.BtoT / Hint.prefetch_write / [Put]
      Mux(!dirResult.hit,   // Acquire.NtoB / Get / Hint.prefetch_read
        Mux(
          transmitFromOtherClient,
          Mux(aNeedProbe, highestState, Mux(gotT, Mux(req_acquire, TRUNK, TIP), BRANCH)), // Miss
          Mux(nestedReleaseToN, TRUNK, Mux(gotT, Mux(req_acquire, TRUNK, TIP), BRANCH)) // Hit
        ),
        MuxLookup(dirResult.meta.state, INVALID, Seq( // dirResult.hit
          INVALID -> BRANCH,
          BRANCH -> Mux(req_promoteT, TRUNK, BRANCH),
          // if prefetch read && hit && self is Trunk
          // self meta won't update, we don't care new_meta
          TRUNK -> TIP,
          TIP -> Mux(
            meta_no_client && req_acquire, // promoteT
            TRUNK, TIP
          )
        ))
      )
    )

    newClientMetas.zipWithIndex.foreach{
      case (newClientMeta, client) =>
        when(reqClient === client.U) {
          newClientMeta.state := Mux(
            req_acquire,
            Mux(nestedReleaseToN, TIP, Mux(req_needT || req_promoteT, TIP, BRANCH)),
            clientDirResult.metas(client).state
          )
        }.otherwise{
          val stateAfterProbe_2 = shrinkNextState(probeAckParamVec(client))
          val TODO_prefetch_2 = 0.U(stateBits.W)

          newClientMeta.state := Mux(
            req_acquire,
            Mux(
              req.param =/= NtoB || req_promoteT,
              Mux(clientDirResult.hits(client) && aNeedProbe, INVALID, Mux(clientDirResult.hits(client), clientDirResult.metas(client).state, INVALID)), // TODO: Optimize logic
              // NtoB
              Mux(clientDirResult.hits(client) && aNeedProbe, stateAfterProbe_2, Mux(clientDirResult.hits(client), clientDirResult.metas(client).state, INVALID)) // TODO: Optimize logic
            ),
            Mux(
              req.opcode === Get,
              Mux(clientDirResult.hits(client) && aNeedProbe, stateAfterProbe_2, Mux(clientDirResult.hits(client), clientDirResult.metas(client).state, INVALID)), // TODO: Optimize logic
              TODO_prefetch_2
            )
          )
        }
    }


    mp_grant.meta := newMeta
    mp_grant.clientMeta := newClientMetas

    mp_grant.metaWen := true.B
    mp_grant.tagWen := !dirResult.hit

    mp_grant.clientWay := clientDirResult.way
    mp_grant.clientSet := clientDirResult.set
    mp_grant.clientTag := clientDirResult.tag
    mp_grant.clientMetaWen := true.B
    mp_grant.clientTagWen := !clientDirResult.hits.asUInt.orR

    // For Put req, dsWen is write in mp_put_wb
//    mp_grant.dsWen := !dirResult.hit && gotGrantData && hasClientHit ||
//                      probeDirty && req_get ||
//                      probeDirty && dirResult.hit
    mp_grant.dsWen := Mux(
                        nestedReleaseToN, 
                        false.B,
                        Mux(
                          dirResult.hit,
                          gotGrantData || probeDirty,
                          gotGrantData && hasClientHit || probeDirty
                        )
                      )

    mp_grant
  }


  // --------------------------------------------------------------------------
  //  MSHR write back Put request
  // --------------------------------------------------------------------------
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
    )
//    mp_put_wb.dsWen := dirResult.hit && req_put
    mp_put_wb.dsWen := true.B // TODO: consider put write bypass ?
    mp_put_wb.clientWay := clientDirResult.way
    mp_put_wb.clientSet := clientDirResult.set
    mp_put_wb.clientTag := clientDirResult.tag
    mp_put_wb
  }


  // --------------------------------------------------------------------------
  //  MainPipe task issue
  // --------------------------------------------------------------------------
  io.tasks.mainpipe.bits := ParallelPriorityMux(
    Seq(
      mp_grant_valid    -> mp_grant,
      mp_release_valid  -> mp_release,
      mp_releaseack_valid  -> mp_releaseack,
      mp_probeack_valid -> mp_probeack,
      mp_put_wb_valid   -> mp_put_wb
    )
  )
  io.tasks.mainpipe.bits.reqSource := req.reqSource


  when(mp_put_wb_valid) {
    if(cacheParams.inclusionPolicy == "NINE") {
      assert(false.B, "TODO: Put for NINE inclusion policy")
    }
  }

  assert(!(mp_probeack_valid && !req.fromProbeHelper))

  // --------------------------------------------------------------------------
  //  Task update
  // --------------------------------------------------------------------------
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
    }.elsewhen (mp_releaseack_valid) {
      state.s_releaseack := true.B
    }.elsewhen (mp_probeack_valid) {
      state.s_probeack := true.B
    }.elsewhen (mp_put_wb_valid) {
      state.s_refill := true.B
      state.s_put_wb := true.B
    }
  }


  /* ======== Refill response ======== */
  val c_resp = io.resps.sink_c
  val d_resp = io.resps.sink_d
  val e_resp = io.resps.sink_e


  val probeAckDoneClient = RegInit(0.U(clientBits.W))
  val incomingProbeAckClient = WireInit(0.U(clientBits.W))
  val probeClientsOH = Mux(req.fromProbeHelper,
                          clientDirResult.hits.asUInt,  // ProbeHelper will probe all of the client block
                          clientDirResult.hits.asUInt & ~reqClientOH
                        )
  assert(!((!state.s_pprobe || !state.s_rprobe) && !hasClientHit), "rprobe:%d pprobe:%d", state.s_rprobe, state.s_pprobe)

  // ! This is the last client sending probeack
  val probeackLast = ((probeAckDoneClient | incomingProbeAckClient) & ~nestedReleaseClientOH) === probeClientsOH || probeClientsOH === 0.U(clientBits.W)

  when(io.alloc.valid) {
    probeAckDoneClient := 0.U
  }

  dontTouch(probeackLast)
  dontTouch(incomingProbeAckClient)
  dontTouch(probeAckDoneClient)
  dontTouch(probeClientsOH)


  // --------------------------------------------------------------------------
  //  Accept D channel resp
  // --------------------------------------------------------------------------
  when(c_resp.valid && io.status.bits.w_c_resp && io.status.valid) {
    incomingProbeAckClient := getClientBitOH(io.resps.sink_c.bits.source)
    when(c_resp.bits.opcode === ProbeAck || c_resp.bits.opcode === ProbeAckData) {
      probeAckDoneClient := probeAckDoneClient | incomingProbeAckClient
      state.w_rprobeackfirst := state.w_rprobeackfirst || probeackLast
      state.w_rprobeacklast := state.w_rprobeacklast || c_resp.bits.last && probeackLast
      state.w_pprobeackfirst := state.w_pprobeackfirst || probeackLast
      state.w_pprobeacklast := state.w_pprobeacklast || c_resp.bits.last && probeackLast
      state.w_pprobeack := state.w_pprobeack || (req.off === 0.U || c_resp.bits.last) && probeackLast

      when(c_resp.bits.last) {
        val client = OHToUInt(incomingProbeAckClient)
        assert(client <= clientBits.U)

        probeAckParamVec(client) := c_resp.bits.param
        stateAfterProbe := MuxLookup(c_resp.bits.param, INVALID, Seq(
                                TtoN -> TIP,
                                BtoN -> BRANCH,
                                TtoB -> TIP
                              )
                            )
      }
    }
    when(c_resp.bits.opcode === ProbeAckData) {
      probeDirty := true.B
    }
    when(isToN(c_resp.bits.param)) {
      probeGotN := true.B
    }
    when(c_resp.bits.param === NtoN) {
      probeGotNtoNReg := true.B
    }
  }.elsewhen(c_resp.valid) { // Other probe sub request with same addr
    // TODO:
  }

  probeGotNtoN := Mux(
    c_resp.bits.param === NtoN && c_resp.valid && io.status.bits.w_c_resp && io.status.valid,
    true.B,
    probeGotNtoNReg
  )


  // --------------------------------------------------------------------------
  //  Accept D channel resp
  // --------------------------------------------------------------------------
  val releaseNextState = RegInit(true.B)
  val releaseackNextState = RegInit(true.B)
  when(io.alloc.valid) {
    releaseNextState := true.B
    releaseackNextState := true.B
  }

  // val dirAddrMatch_1 = req.set === io.nestedwb.set && dirResult.tag === io.nestedwb.tag
  // when(nestedWbMatch && io.nestedwb.fromB && io.nestedwb.b_toN && dirAddrMatch_1) {
  //   when(!state.w_releaseack) {
  //     releaseackNextState  := false.B // Bufferd extra release ack
  //   }
  // }

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
      // state.w_releaseack := releaseackNextState // true.B
      // releaseackNextState := true.B
    }
  }


  // --------------------------------------------------------------------------
  //  Accept E channel resp
  // --------------------------------------------------------------------------
  when (e_resp.valid) {
    state.w_grantack := true.B
  }


  // --------------------------------------------------------------------------
  //  Source C channel monitor
  // --------------------------------------------------------------------------
  when (io.resps.source_c.valid) {
    state.w_release_sent := true.B
  }


  // --------------------------------------------------------------------------
  //  MSHR unlock logic
  // --------------------------------------------------------------------------
  when (status_reg.valid) {
    timer := timer + 1.U
  }
  
  val no_schedule = state.s_refill && state.s_probeack
  val no_wait = state.w_rprobeacklast && state.w_pprobeacklast && state.w_grantlast && state.w_releaseack && state.w_grantack && state.w_probehelper_done && state.w_release_sent 
  val will_free = no_schedule && no_wait && !waitNestedC && !waitNestedB && !nestedWbMatch && !needWaitNestedC
  
  val mshrTaskIsFireReg = RegInit(false.B)
  val mshrTaskIsFire = Mux(io.mshrTaskIsFire, true.B, mshrTaskIsFireReg)
  when (io.alloc.valid) {
    mshrTaskIsFireReg := false.B
  }.elsewhen(io.mshrTaskIsFire) {
    mshrTaskIsFireReg := true.B
  }

  when (will_free && status_reg.valid && mshrTaskIsFire) {
    status_reg.valid := false.B
    timer := 0.U
  }


  // --------------------------------------------------------------------------
  //  Status report
  // --------------------------------------------------------------------------
  io.status.valid := status_reg.valid
  io.status.bits <> status_reg.bits
  // For A reqs, we only concern about the tag to be replaced
  io.status.bits.tag := Mux(state.w_release_sent, req.tag, dirResult.tag) // s_release is low-as-valid
  io.status.bits.nestB := status_reg.valid && state.w_releaseack && state.w_rprobeacklast && state.w_pprobeacklast && !waitNestedC && (!state.w_grantfirst || !state.w_probehelper_done) && !status_reg.bits.fromC // allow nested probehelper req
  io.status.bits.nestC := status_reg.valid && Mux(waitNestedB || req.fromProbeHelper, true.B, state.w_releaseack) && MuxCase(false.B, Seq(
    req.fromA -> (!state.s_refill && !mp_grant_valid),
    req.fromB -> (!mp_probeack_valid && !mp_release_valid),
    req.fromC -> false.B
  ))

  // wait for resps, high as valid
  io.status.bits.w_c_resp := !state.w_rprobeacklast || !state.w_pprobeacklast || !state.w_pprobeack
  io.status.bits.w_d_resp := !state.w_grantlast || !state.w_grant || !state.w_releaseack
  io.status.bits.w_e_resp := !state.w_grantack
  io.status.bits.will_free := will_free
  io.status.bits.is_miss := !dirResult.hit
  io.status.bits.is_prefetch := req_prefetch


  // --------------------------------------------------------------------------
  //  Info for the request buffer
  // --------------------------------------------------------------------------
  io.toReqBuf.valid := status_reg.valid
  io.toReqBuf.bits.set := req.set
  io.toReqBuf.bits.way := req.way
  io.toReqBuf.bits.reqTag := req.tag
  io.toReqBuf.bits.needRelease := !state.w_release_sent
  io.toReqBuf.bits.metaTag := dirResult.tag
  io.toReqBuf.bits.willFree := will_free
  io.toReqBuf.bits.isAcqOrPrefetch := req_acquire
  io.toReqBuf.bits.isChannelC := req.fromC

  when(status_reg.valid) {
    assert(!(c_resp.valid && !io.status.bits.w_c_resp), "mshrId:%d", io.id)
    assert(!(d_resp.valid && !io.status.bits.w_d_resp), "mshrId:%d", io.id)
    assert(!(e_resp.valid && !io.status.bits.w_e_resp), "mshrId:%d", io.id)
  }



  // --------------------------------------------------------------------------
  //  Nested write back logic
  // --------------------------------------------------------------------------
  /**
    * Nested cases:
    *   1) B nest A 
    *         B________________B_Resp
    *       A________________________A_Resp
    * 
    *   2) C nest A
    *         C________________C_Resp
    *       A________________________A_Resp
    * 
    *   3) C nest B
    *         C________________C_Resp
    *       B________________________B_Resp
    * 
    *   4) C nest B nest A
    *           C________C_Resp
    *         B________________B_Resp
    *       A________________________A_Resp
    * 
    */
  val reqAddrMatch = req.set === io.nestedwb.set && req.tag === io.nestedwb.tag
  val dirAddrMatch = req.set === io.nestedwb.set && dirResult.tag === io.nestedwb.tag
  val clientTag = Cat(clientDirResult.tag, clientDirResult.set) >> setBits.U
  val clientDirAddrMatch = req.set === io.nestedwb.set && clientTag === io.nestedwb.tag
  val nestedAddrMatch = dirAddrMatch || clientDirAddrMatch || reqAddrMatch
  dontTouch(reqAddrMatch)
  dontTouch(dirAddrMatch)
  dontTouch(clientDirAddrMatch)
  dontTouch(nestedAddrMatch)
  // Cache line is not occupied when meta.state === INVALID.
  // Nested condition can only happen when the address match the other valid address(meta.state =/= INVALID) hold by MSHR.
  // If nested happen, we should update our own meta info, then we will not need to read directory again and still keep our meta updated.
  nestedWbMatch := status_reg.valid && nestedAddrMatch && io.nestedwb.valid
  nestedValid := nestedWbMatch
  when(io.alloc.valid) {
    waitNestedC := false.B
    nestedSourceIdC := DontCare
    nestedReleaseNeedRelease := false.B
    nestedReleaseClientOH := 0.U
    nestedReleaseToN := false.B
    waitNestedB := false.B
    nestedSourceIdB := DontCare
    nestedProbeToN := false.B
    needWaitNestedC := false.B
  }
  
  when(probeGotNtoN && !nestedReleaseToN) {
    waitNestedC := true.B
    needWaitNestedC := true.B
  }

  when(nestedWbMatch) {
    // Nest B
    //    B nest A
    // Not happen in noninclusive-L3 since L3 is Last Level Cache(LLC), probe req from outside the L3 cannot reach.
    when(io.nestedwb.fromB) {
      waitNestedB := io.nestedwb.needMSHR
      nestedSourceIdB := io.nestedwb.sourceId

      // TODO: consider ProbeHelper nest
      when(dirAddrMatch) {
        nestedProbeToN := true.B

        when(io.nestedwb.b_toN) {
          val clientsHasTIP = Cat(dirResult.meta.clientStates.map( state => state === TIP )).orR
          val stateAfterProbeHelper = Mux(clientsHasTIP, TIP, BRANCH)
          dirResult.meta.state := stateAfterProbeHelper
          dirResult.meta.dirty := true.B
          dirResult.meta.clientStates.foreach(_ := INVALID)

          when(stateAfterProbeHelper === TIP) {
            state.s_release := false.B
            state.w_releaseack := false.B
          }
        }
      } // dirAddrMatch

      when(clientDirAddrMatch) {
        when(io.nestedwb.b_toN) {
          clientDirResult.hits.foreach(_ := false.B)
          clientDirResult.metas.foreach(_.state := INVALID)
        }

        when(!state.s_rprobe) {
          state.s_rprobe := true.B
          state.w_rprobeackfirst := true.B
          state.w_rprobeacklast := true.B
        }
      }
    } // fromB


    // Nest C
    //    C nest A || C nest B
    // noninclusive L3 only meet with C nest A
    when(io.nestedwb.fromC) {
      waitNestedC := io.nestedwb.needMSHR // If a nested request does not need MSHR, then we just update nested info.
      nestedSourceIdC := io.nestedwb.sourceId

      when(dirAddrMatch) {
        nestedReleaseToN := dirResult.hit

        when(io.nestedwb.c_set_dirty) { // Accept ReleaseData will set this flag
          meta.dirty := true.B
        }

        when(io.nestedwb.c_toN) {
          dirResult.way := io.nestedwb.way

          when(dirResult.meta.state === TRUNK) {
            dirResult.meta.state := TIP
            dirResult.meta.dirty := true.B
            dirResult.meta.clientStates.zip(io.nestedwb.c_client.asBools).foreach{
              case(clientState, en) =>
                clientState := Mux(en, INVALID, clientState)
            }
            when(~dirResult.hit) {
              nestedReleaseNeedRelease := true.B
              state.s_release := false.B
              state.w_releaseack := false.B
            }
          }

          when(dirResult.meta.state === TIP) {
            dirResult.meta.clientStates.zip(io.nestedwb.c_client.asBools).foreach {
              case (clientState, en) =>
                clientState := Mux(en, INVALID, clientState)
            }
          }

        } // io.nestedwb.c_toN
      } // dirAddrMatch

      // TODO: Only nested probehelper
      when(clientDirAddrMatch) { // Only hit clientResult can be modified
        needWaitNestedC := false.B
        nestedReleaseClientOH := io.nestedwb.c_client

        when(io.nestedwb.c_toN) {
          clientDirResult.hits.zip(io.nestedwb.c_client.asBools).foreach {
            case (clientHit, en) =>
              when(io.nestedwb.c_toN) {
                clientHit := clientHit & ~en
              }
          }

          clientDirResult.metas.zip(io.nestedwb.c_client.asBools).foreach {
            case (clientMeta, en) =>
              when(io.nestedwb.c_toN) {
                clientMeta.state := Mux(en, INVALID, clientMeta.state)
              }

              when(io.nestedwb.c_toB) {
                clientMeta.state := Mux(en, BRANCH, clientMeta.state)
              }
          }
        } // io.nestedwb.c_toN

        when(io.nestedwb.c_toB) { // Only hit clientResult can be modified
          clientDirResult.metas.zip(io.nestedwb.c_client.asBools).foreach {
            case (clientMeta, en) =>
              clientMeta.state := Mux(en, BRANCH, clientMeta.state)
          }
        } // io.nestedwb.c_toB

        val nestedwbMatchReqState = io.tasks.source_b.bits.param === toB && (io.nestedwb.c_toB || io.nestedwb.c_toN) ||
                                    io.tasks.source_b.bits.param === toN && io.nestedwb.c_toN
        when(!state.s_rprobe && nestedwbMatchReqState) {
          state.s_rprobe := true.B
          state.w_rprobeackfirst := true.B
          state.w_rprobeacklast := true.B
        }

        when(!state.s_pprobe && nestedwbMatchReqState) {
          state.s_pprobe := true.B
          state.w_pprobeackfirst := true.B
          state.w_pprobeacklast := true.B
        }

      } // clientDirAddrMatch

      when(reqAddrMatch && !dirAddrMatch) {
        // assert(hasClientHit)
        nestedReleaseToN := true.B

        when(io.nestedwb.c_toN) {
          dirResult.hit := true.B
          dirResult.way := io.nestedwb.way
          dirResult.tag := io.nestedwb.tag
          dirResult.meta.dirty := true.B
          dirResult.meta.state := clientDirResult.metas(OHToUInt(io.nestedwb.c_client)).state
          dirResult.meta.clientStates.zipWithIndex.foreach{
            case(clientMeta, client) =>
              clientMeta := Mux(io.nestedwb.c_client === UIntToOH(client.U), INVALID, clientDirResult.metas(client).state)
          }
          req.way := io.nestedwb.way
          
          when(!state.s_release) {
            state.s_release := true.B
            state.w_releaseack := true.B

            // ProbeHelper need probeack to write meta
            state.s_probeack := !req.fromProbeHelper
          }
        }
      } // reqAddrMatch
    } // fromC
   } // nested match

  //  Wakeup nested pending task
  when(io.nestedwb.wakeupValid) {
    when(waitNestedC && io.nestedwb.wakeupSourceId === nestedSourceIdC) {
      waitNestedC := false.B
    }
    when(waitNestedB && io.nestedwb.wakeupSourceId === nestedSourceIdB && io.nestedwb.fromProbeHelper) {
      waitNestedB := false.B
    }
  }


  // If this MSHR is trigger by ProbeHelper we won't write back nested data from the target Release block,
  // which will prevent releaseBuf from being write twice simutaneously. (i.e. one from SinkC and the other from MainPipe)
  // io.nestedwbData := nestedwb_match && io.nestedwb.c_set_dirty && !req.fromProbeHelper
  io.nestedwbData := false.B


  // Waitting for ProbeHelper task finish
  val phAddrMatch = clientDirResult.set === io.probeHelperWakeup.set && clientDirResult.tag === io.probeHelperWakeup.tag
  val phWakeupMatch = status_reg.valid && !state.w_probehelper_done && io.probeHelperWakeup.valid && phAddrMatch
  when(phWakeupMatch) {
    state.w_probehelper_done := true.B
  }
  


  dontTouch(state)

  assert(!(status_reg.valid && timer >= 15000.U), "mshr timeout! cnt:%d id:%d addr:0x%x", timer, io.id, Cat(status_reg.bits.tag, status_reg.bits.set))

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
