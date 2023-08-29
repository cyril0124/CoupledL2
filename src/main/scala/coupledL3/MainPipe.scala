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
import utility._
import utility.ParallelMax
import coupledL3.MetaData._
import chipsalliance.rocketchip.config.Parameters
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tilelink.TLMessages._
import freechips.rocketchip.tilelink.TLPermissions._
import coupledL3.utils._
import coupledL3.debug._
import coupledL3.prefetch.PrefetchTrain
import chisel3.util.experimental.BoringUtils
import coupledL3.noninclusive.ClientDirResult

class MainPipe(implicit p: Parameters) extends L3Module with noninclusive.HasClientInfo {
  val io = IO(new Bundle() {
    /* receive task from arbiter at stage 2 */
    val taskFromArb_s2 = Flipped(DecoupledIO(new TaskBundle()))

    /* handle set conflict in req arb */
    val fromReqArb = Input(new Bundle() {
      val status_s1 = new PipeEntranceStatus
    })
    /* block B and C at Entrance */
    val toReqArb = Output(new BlockInfo())

    /* block A at Entrance */
    val toReqBuf = Output(Vec(2, Bool()))

    /* handle capacity conflict of GrantBuffer */
    val status_vec = Vec(3, ValidIO(new PipeStatus))

    /* get dir result at stage 3 */
    val dirResp_s3 = Input(new DirResult)

    /* get client dir result at stage 3 */
    val clientDirResp_s3 = Input(new noninclusive.ClientDirResult)

    /* get ProbeHelper info */
    val clientDirConflict = Input(Bool())

    /* send task to MSHRCtl at stage 3 */
    val toMSHRCtl = new Bundle() {
      val mshr_alloc_s3 = ValidIO(new MSHRRequest())
    }

    val fromMSHRCtl = new Bundle() {
      val mshr_alloc_ptr = Input(UInt(mshrBits.W))
    }

    /* read C-channel Release Data and write into DS */
    val bufRead = Output(ValidIO(new PipeBufferRead))
    val bufResp = Input(new PipeBufferResp)

    /* read A-channel PutFullData/PutPartial Data and write into DS */
    val putBufRead = Output(ValidIO(new PutBufferRead))
    val putBufResp = Input(Vec(beatSize, new PutBufferEntry))
    val toSinkA = Output(new Bundle {
      val putReqGood_s3 = Bool()
    })

    /* get MSHR buffer read result */
    val mshrBufResp_s3 = Flipped(ValidIO(new MSHRBufReadResp))

    /* get PutDataBuffer read result */
    val putDataBufResp_s3 = Flipped(ValidIO(new DSBlock))

    /* read or write data storage */
    val toDS = new Bundle() {
      val req_s3 = DecoupledIO(new DSRequest)
      val rdata_s5 = Input(new DSBlock)
      val error_s5 = Input(Bool())
      val wdata_s3 = Output(new DSBlock)
    }

    /* send Release/Grant/ProbeAck via SourceC/D channels */
    val toSourceC, toSourceD = DecoupledIO(new Bundle() {
      val task = new TaskBundle
      val data = new DSBlock
    })

    /* write dir, including reset dir */
    val metaWReq = DecoupledIO(new MetaWrite)
    val tagWReq = DecoupledIO(new TagWrite)


    /* write client dir */
    val clientMetaWReq = DecoupledIO(new noninclusive.ClientMetaWrite)
    val clientTagWReq = DecoupledIO(new noninclusive.ClientTagWrite)
    val clientBusyWakeup = ValidIO(new noninclusive.ClientBusyWakeup)

    // /* read DS and write data into MSHRBuffer which will be used in the future */
    val mshrBufWrite = DecoupledIO(new MSHRBufWrite())

    /* read DS and write data into PutDataBuf when req is Put and need to alloc MSHR */
    val putDataBufWrite = Flipped(new LookupBufWrite())

    val nestedwb = Output(new NestedWriteback)
    val nestedwbData = Output(new DSBlock)

    val probeHelperWakeup = Output(new ProbeHelperWakeupInfo) // Only for NINE

    val pipeFlow_s2 = Output(Bool())
    val pipeFlow_s3 = Output(Bool())
    val acceptDirResp = Output(Bool())

    val fromReqBufSinkA = Input(new Bundle{
      val valid = Bool()
      val set = UInt(setBits.W)
    })
  })

  val resetFinish = RegInit(false.B)
  val resetIdx = RegInit((cacheParams.sets - 1).U)
  val resetFinishClient = RegInit(false.B)
  val resetIdxClient = RegInit((clientSets - 1).U)
  /* block reqs when reset */
  when(!resetFinish && io.metaWReq.fire) {
    resetIdx := resetIdx - 1.U
  }
  when(resetIdx === 0.U) {
    resetFinish := true.B
  }

  when(!resetFinishClient && io.clientMetaWReq.fire) {
    resetIdxClient := resetIdxClient - 1.U
  }
  when(resetIdxClient === 0.U) {
    resetFinishClient := true.B
  } 

  val c_s3, c_s5 = Wire(io.toSourceC.cloneType)
  val d_s3, d_s5 = Wire(io.toSourceD.cloneType)
  val c_s4 = WireInit(0.U.asTypeOf(io.toSourceC))
  val d_s4 = WireInit(0.U.asTypeOf(io.toSourceD))

  require(cacheParams.inclusionPolicy == "NINE", "For this repo, L3 only support NINE")

  val s3_valid, s3_ready, s3_fire = Wire(Bool())
  val s4_valid, s4_ready, s4_fire = Wire(Bool())
  val s5_valid, s5_ready, s5_fire = Wire(Bool())

  val s3_full = RegInit(false.B)
  val s4_full = RegInit(false.B)
  val s5_full = RegInit(false.B)

  
  // --------------------------------------------------------------------------
  //  Stage2: 
  // --------------------------------------------------------------------------
  // send out MSHR task if data is not needed
  val task_s2 = io.taskFromArb_s2
  val hasData_s2 = task_s2.bits.opcode(0)
  val req_opcode = task_s2.bits.opcode
  val req_put_s2 = (req_opcode === PutFullData || req_opcode === PutPartialData) && !task_s2.bits.mshrTask
  val mshr_put_s2 = (req_opcode === PutFullData || req_opcode === PutPartialData) && task_s2.bits.mshrTask && task_s2.bits.opcodeIsReq

  io.putBufRead <> DontCare
  io.putBufRead.valid := task_s2.valid && task_s2.bits.fromA && (req_put_s2 || mshr_put_s2)
  io.putBufRead.bits.idx := task_s2.bits.pbIdx
  io.putBufRead.bits.isMSHRTask := task_s2.bits.mshrTask

  task_s2.ready := s3_ready

  // --------------------------------------------------------------------------
  //  Stage3: 
  // --------------------------------------------------------------------------
  val req_drop_s3 = Wire(Bool())
  val willAccessDS = Wire(Bool())
  val willAccessDirMeta = Wire(Bool())
  val willAccessDirTag = Wire(Bool())
  val willAccessClientDirMeta = Wire(Bool())
  val willAccessClientDirTag = Wire(Bool())

  val sendSourceC, sendSourceD = RegInit(false.B)
  val willSendSourceC = Wire(Bool())
  val willSendSourceD = Wire(Bool())

  val s2_fire = task_s2.fire // task_s2.valid && s3_ready
  s3_ready := !s3_full || s3_fire
  s3_valid := s3_full && (
    !(willAccessDS            && !io.toDS.req_s3.ready   ) && 
    !(willAccessDirMeta       && !io.metaWReq.ready      ) && 
    !(willAccessDirTag        && !io.tagWReq.ready       ) &&
    !(willAccessClientDirMeta && !io.clientMetaWReq.ready) &&
    !(willAccessClientDirTag  && !io.clientTagWReq.ready ) &&
    !(willSendSourceC && !c_s3.ready && !sendSourceC     ) &&
    !(willSendSourceD && !d_s3.ready && !sendSourceD     )
  )
  // s3_fire := s3_valid && s4_ready
  s3_fire := s3_valid && s5_ready // TODO:
  when(s2_fire) {
    s3_full := true.B 
  }.elsewhen(s3_fire) {
    s3_full := false.B
  }
  

  io.pipeFlow_s2 := s2_fire
  io.pipeFlow_s3 := s3_fire


  val task_s3 = RegInit(0.U.asTypeOf(Valid(new TaskBundle())))
  // val task_s3 = RegInit(0.U.asTypeOf(Decoupled(new TaskBundle())))
  // task_s3.valid := task_s2.valid
  // when(task_s2.valid) {
  //   task_s3.bits := task_s2.bits
  // }

  io.acceptDirResp := s3_fire && !task_s3.bits.mshrTask


  when(s2_fire) {
    task_s3.valid := true.B
    task_s3.bits := task_s2.bits
  }.elsewhen(s3_fire) {
    task_s3.valid := false.B
  }


  //  TODO: debug address consider multi-bank
  def restoreAddr(set: UInt, tag: UInt) = {
    (set << offsetBits).asUInt + (tag << (setBits + offsetBits)).asUInt
  }
  val debug_addr_s3 = restoreAddr(task_s3.bits.set, task_s3.bits.tag) // (task_s3.bits.set << offsetBits).asUInt + (task_s3.bits.tag << (setBits + offsetBits)).asUInt
  dontTouch(debug_addr_s3)


  /* ======== Enchantment ======== */
  // self dir result
  val gotDirResult_s3 = RegInit(false.B)
  val dirResultReg_s3 = RegInit(0.U.asTypeOf(io.dirResp_s3))
  // val dirResult_s3 = io.dirResp_s3
  val dirResult_s3 = Mux(gotDirResult_s3, dirResultReg_s3, io.dirResp_s3)
  val meta_s3 = dirResult_s3.meta
  val meta_error_s3 = dirResult_s3.error
  when(s3_fire) { 
    gotDirResult_s3 := false.B
  }.elsewhen(RegNext(s2_fire)) {
    gotDirResult_s3 := true.B
    dirResultReg_s3 := io.dirResp_s3
  }
  when(~reset.asBool) {
    assert(!RegNext(dirResult_s3.set =/= task_s3.bits.set && task_s3.valid && !task_s3.bits.mshrTask), "dirResult_s3.set:%d =/= task_s3.bits.set:%d mshrTask:%d", RegNext(dirResult_s3.set), RegNext(task_s3.bits.set), RegNext(task_s3.bits.mshrTask))
  }

  def selfToClientDirResult(selfDir: DirResult, clientDir: noninclusive.ClientDirResult): noninclusive.ClientDirResult = {
    val clientDirResult = WireInit(0.U.asTypeOf(new noninclusive.ClientDirResult))
    clientDirResult.set := clientDir.set
    clientDirResult.tag := clientDir.tag
    clientDirResult.way := clientDir.way
    clientDirResult.replacerInfo := clientDir.replacerInfo
    clientDirResult.hits := selfDir.meta.clientStates.map( m => m =/= INVALID )
    clientDirResult.error := false.B // TODO:
    // clientDirResult.metas := selfDir.meta.clientStates.asTypeOf(Vec(clientBits, new noninclusive.ClientMetaEntry()))
    clientDirResult.metas.zipWithIndex.foreach{ 
      case(m, i) => 
        m.state := selfDir.meta.clientStates(i)
    } 
    clientDirResult
  }

  // client dir result (Only for NINE)
  val gotClientDirResult_s3 = RegInit(false.B)
  val clientDirResultReg_s3 = RegInit(0.U.asTypeOf(io.clientDirResp_s3))
  val clientDirResult_s3_1 = Mux(gotClientDirResult_s3, clientDirResultReg_s3, io.clientDirResp_s3)
  val clientDirResult_s3 = Mux(dirResult_s3.hit, selfToClientDirResult(dirResult_s3, clientDirResult_s3_1), clientDirResult_s3_1)
  val clientMetas_s3 = clientDirResult_s3.metas
  val hasClientHit = clientDirResult_s3.hits.asUInt.orR
  dontTouch(clientDirResult_s3) // TODO: NINE

  val clientDirMetaNotMatch = !Cat(dirResult_s3.meta.clientStates.zipWithIndex.map{
    case(clientState, i) =>
      clientState === clientDirResult_s3_1.metas(i).state
  }).andR
  val clientHasHit = clientDirResult_s3_1.hits.asUInt.orR
  assert(!(dirResult_s3.hit && clientHasHit && clientDirMetaNotMatch && s3_valid), 
          "clientState not match self clientState, set:%x tag:%x mshrTask:%d sourceId:%d channel:%x addr:%x", 
          task_s3.bits.set, task_s3.bits.tag, task_s3.bits.mshrTask, task_s3.bits.sourceId, task_s3.bits.channel, debug_addr_s3
        )

  when(s3_fire) { 
    gotClientDirResult_s3 := false.B
  }.elsewhen(RegNext(s2_fire)) {
    gotClientDirResult_s3 := true.B
    clientDirResultReg_s3 := io.clientDirResp_s3
  }


  val gotClientDirConflict_s3 = RegInit(false.B)
  val clientDirConflict_s3 = Mux(gotClientDirResult_s3, gotClientDirConflict_s3, io.clientDirConflict)
  when(s3_fire) {
    gotClientDirConflict_s3 := false.B
  }.elsewhen(RegNext(s2_fire)) {
    gotClientDirConflict_s3 := io.clientDirConflict
  }

  val req_s3 = task_s3.bits
  val mshr_req_s3 = req_s3.mshrTask
  val sink_req_s3 = !mshr_req_s3
  val sinkA_req_s3 = !mshr_req_s3 && req_s3.fromA
  val sinkB_req_s3 = !mshr_req_s3 && req_s3.fromB
  val sinkC_req_s3 = !mshr_req_s3 && req_s3.fromC

  val req_needT_s3 = needT(req_s3.opcode, req_s3.param) // require T status to handle req
  val req_acquire_s3 = sinkA_req_s3 && (req_s3.opcode === AcquireBlock || req_s3.opcode === AcquirePerm)
  val req_acquireBlock_s3 = sinkA_req_s3 && req_s3.opcode === AcquireBlock
  val req_get_s3 = sinkA_req_s3 && req_s3.opcode === Get
  val req_put_full_s3 = sinkA_req_s3 && req_s3.opcode === PutFullData
  val req_put_partial_s3 = sinkA_req_s3 && req_s3.opcode === PutPartialData
  val req_put_s3 = req_put_full_s3 || req_put_partial_s3

  val mshr_grant_s3 = mshr_req_s3 && req_s3.fromA && req_s3.opcode(2, 1) === Grant(2, 1) // Grant or GrantData from mshr
  val mshr_grantdata_s3 = mshr_req_s3 && req_s3.fromA && req_s3.opcode === GrantData
  val mshr_accessackdata_s3 = mshr_req_s3 && req_s3.fromA && req_s3.opcode === AccessAckData
  val mshr_accessack_s3 = mshr_req_s3 && req_s3.fromA && req_s3.opcode === AccessAck
  val mshr_probeack_s3 = mshr_req_s3 && req_s3.fromB && req_s3.opcode(2, 1) === ProbeAck(2, 1) // ProbeAck or ProbeAckData from mshr
  val mshr_probeackdata_s3 = mshr_req_s3 && req_s3.fromB && req_s3.opcode === ProbeAckData
  val mshr_release_s3 = mshr_req_s3 && req_s3.opcode(2, 1) === Release(2, 1) // voluntary Release or ReleaseData from mshr
  val mshr_releaseack_s3 = mshr_req_s3 && req_s3.fromC && req_s3.opcode === ReleaseAck // only for NINE
  val mshr_putpartial_s3 = mshr_req_s3 && req_s3.fromA && req_s3.opcode === PutPartialData && req_s3.opcodeIsReq
  val mshr_putfull_s3 = mshr_req_s3 && req_s3.fromA && req_s3.opcode === PutFullData && req_s3.opcodeIsReq
  val mshr_put_s3 = mshr_putpartial_s3 || mshr_putfull_s3

  
  // Clients releted signal
  val reqClient   = RegInit(0.U((log2Up(clientBits) + 1).W)) // Which client does this req come from?
  val reqClientOH = RegInit(0.U(clientBits.W)) // getClientBitOH(task_s3.bits.sourceId) // ! This is only for channel task
  when(s2_fire) {
    val reqClientOHWire = getClientBitOH(task_s2.bits.sourceId)
    reqClientOH := reqClientOHWire
    reqClient := Mux(reqClientOHWire === 0.U, Cat(1.U(1.W), 0.U(log2Up(clientBits).W)), OHToUInt(reqClientOHWire)) // The highest bit of reqClient indicates that req comes from TL-UL node
  }

  // Deal with coherence
  val willAllocMSHR = Wire(Bool())
  val cohChecker         = Module(new CohChecker())
  val cache_alias        = cohChecker.io.out.flags.cacheAlias
  val need_mshr_s3       = cohChecker.io.out.flags.needMSHR
  val a_need_replacement = cohChecker.io.out.flags.aNeedReplacement
  val c_need_replacement = cohChecker.io.out.flags.cNeedReplacement
  val need_probe_s3_a    = cohChecker.io.out.flags.aNeedProbe
  val need_mshr_s3_a     = cohChecker.io.out.flags.aNeedMSHR
  val need_mshr_s3_b     = cohChecker.io.out.flags.bNeedMSHR
  val need_mshr_s3_c     = cohChecker.io.out.flags.cNeedMSHR
  // cohChecker.io.in <> DontCare
  cohChecker.io.in.task <> task_s3
  cohChecker.io.in.dirResult := dirResult_s3
  cohChecker.io.in.clientDirResult := clientDirResult_s3
  cohChecker.io.in.clientDirConflict := clientDirConflict_s3
  io.toMSHRCtl.mshr_alloc_s3 <> cohChecker.io.out.mshrAlloc
  willAllocMSHR := cohChecker.io.out.mshrAlloc.valid
  io.toMSHRCtl.mshr_alloc_s3.valid := willAllocMSHR && s3_fire
  

  /* ======== Resps to SinkA/B/C Reqs ======== */
  val sink_resp_s3 = WireInit(0.U.asTypeOf(Valid(new TaskBundle))) // resp for sinkA/B/C request that does not need to alloc mshr
  val mainpipe_release = a_need_replacement || c_need_replacement
  
  val exceptReqClientHasB = VecInit(clientDirResult_s3.metas.zipWithIndex.map{
    case (meta, client) => 
      Mux(reqClient === client.U, false.B, meta.state === BRANCH)
  }).asUInt.orR
  val sink_resp_s3_a_promoteT = dirResult_s3.hit && isT(meta_s3.state) && !exceptReqClientHasB

  sink_resp_s3.valid := task_s3.valid && !mshr_req_s3 && (!need_mshr_s3 || mainpipe_release)
  sink_resp_s3.bits := task_s3.bits
  sink_resp_s3.bits.mshrId := Mux(
                                  mainpipe_release, 
                                  io.fromMSHRCtl.mshr_alloc_ptr, // for NINE, mainpipe release will alloc a MSHR
                                  mshrsAll.U + sink_resp_s3.bits.sourceId // extra id for reqs that do not enter mshr
                                  // (1 << (mshrBits - 1)).U + sink_resp_s3.bits.sourceId // extra id for reqs that do not enter mshr
                                )
    

  when(meta_error_s3) {
    when(req_s3.fromA) {
      // Sink resp for channel d
      sink_resp_s3.bits.opcode := odOpGen(req_s3.opcode)
      sink_resp_s3.bits.param := Mux(
        req_acquire_s3,
        Mux(req_s3.param === NtoB && !sink_resp_s3_a_promoteT, toB, toT),
        0.U // reserved
      )
      sink_resp_s3.bits.denied := true.B
    }.elsewhen(req_s3.fromB) {
      // Sink resp for channel c
      sink_resp_s3.bits.opcode := ProbeAck // TODO: Non-inclusive
      sink_resp_s3.bits.corrupt := true.B // channel c does not have denied field so we use corrupt for tag error condition
    }.otherwise { // req_s3.fromC
      // Sink resp for channel d
      sink_resp_s3.bits.opcode := ReleaseAck
      sink_resp_s3.bits.param := 0.U // param of ReleaseAck must be 0
      sink_resp_s3.bits.denied := true.B
    }
  }.otherwise {
    when(req_s3.fromA) {
      when(mainpipe_release) { // replacement-Release for A-miss
        sink_resp_s3.bits.opcode := {
          cacheParams.releaseData match {
            case 0 => Mux(meta_s3.dirty, ReleaseData, Release)
//            case 1 => Mux(meta_s3.dirty && meta_s3.accessed, ReleaseData, Release)
            case 2 => ReleaseData
            case 3 => ReleaseData
          }
        }
        sink_resp_s3.bits.param := Mux(isT(meta_s3.state), TtoN, BtoN)
        // sink_resp_s3.bits.mshrId is changed to mshr_alloc_ptr at stage 4
        // so source of C-Release is correct
        sink_resp_s3.bits.tag := dirResult_s3.tag
        sink_resp_s3.bits.dirty := meta_s3.dirty

      }.otherwise { // Grant for A-hit
        sink_resp_s3.bits.opcode := odOpGen(req_s3.opcode)
        sink_resp_s3.bits.param := Mux(
          req_acquire_s3,
          Mux(req_s3.param === NtoB && !sink_resp_s3_a_promoteT, toB, toT),
          0.U // reserved
        )
      }
    }.elsewhen(req_s3.fromB) {
      sink_resp_s3.bits.opcode := Mux(
        dirResult_s3.hit && (meta_s3.state === TIP && meta_s3.dirty || req_s3.needProbeAckData),
        ProbeAckData,
        ProbeAck
      )
      sink_resp_s3.bits.param := Mux(!dirResult_s3.hit, NtoN,
        MuxLookup(Cat(req_s3.param, meta_s3.state), BtoB, Seq(
          Cat(toN, BRANCH) -> BtoN,
          Cat(toN, TIP) -> TtoN,
          Cat(toB, TIP) -> TtoB,
          Cat(toT, TIP) -> TtoT
        )) // other combinations should miss or have mshr allocated
      )
    }.otherwise { // req_s3.fromC
      when(mainpipe_release) {
        sink_resp_s3.bits.opcode := {
          cacheParams.releaseData match {
            case 0 => Mux(meta_s3.dirty, ReleaseData, Release)
//            case 1 => Mux(meta_s3.dirty && meta_s3.accessed, ReleaseData, Release)
            case 2 => ReleaseData
            case 3 => ReleaseData
          }
        }
        sink_resp_s3.bits.param := Mux(isT(meta_s3.state), TtoN, BtoN)
        sink_resp_s3.bits.tag := dirResult_s3.tag
        sink_resp_s3.bits.dirty := meta_s3.dirty
      }.otherwise{
        sink_resp_s3.bits.opcode := ReleaseAck
        sink_resp_s3.bits.param := 0.U // param of ReleaseAck must be 0
      }
    }
  }

  val source_req_s3 = Wire(new TaskBundle)
  source_req_s3 := Mux(sink_resp_s3.valid, sink_resp_s3.bits, req_s3)


  /* ======= Report put status ======= */
  io.toSinkA.putReqGood_s3 := req_put_full_s3 && !need_mshr_s3_a


  /* ======== Interact with DS ======== */
  val gotMSHRBufResp_s3 = RegInit(false.B)
  val mshrBufRespReg_s3 = RegInit(0.U.asTypeOf(io.mshrBufResp_s3.bits.data))
  when(s3_fire) { 
    gotMSHRBufResp_s3 := false.B
  }.elsewhen(io.mshrBufResp_s3.valid && !gotMSHRBufResp_s3) {
    mshrBufRespReg_s3 := io.mshrBufResp_s3.bits.data
    gotMSHRBufResp_s3 := true.B
  }

  val mshrBufData = Mux(gotMSHRBufResp_s3, mshrBufRespReg_s3, io.mshrBufResp_s3.bits.data)
  val data_s3 = mshrBufData

  val hasData_s3 = source_req_s3.opcode(0)
  // assert(!(io.refillBufResp_s3.valid && io.releaseBufResp_s3.valid), "can not read both refillBuf and releaseBuf at the same time")

  val wen_a = req_put_full_s3 && io.toSinkA.putReqGood_s3
  val wen_c = sinkC_req_s3 && req_s3.opcode(0) && !need_mshr_s3
  val wen = wen_c || wen_a || req_s3.dsWen && (mshr_grant_s3 || mshr_accessackdata_s3 || mshr_probeack_s3 || mshr_put_s3 || mshr_releaseack_s3)


  val need_data_on_hit_a = req_get_s3 || req_acquireBlock_s3 || req_put_partial_s3
  val need_data_on_miss_a = a_need_replacement // read data ahead of time to prepare for ReleaseData later
  val need_data_on_miss_c = c_need_replacement
  val need_data_b = sinkB_req_s3 && dirResult_s3.hit &&
    (meta_s3.state === TRUNK || meta_s3.state === TIP && meta_s3.dirty || req_s3.needProbeAckData)
  val ren = Mux(dirResult_s3.hit, need_data_on_hit_a, need_data_on_miss_a || need_data_on_miss_c) || need_data_b || task_s3.bits.selfHasData && mshr_req_s3
  val bufResp_s3 = io.bufResp.data.asUInt
  val putBufResp_s3 = RegNext(io.putBufResp) // for Put from A-channel // TODO: half freq
  val putData_s3 = VecInit(putBufResp_s3.map(_.data)).asUInt // only for putFull data
  val putMask_s3 = VecInit(putBufResp_s3.map(_.mask)).asUInt

  def mergePutData(old_data: UInt, new_data: UInt, wmask: UInt): UInt = {
    val full_wmask = FillInterleaved(8, wmask)
    ((~full_wmask & old_data) | (full_wmask & new_data))
  }

  val putOldData_s3 = Mux(gotMSHRBufResp_s3 || io.mshrBufResp_s3.valid, mshrBufData, io.putDataBufResp_s3.bits.data)
  val putPartialData = mergePutData(putOldData_s3, putData_s3, putMask_s3) // TODO: put miss should not use putDataBuf
  val putFullData = putData_s3
  val mshrWrData = ParallelPriorityMux(Seq(
                      mshr_putpartial_s3 -> putPartialData,
                      mshr_putfull_s3 -> putFullData,
                      mshr_releaseack_s3 -> bufResp_s3, // only for NINE
                      (req_s3.useProbeData || !req_s3.useProbeData) -> mshrBufData // TODO:
                    ))
  dontTouch(mshr_putpartial_s3)
  dontTouch(mshr_putfull_s3)

  
  // Free sink c buffer when mshr is not allcated, which means that we will not read this buf anymore.
  io.bufRead.valid := task_s3.valid && ( 
                        sinkC_req_s3 && task_s3.bits.opcode(0) && !need_mshr_s3 || 
                        mshr_releaseack_s3
                      )
  io.bufRead.bits.bufIdx := task_s3.bits.bufIdx
  io.bufRead.bits.bufInvalid := s3_fire
  

  willAccessDS := task_s3.valid && (ren || wen) 
  io.toDS.req_s3.valid := willAccessDS && s3_fire
  io.toDS.req_s3.bits.way := Mux(mshr_req_s3, req_s3.way, dirResult_s3.way)
  io.toDS.req_s3.bits.set := Mux(mshr_req_s3, req_s3.set, dirResult_s3.set)
  io.toDS.req_s3.bits.wen := wen
  //[Alias] TODO: may change this according to four || signals of wen, use ParallelPriorityMux
  io.toDS.wdata_s3.data := Mux(
    !mshr_req_s3,
    Mux(wen_a, putData_s3, bufResp_s3),
    mshrWrData // mshr req
  )

  /* ======== Read DS and store data in Buffer ======== */
  val needWriteMSHRBuf = need_probe_s3_a && req_acquireBlock_s3 && dirResult_s3.hit ||
                         need_data_b && need_mshr_s3_b || // TODO: Not for L3
                         req_acquireBlock_s3 && req_needT_s3 && dirResult_s3.hit && meta_s3.state === BRANCH && !req_put_s3

  val need_write_putDataBuf = sinkA_req_s3 && req_put_partial_s3 && dirResult_s3.hit

  /* ======== Write Directory ======== */
  val metaW_valid_s3_a = sinkA_req_s3 && !need_mshr_s3_a && !req_get_s3 && !req_put_s3 // get & prefetch that hit will not write meta
  val metaW_valid_s3_b = sinkB_req_s3 && !need_mshr_s3_b && dirResult_s3.hit && (meta_s3.state === TIP || meta_s3.state === BRANCH && req_s3.param === toN) && !req_s3.fromProbeHelper
  val metaW_valid_s3_c = sinkC_req_s3 && !need_mshr_s3_c
  val metaW_valid_s3_repl = false.B // !mshr_req_s3 && mainpipe_release
  val metaW_valid_s3_mshr = mshr_req_s3 && req_s3.metaWen
  assert(PopCount(Seq(metaW_valid_s3_a, metaW_valid_s3_b, metaW_valid_s3_c, metaW_valid_s3_repl, metaW_valid_s3_mshr)) <= 1.U, "a:%d b:%d c:%d repl:%d mshr:%d", metaW_valid_s3_a, metaW_valid_s3_b, metaW_valid_s3_c, metaW_valid_s3_repl, metaW_valid_s3_mshr)
  println(s"clientBits: ${clientBits}")


  /* ======== Directory write logic ======== */
  // Get and Prefetch should not change alias bit

  val metaW_s3_a = {
    val selfState = Mux(req_needT_s3 || sink_resp_s3_a_promoteT, TRUNK, meta_s3.state)
    val clientStates = VecInit(meta_s3.clientStates.zip(reqClientOH.asBools).map {
      case (clientState, en) =>
        Mux(en, Mux(req_needT_s3 || sink_resp_s3_a_promoteT, TIP, BRANCH), Mux(dirResult_s3.hit, clientState, INVALID))
    })

    MetaEntry(
      meta_s3.dirty,
      selfState,
      clientStates = clientStates,
    )
  }



  val metaW_s3_b = Mux(req_s3.param === toN, MetaEntry(), MetaEntry(false.B, BRANCH))
   
  val metaW_s3_c = {
    val selfState = MuxLookup(
      req_s3.param,
      meta_s3.state,
      Seq(
        TtoT -> TRUNK,
        TtoB -> TIP,
        TtoN -> TIP,
        BtoN -> Mux(dirResult_s3.hit && meta_s3.state === TIP, TIP, BRANCH)
      )
    )

    val clientStates = VecInit(meta_s3.clientStates.zip(reqClientOH.asBools).zipWithIndex.map {
      case ((clientState, en), client) =>
        Mux(en, Mux(isToN(req_s3.param), INVALID, BRANCH), Mux(dirResult_s3.hit, clientState, clientDirResult_s3.metas(client).state))
    })

    MetaEntry(
      meta_s3.dirty || wen_c,
      selfState,
      clientStates = clientStates,
    )
  }



  val metaW_s3_repl = MetaEntry()
  val metaW_s3_mshr = req_s3.meta



  val clientMetaW_valid_s3_a = sinkA_req_s3 && !need_mshr_s3_a && !req_get_s3 && !req_put_s3 && (hasClientHit || !hasClientHit && !clientDirConflict_s3) // get & prefetch that hit will not write meta
  val clientMetaW_valid_s3_c = sinkC_req_s3 && !need_mshr_s3_c && (hasClientHit || !hasClientHit && !clientDirConflict_s3)
  val clientMetaW_valid_s3_mshr = mshr_req_s3 && req_s3.clientMetaWen

  val clientMetaW_s3_a    = WireInit(VecInit(Seq.fill(clientBits)(0.U.asTypeOf(new noninclusive.ClientMetaEntry))))
  val clientMetaW_s3_c    = WireInit(VecInit(Seq.fill(clientBits)(0.U.asTypeOf(new noninclusive.ClientMetaEntry))))
  val clientMetaW_s3_mshr = WireInit(VecInit(Seq.fill(clientBits)(0.U.asTypeOf(new noninclusive.ClientMetaEntry))))
  assert(PopCount(Seq(clientMetaW_valid_s3_a, clientMetaW_valid_s3_c, clientMetaW_valid_s3_mshr)) <= 1.U, "a:%d c:%d mshr:%d", clientMetaW_valid_s3_a, clientMetaW_valid_s3_c, clientMetaW_valid_s3_mshr)

  clientMetaW_s3_a.zipWithIndex.foreach{
    case(clientMeta, client) =>
      when(reqClient === client.U) {
        clientMeta.state := Mux(sink_resp_s3_a_promoteT || req_s3.param === NtoT || req_s3.param === BtoT, TIP, BRANCH)
      }.otherwise{
        clientMeta.state := Mux(clientDirResult_s3.hits(client), clientMetas_s3(client).state, INVALID)
      }
  }
  clientMetaW_s3_c.zipWithIndex.foreach{
    case(clientMeta, client) =>
      when(reqClient === client.U) {
        clientMeta.state := INVALID
      }.otherwise{
        clientMeta.state := Mux(clientDirResult_s3.hits(client), clientMetas_s3(client).state, INVALID)
      }
  }
  clientMetaW_s3_mshr := req_s3.clientMeta


  // Write self meta & tag
  willAccessDirMeta := task_s3.valid && (metaW_valid_s3_a || metaW_valid_s3_b || metaW_valid_s3_c || metaW_valid_s3_mshr || metaW_valid_s3_repl)
  io.metaWReq.valid      := !resetFinish || willAccessDirMeta && s3_fire
  io.metaWReq.bits.set   := Mux(resetFinish, req_s3.set, resetIdx)
  io.metaWReq.bits.wayOH := Mux(resetFinish, UIntToOH(Mux(mshr_req_s3, req_s3.way, dirResult_s3.way)), Fill(cacheParams.ways, true.B))
  io.metaWReq.bits.wmeta := Mux(
    resetFinish,
    ParallelPriorityMux(
      Seq(metaW_valid_s3_a, metaW_valid_s3_b, metaW_valid_s3_c, metaW_valid_s3_repl, metaW_valid_s3_mshr),
      Seq(metaW_s3_a, metaW_s3_b, metaW_s3_c, metaW_s3_repl, metaW_s3_mshr)
    ),
    MetaEntry()
  )

  val selfIsBRANCH = io.metaWReq.bits.wmeta.state === BRANCH
  val clientsHasTIP = Cat(io.metaWReq.bits.wmeta.clientStates.map( state => state === TIP )).orR
  assert(!(io.metaWReq.valid && selfIsBRANCH && clientsHasTIP && (
            task_s3.bits.mshrTask ||
            !task_s3.bits.mshrTask // && dirResult_s3.hit
          )), 
          "illegal cache states! self is BRANCH and clients has TIP addr:0x%x channel:%d opcode:%d param:%d mshrTask:%d mshrId:%d sourceId:%d" , 
          debug_addr_s3, task_s3.bits.channel, task_s3.bits.opcode, task_s3.bits.param, task_s3.bits.mshrTask, task_s3.bits.mshrId, task_s3.bits.sourceId)

  val metaWrNotMatch = VecInit(io.metaWReq.bits.wmeta.clientStates.zip(io.clientMetaWReq.bits.wmeta).map{
    case(selfMeta, clientMeta) =>
      selfMeta =/= clientMeta.state
  })
  assert(!(io.metaWReq.valid && io.clientMetaWReq.valid && metaWrNotMatch.asUInt.orR), 
        "self client meta not match client meta! addr:0x%x channel:%d opcode:%d param:%d mshrTask:%d mshrId:%d sourceId:%d",
        debug_addr_s3, task_s3.bits.channel, task_s3.bits.opcode, task_s3.bits.param, task_s3.bits.mshrTask, task_s3.bits.mshrId, task_s3.bits.sourceId)

  
  willAccessDirTag := task_s3.valid && (
                            (mshr_grant_s3 || mshr_accessack_s3 || mshr_accessackdata_s3 || mshr_releaseack_s3) && req_s3.tagWen ||
                            metaW_valid_s3_c
                          )
  io.tagWReq.valid     := willAccessDirTag && s3_fire
  io.tagWReq.bits.set  := req_s3.set
  io.tagWReq.bits.way  := Mux(mshr_req_s3, req_s3.way, dirResult_s3.way)
  io.tagWReq.bits.wtag := req_s3.tag


  // Write client meta
  willAccessClientDirMeta := task_s3.valid && (clientMetaW_valid_s3_a || clientMetaW_valid_s3_c || clientMetaW_valid_s3_mshr)
  io.clientMetaWReq.valid := !resetFinishClient || willAccessClientDirMeta && s3_fire
  io.clientMetaWReq.bits.set := Mux(resetFinishClient, Mux(mshr_req_s3, req_s3.clientSet, clientDirResult_s3.set), resetIdxClient)
  io.clientMetaWReq.bits.wayOH := Mux(resetFinishClient, UIntToOH(Mux(mshr_req_s3, req_s3.clientWay, clientDirResult_s3.way)), Fill(clientWays, true.B))
  io.clientMetaWReq.bits.wmeta.zipWithIndex.foreach{
    case (newClientMeta, client) =>
        newClientMeta.state := Mux(
          resetFinishClient,
          ParallelPriorityMux(
            Seq(clientMetaW_valid_s3_a, clientMetaW_valid_s3_c, clientMetaW_valid_s3_mshr),
            Seq(clientMetaW_s3_a(client).state, clientMetaW_s3_c(client).state, clientMetaW_s3_mshr(client).state)
          ),
          INVALID
        )
  }
  
  // Write client tag
  val clientTagW_valid_s3_a = clientMetaW_valid_s3_a && !clientDirResult_s3.tagMatch
  val clientTagW_valid_s3_mshr = (mshr_grant_s3 || mshr_accessack_s3 || mshr_accessackdata_s3) && req_s3.clientTagWen
  willAccessClientDirTag := task_s3.valid && (clientTagW_valid_s3_mshr || clientTagW_valid_s3_a)
  // io.clientTagWReq.valid := willAccessClientDirTag && s3_fire
  // io.clientTagWReq.bits.apply(
  //   Cat(req_s3.tag, req_s3.set),
  //   Mux(clientTagW_valid_s3_mshr, req_s3.clientWay, clientDirResult_s3.way)
  // )

  io.clientTagWReq.valid := willAccessClientDirTag && s3_fire || !resetFinishClient
  when(resetFinishClient) {
    io.clientTagWReq.bits.apply(
      Cat(req_s3.tag, req_s3.set),
      Mux(clientTagW_valid_s3_mshr, req_s3.clientWay, clientDirResult_s3.way)
    )
  }.otherwise{
    io.clientTagWReq.bits.set := resetIdxClient
    io.clientTagWReq.bits.tag := 0.U
    io.clientTagWReq.bits.way := Fill(clientWays, true.B)
  }


  io.clientBusyWakeup := DontCare
  val sinkReqWakeUp = !need_mshr_s3 && sink_req_s3 && s3_fire
  val mshrReqWakeUp = mshr_req_s3 && s3_fire && !(mshr_release_s3 && (!req_s3.fromC && !req_s3.fromProbeHelper))
  io.clientBusyWakeup.valid := sinkReqWakeUp || mshrReqWakeUp
  io.clientBusyWakeup.bits.set := Mux(sinkReqWakeUp, clientDirResult_s3.set, task_s3.bits.clientSet)
  io.clientBusyWakeup.bits.way := Mux(sinkReqWakeUp, clientDirResult_s3.way, task_s3.bits.clientWay)

  // --------------------------------------------------------------------------
  //  Interact with Channels (C & D)
  // --------------------------------------------------------------------------
  val task_ready_s3 = !hasData_s3 || req_s3.fromC || (need_mshr_s3 && !a_need_replacement) || mshr_req_s3 || req_put_s3
  // do not need s4 & s5
  req_drop_s3 := (!mshr_req_s3 && need_mshr_s3 && !needWriteMSHRBuf && !need_write_putDataBuf && !mainpipe_release) ||
                    (task_ready_s3 && (c_s3.fire || d_s3.fire || sendSourceC || sendSourceD)) ||
                    (mshr_req_s3 && req_s3.fromProbeHelper || !mshr_req_s3 && req_s3.fromProbeHelper)  // We won't send resp for the ProbeHepler request, since it is an inner request not an outer request.

  
  if(cacheParams.inclusionPolicy == "NINE") 
    assert(!(mainpipe_release && req_drop_s3 && !mshr_req_s3))
  
  //[Alias] TODO: may change this to ren?
  val data_unready_s3 = hasData_s3 && !mshr_req_s3 || task_s3.bits.selfHasData && mshr_req_s3
  
  when(s3_fire) {
    sendSourceC := false.B
  }.elsewhen(c_s3.fire) {
    sendSourceC := true.B
  }
  when(s3_fire) {
    sendSourceD := false.B
  }.elsewhen(d_s3.fire) {
    sendSourceD := true.B
  }

  willSendSourceC := task_s3.valid && Mux(
    mshr_req_s3,
    mshr_release_s3 && !req_s3.fromC && !data_unready_s3 || mshr_probeack_s3 && !req_s3.fromProbeHelper, // We won't send resp for the ProbeHepler request, since it is an inner request not an outer request.
    req_s3.fromB && !need_mshr_s3 && !data_unready_s3 && !req_s3.fromProbeHelper
  )
  c_s3.valid := willSendSourceC && !sendSourceC
  
  willSendSourceD := task_s3.valid && Mux(
    mshr_req_s3,
    mshr_grant_s3 & !task_s3.bits.selfHasData || mshr_accessackdata_s3 || mshr_accessack_s3 || mshr_putpartial_s3 || mshr_releaseack_s3,
    req_s3.fromC && !need_mshr_s3 || req_s3.fromA && !need_mshr_s3 && !mainpipe_release &&(!data_unready_s3 || req_put_full_s3)
  )
  d_s3.valid := willSendSourceD && !sendSourceD

  assert(!((d_s3.valid || c_s3.valid) && !sink_resp_s3.valid && !req_s3.mshrTask), "d_s3.valid:%d  c_s3.valid:%d", d_s3.valid, c_s3.valid)

  c_s3.bits.task      := source_req_s3
  c_s3.bits.data.data := data_s3
  d_s3.bits.task      := source_req_s3
  when(mshr_put_s3) {
    d_s3.bits.task.opcode := AccessAck
  }
  d_s3.bits.data.data := data_s3

  /* ======== nested & prefetch ======== */
  io.nestedwb.valid := sink_req_s3 && task_s3.valid && s3_fire
  io.nestedwb.channel := req_s3.channel
  io.nestedwb.set := req_s3.set
  io.nestedwb.tag := req_s3.tag
  io.nestedwb.sourceId := Mux(req_s3.fromProbeHelper, io.fromMSHRCtl.mshr_alloc_ptr, req_s3.sourceId)
  io.nestedwb.needMSHR := need_mshr_s3
  io.nestedwb.way := dirResult_s3.way

  io.nestedwb.b_toN := req_s3.param === toN
  io.nestedwb.b_toB := req_s3.param === toB
  io.nestedwb.b_clr_dirty := meta_s3.dirty

  // c_set_dirty is true iff Release has Data
  io.nestedwb.c_set_dirty := task_s3.bits.opcode === ReleaseData
  io.nestedwb.c_toN := isToN(task_s3.bits.param)
  io.nestedwb.c_toB := isToB(task_s3.bits.param)
  io.nestedwb.c_client := reqClientOH

  io.nestedwb.wakeupValid := req_s3.mshrTask && task_s3.valid && (req_s3.fromC || req_s3.fromB) && s3_fire
  io.nestedwb.wakeupSourceId := Mux(req_s3.fromProbeHelper, req_s3.mshrId, req_s3.sourceId)
  io.nestedwb.fromProbeHelper := req_s3.fromProbeHelper

  io.nestedwbData := bufResp_s3.asTypeOf(new DSBlock)


  // Wake up MSHR that waitting for the ProbeHelper task. (Only for NINE)
  val probeHelperWakeupFromMSHR = mshr_req_s3 && req_s3.fromProbeHelper
  val probeHelperWakeupFromSink = !mshr_req_s3 && req_s3.fromProbeHelper && !need_mshr_s3
  io.probeHelperWakeup.valid := (probeHelperWakeupFromMSHR || probeHelperWakeupFromSink) && s3_fire
  io.probeHelperWakeup.set := req_s3.set
  io.probeHelperWakeup.tag := req_s3.tag
  


  // --------------------------------------------------------------------------
  //  Stage4: 
  // --------------------------------------------------------------------------
  val task_s4 = RegInit(0.U.asTypeOf(Valid(new TaskBundle())))
  val ren_s4 = RegInit(false.B)
  val needWriteMSHRBuf_s4 = RegInit(false.B)
  val need_write_putDataBuf_s4 = RegInit(false.B)
  val s4_latch = s3_fire && !req_drop_s3
  s4_valid := s4_full
  s4_ready := !s4_full || s4_fire
  s4_fire := s4_valid && s5_ready
  when(s4_latch) {
    s4_full := true.B
    task_s4.valid := true.B
  }.elsewhen(s4_fire) {
    s4_full := false.B
    task_s4.valid := false.B
  }
  // task_s4.valid := task_s3.valid && !req_drop_s3 && s3_fire
  // when (task_s3.valid && !req_drop_s3 && s3_fire) {
  when (s4_latch) {
    task_s4.bits := source_req_s3
    task_s4.bits.mshrId := Mux(!task_s3.bits.mshrTask && need_mshr_s3, io.fromMSHRCtl.mshr_alloc_ptr, source_req_s3.mshrId)
    ren_s4 := ren
    needWriteMSHRBuf_s4 := needWriteMSHRBuf
    need_write_putDataBuf_s4 := need_write_putDataBuf
  }
  val isC_s4 = task_s4.bits.opcode(2, 1) === Release(2, 1) && task_s4.bits.fromA ||
                task_s4.bits.opcode(2, 1) === ProbeAck(2, 1) && task_s4.bits.fromB || 
                task_s4.bits.opcode(2, 1) === Release(2, 1) && task_s4.bits.fromC // for C and c_need_replacement
                
  val isD_s4 =  task_s4.bits.opcode(2, 1) =/= Release(2, 1) && task_s4.bits.fromC || 
                  task_s4.bits.fromA && (
                    task_s4.bits.opcode(2, 1) === Grant(2, 1) ||
                    task_s4.bits.opcode(2, 1) === AccessAck(2, 1)
                  )


  
  // --------------------------------------------------------------------------
  //  Stage5: 
  // --------------------------------------------------------------------------
  val task_s5 = RegInit(0.U.asTypeOf(Valid(new TaskBundle())))
  val ren_s5 = RegInit(false.B)
  val gotData_s5 = RegInit(false.B)
  val dataReg_s5 = RegInit(0.U.asTypeOf(new DSBlock()))
  val needWriteMSHRBuf_s5 = RegInit(false.B)
  val need_write_putDataBuf_s5 = RegInit(false.B)
  val isC_s5, isD_s5 = RegInit(false.B)
  val willWriteMSHRBuf = WireInit(false.B)
  val willWritePutDataBuf = WireInit(false.B)
  val willSendSourceC_s5 = WireInit(false.B)
  val willSendSourceD_s5 = WireInit(false.B)
  val sendSourceC_s5 = RegInit(false.B)
  val sendSourceD_s5 = RegInit(false.B)
  when(s5_fire) {
    sendSourceC_s5 := false.B
  }.elsewhen(c_s5.fire) {
    sendSourceC_s5 := true.B
  }
  when(s5_fire) {
    sendSourceD_s5 := false.B
  }.elsewhen(d_s5.fire) {
    sendSourceD_s5 := true.B
  }
  
  when(s5_fire) { 
    gotData_s5 := false.B
  }.elsewhen(RegNext(s4_fire)) {
    dataReg_s5 := io.toDS.rdata_s5
    gotData_s5 := true.B
  }

  s5_ready := !s5_full || s5_fire
  s5_valid := s5_full && (
    !(willWriteMSHRBuf && !io.mshrBufWrite.ready ) && 
    // !(willWritePutDataBuf && !io.putDataBufWrite.ready ) &&
    !(willSendSourceC_s5 && !c_s5.ready && !sendSourceC_s5   ) &&
    !(willSendSourceD_s5 && !d_s5.ready && !sendSourceD_s5   )
  )
   
  s5_fire := s5_valid
  when(s4_fire) {
    s5_full := true.B
    task_s5.valid := true.B
  }.elsewhen(s5_fire) {
    s5_full := false.B
    task_s5.valid := false.B
  }

  when (s4_fire) {
    task_s5.bits := task_s4.bits
    ren_s5 := ren_s4
    needWriteMSHRBuf_s5 := needWriteMSHRBuf_s4
    // need_write_releaseBuf_s5 := need_write_releaseBuf_s4
    // need_write_refillBuf_s5 := need_write_refillBuf_s4
    need_write_putDataBuf_s5 := need_write_putDataBuf_s4
    isC_s5 := isC_s4
    isD_s5 := isD_s4
  }
  assert(!RegNext(!ren_s5 && task_s5.valid), "ren_s5:%d task_s5_valid:%d isC_s5:%d isD_s5:%d channel:%d opcode:%d mshrTask:%d", RegNext(ren_s5), RegNext(task_s5.valid), RegNext(isC_s5), RegNext(isD_s5), RegNext(task_s5.bits.channel), RegNext(task_s5.bits.opcode), RegNext(task_s5.bits.mshrTask))
  val rdata_s5 = Mux(gotData_s5, dataReg_s5.data, io.toDS.rdata_s5.data)
  task_s5.bits.corrupt := Mux(ren_s5, io.toDS.error_s5, false.B)
  val chnl_fire_s5 = c_s5.fire() || d_s5.fire()

  willWriteMSHRBuf := s5_full && needWriteMSHRBuf_s5
  io.mshrBufWrite.valid           := willWriteMSHRBuf
  io.mshrBufWrite.bits.beat_sel   := Fill(beatSize, 1.U(1.W))
  io.mshrBufWrite.bits.data.data  := rdata_s5
  io.mshrBufWrite.bits.id         := task_s5.bits.mshrId
  io.mshrBufWrite.bits.corrupt    := task_s5.bits.corrupt // TODO: Ecc


  willWritePutDataBuf := s5_full && need_write_putDataBuf_s5
  io.putDataBufWrite.valid        := willWritePutDataBuf
  io.putDataBufWrite.beat_sel     := Fill(beatSize, 1.U(1.W))
  io.putDataBufWrite.data.data    := rdata_s5
  io.putDataBufWrite.id           := task_s5.bits.sourceId // TODO:
  io.putDataBufWrite.corrupt      := task_s5.bits.corrupt || io.toDS.error_s5

  willSendSourceC_s5 := s5_full && isC_s5 && !needWriteMSHRBuf_s5 && !need_write_putDataBuf_s5
  willSendSourceD_s5 := s5_full && isD_s5 && !needWriteMSHRBuf_s5 && !need_write_putDataBuf_s5
  c_s5.valid := willSendSourceC_s5 && !sendSourceC_s5
  d_s5.valid := willSendSourceD_s5 && !sendSourceD_s5
  c_s5.bits.task := task_s5.bits
  c_s5.bits.data.data := rdata_s5
  d_s5.bits.task := task_s5.bits
  d_s5.bits.data.data := rdata_s5

  // assert(!(d_s5.valid && !d_s5.ready), "d_s5 should be ready when given valid")


  // --------------------------------------------------------------------------
  //  BlockInfo
  // --------------------------------------------------------------------------
  def pipelineBlock(chn: Char, s: TaskBundle, allTask: Boolean = false, tag: Boolean = false): Bool = {
    val s1 = io.fromReqArb.status_s1
    val s1_tag = if(chn == 'a') s1.a_tag else s1.b_tag
    val s1_set = if(chn == 'a') s1.a_set else s1.b_set

    // allTask false: only !mshrTask (SinkReq) blocks Entrance
    // allTask true : all tasks with the same set at s2 block Entrance
    // tag true : compare tag+set
    // tag false: compare set alone
    s.set === s1_set && (if(allTask) true.B else !s.mshrTask) && (if(tag) s.tag === s1_tag else true.B)
  }

  io.toReqBuf(0) := task_s2.valid && pipelineBlock('a', task_s2.bits, allTask = true)
  io.toReqBuf(1) := task_s3.valid && pipelineBlock('a', task_s3.bits)

  val stage3IsBlocked = s3_full && !s3_fire
  val fromReqBufSinkA_valid = WireInit(false.B)
  val fromReqBufSinkA_set = WireInit(0.U.asTypeOf(task_s2.bits.set))
  val fromReqBufSinkA_blockFromS2 = fromReqBufSinkA_valid && task_s2.valid && (
      fromReqBufSinkA_set === task_s2.bits.set || 
      fromReqBufSinkA_set(clientSetBits-1, 0) === task_s2.bits.set(clientSetBits-1, 0) && task_s2.bits.fromC
  )
  val fromReqBufSinkA_blockFromS3 = fromReqBufSinkA_valid && task_s3.valid && (
      fromReqBufSinkA_set === task_s3.bits.set || 
      fromReqBufSinkA_set(clientSetBits-1, 0) === task_s3.bits.set(clientSetBits-1, 0) && task_s3.bits.fromC
  )
  fromReqBufSinkA_valid := io.fromReqBufSinkA.valid
  fromReqBufSinkA_set := io.fromReqBufSinkA.set

  io.toReqArb.blockC_s1 :=
    task_s2.valid && task_s2.bits.set === io.fromReqArb.status_s1.c_set ||
    (stage3IsBlocked || willAllocMSHR) && task_s3.bits.set === io.fromReqArb.status_s1.c_set
  io.toReqArb.blockB_s1 :=
    task_s2.valid && pipelineBlock('b', task_s2.bits, allTask = true) ||
    task_s3.valid && pipelineBlock('b', task_s3.bits, allTask = true) || // TODO: tag match ?
    // task_s3.valid && pipelineBlock('b', task_s3.bits)                 ||
    task_s4.valid && pipelineBlock('b', task_s4.bits, tag = true)     ||
    task_s5.valid && pipelineBlock('b', task_s5.bits, tag = true)
  io.toReqArb.blockA_s1 := io.toReqBuf(0) || io.toReqBuf(1) || fromReqBufSinkA_blockFromS2 || fromReqBufSinkA_blockFromS3



  // --------------------------------------------------------------------------
  //  Pipeline Status
  // --------------------------------------------------------------------------
  require(io.status_vec.size == 3)
  io.status_vec(0).valid := task_s3.valid && Mux(
    mshr_req_s3,
    mshr_grant_s3 || mshr_accessackdata_s3 || mshr_accessack_s3,
    true.B
    // TODO: To consider grantBuffer capacity conflict,
    // only " req_s3.fromC || req_s3.fromA && !need_mshr_s3 " is needed
    // But to consider mshrFull, all channel_reqs are needed
  )
  io.status_vec(0).bits.channel := task_s3.bits.channel
  io.status_vec(0).bits.set     := task_s3.bits.set
  io.status_vec(0).bits.mshrTask := task_s3.bits.mshrTask
  io.status_vec(1).valid        := task_s4.valid && isD_s4 && !needWriteMSHRBuf_s4
  io.status_vec(1).bits.channel := task_s4.bits.channel
  io.status_vec(1).bits.set     := task_s4.bits.set
  io.status_vec(1).bits.mshrTask := task_s4.bits.mshrTask
  io.status_vec(2).valid        := d_s5.valid
  io.status_vec(2).bits.channel := task_s5.bits.channel
  io.status_vec(2).bits.set     := task_s5.bits.set
  io.status_vec(2).bits.mshrTask := task_s5.bits.mshrTask

  // make sure we don't send two reqs continuously with the same set
  assert(!(task_s2.bits.set === task_s3.bits.set &&
    task_s2.valid && !task_s2.bits.mshrTask && task_s2.bits.fromA &&
    task_s3.valid && !task_s3.bits.mshrTask && task_s3.bits.fromA),
    "s2 and s3 task same set, failed in blocking")



  // --------------------------------------------------------------------------
  //  Other Signals Assignment
  // --------------------------------------------------------------------------
  c_s4.ready := false.B
  d_s4.ready := false.B
  val c = Seq(c_s5, 0.U.asTypeOf(c_s4), c_s3)
  val d = Seq(d_s5, 0.U.asTypeOf(d_s4), d_s3)
  // DO NOT use TLArbiter because TLArbiter will send continuous beats for the same source
  val fifoArbEntries =  5
  // val c_arb = Module(new FIFOArbiter(io.toSourceC.bits.cloneType, c.size, fifoArbEntries)) // TODO: optimize
  // val d_arb = Module(new FIFOArbiter(io.toSourceD.bits.cloneType, d.size, fifoArbEntries))
  val c_arb = Module(new Arbiter(io.toSourceC.bits.cloneType, c.size))
  val d_arb = Module(new Arbiter(io.toSourceD.bits.cloneType, d.size))
  c_arb.io.in <> c
  d_arb.io.in <> d

  io.toSourceC <> c_arb.io.out
  io.toSourceD <> d_arb.io.out

  assert(!(d_s3.valid && d_s3.bits.task.opcode === 7.U), "d_s3 invalid opcode: 7  mshrTask:%d mshrId:%d Tag:0x%x Set:0x%x", req_s3.mshrTask, req_s3.mshrId, req_s3.tag, req_s3.set)
  assert(!(d_s4.valid && d_s4.bits.task.opcode === 7.U), "d_s4 invalid opcode: 7  mshrTask:%d mshrId:%d Tag:0x%x Set:0x%x", task_s4.bits.mshrTask, task_s4.bits.mshrId, task_s4.bits.tag, task_s4.bits.set)
  assert(!(d_s5.valid && d_s5.bits.task.opcode === 7.U), "d_s5 invalid opcode: 7  mshrTask:%d mshrId:%d Tag:0x%x Set:0x%x", task_s5.bits.mshrTask, task_s5.bits.mshrId, task_s5.bits.tag, task_s5.bits.set)

  val s2HasGrant = task_s2.valid && task_s2.bits.mshrTask && task_s2.bits.fromA && (task_s2.bits.opcode === GrantData || task_s2.bits.opcode === Grant)
  val s3HasRelease = task_s3.valid && !task_s3.bits.mshrTask && task_s3.bits.fromC && (task_s3.bits.opcode === ReleaseData || task_s3.bits.opcode === Release)
  val s2s3SameSet = task_s2.valid && task_s3.valid && task_s2.bits.set === task_s3.bits.set
  val s2s3SameTag = task_s2.valid && task_s3.valid && task_s2.bits.tag === task_s3.bits.tag
  assert(!(s2HasGrant && s3HasRelease && s2s3SameSet && s2s3SameTag), "Release may not be able to nest Acquire")

  // --------------------------------------------------------------------------
  //  Performance counters
  // --------------------------------------------------------------------------
  // num of mshr req
  XSPerfAccumulate(cacheParams, "mshr_grant_req", task_s3.valid && mshr_grant_s3)
  XSPerfAccumulate(cacheParams, "mshr_grantdata_req", task_s3.valid && mshr_grantdata_s3)
  XSPerfAccumulate(cacheParams, "mshr_accessackdata_req", task_s3.valid && mshr_accessackdata_s3)
  XSPerfAccumulate(cacheParams, "mshr_accessack_req", task_s3.valid && mshr_accessack_s3)
  XSPerfAccumulate(cacheParams, "mshr_probeack_req", task_s3.valid && mshr_probeack_s3)
  XSPerfAccumulate(cacheParams, "mshr_probeackdata_req", task_s3.valid && mshr_probeackdata_s3)
  XSPerfAccumulate(cacheParams, "mshr_release_req", task_s3.valid && mshr_release_s3)

  // directory access result
  val hit_s3 = task_s3.valid && !mshr_req_s3 && dirResult_s3.hit && s3_fire
  val miss_s3 = task_s3.valid && !mshr_req_s3 && !dirResult_s3.hit && s3_fire
  XSPerfAccumulate(cacheParams, "a_req_hit", hit_s3 && req_s3.fromA)
  XSPerfAccumulate(cacheParams, "acquire_hit", hit_s3 && req_s3.fromA &&
    (req_s3.opcode === AcquireBlock || req_s3.opcode === AcquirePerm))
  XSPerfAccumulate(cacheParams, "get_hit", hit_s3 && req_s3.fromA && req_s3.opcode === Get)

  XSPerfAccumulate(cacheParams, "a_req_miss", miss_s3 && req_s3.fromA)
  XSPerfAccumulate(cacheParams, "acquire_miss", miss_s3 && req_s3.fromA &&
    (req_s3.opcode === AcquireBlock || req_s3.opcode === AcquirePerm))
  XSPerfAccumulate(cacheParams, "get_miss", miss_s3 && req_s3.fromA && req_s3.opcode === Get)

  XSPerfAccumulate(cacheParams, "c_req_miss", miss_s3 && req_s3.fromC)
  XSPerfAccumulate(cacheParams, "c_req_hit", hit_s3 && req_s3.fromC)

  XSPerfAccumulate(cacheParams, "a_req_need_replacement",
    io.toMSHRCtl.mshr_alloc_s3.valid && a_need_replacement && req_s3.fromA)
  XSPerfAccumulate(cacheParams, "c_req_need_replacement",
    io.toMSHRCtl.mshr_alloc_s3.valid && c_need_replacement && req_s3.fromC)

  XSPerfAccumulate(cacheParams, "b_req_hit", hit_s3 && req_s3.fromB)
  XSPerfAccumulate(cacheParams, "b_req_miss", miss_s3 && req_s3.fromB)

  XSPerfHistogram(cacheParams, "a_req_access_way", perfCnt = dirResult_s3.way,
    enable = task_s3.valid && !mshr_req_s3 && req_s3.fromA && !req_put_s3, start = 0, stop = cacheParams.ways, step = 1)
  XSPerfHistogram(cacheParams, "a_req_hit_way", perfCnt = dirResult_s3.way,
    enable = hit_s3 && req_s3.fromA && !req_put_s3, start = 0, stop = cacheParams.ways, step = 1)
  XSPerfHistogram(cacheParams, "a_req_miss_way_choice", perfCnt = dirResult_s3.way,
    enable = miss_s3 && req_s3.fromA && !req_put_s3, start = 0, stop = cacheParams.ways, step = 1)

  // pipeline stages for sourceC and sourceD reqs
  val sourceC_pipe_len = ParallelMux(Seq(
    c_s5.fire() -> 5.U,
    c_s4.fire() -> 4.U,
    c_s3.fire() -> 3.U
  ))
  val sourceD_pipe_len = ParallelMux(Seq(
    d_s5.fire() -> 5.U,
    d_s4.fire() -> 4.U,
    d_s3.fire() -> 3.U
  ))
  XSPerfHistogram(cacheParams, "sourceC_pipeline_stages", sourceC_pipe_len,
    enable = io.toSourceC.fire(), start = 3, stop = 5+1, step = 1)
  XSPerfHistogram(cacheParams, "sourceD_pipeline_stages", sourceD_pipe_len,
    enable = io.toSourceD.fire(), start = 3, stop = 5+1, step = 1)
}
