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
import utility._
import utility.ParallelMax
import coupledL2.MetaData._
import chipsalliance.rocketchip.config.Parameters
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tilelink.TLMessages._
import freechips.rocketchip.tilelink.TLPermissions._
import coupledL2.utils._
import coupledL2.debug._
import coupledL2.prefetch.PrefetchTrain

class MainPipe(implicit p: Parameters) extends L2Module with noninclusive.HasClientInfo {
  val io = IO(new Bundle() {
    /* receive task from arbiter at stage 2 */
    val taskFromArb_s2 = Flipped(ValidIO(new TaskBundle()))
    /* status from arbiter at stage1  */
    val taskInfo_s1 = Flipped(ValidIO(new TaskBundle()))

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
    val clientDirResult_s3 = if(cacheParams.inclusionPolicy == "NINE") Some(Input(new noninclusive.ClientDirResult)) else None

    /* get ProbeHelper info */
    val clientDirConflict = if(cacheParams.inclusionPolicy == "NINE") Some(Input(Bool())) else None

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

    /* get ReleaseBuffer and RefillBuffer read result */
    val refillBufResp_s3 = Flipped(ValidIO(new DSBlock))
    val releaseBufResp_s3 = Flipped(ValidIO(new DSBlock))

    /* get PutDataBuffer read result */
    val putDataBufResp_s3 = Flipped(ValidIO(new DSBlock))

    /* read or write data storage */
    val toDS = new Bundle() {
      val req_s3 = ValidIO(new DSRequest)
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
    val metaWReq = ValidIO(new MetaWrite)
    val tagWReq = ValidIO(new TagWrite)

    /* write client dir */
    val clientMetaWReq = if(cacheParams.inclusionPolicy == "NINE") Some(Valid(new noninclusive.ClientMetaWrite)) else None
    val clientTagWReq = if(cacheParams.inclusionPolicy == "NINE") Some(Valid(new noninclusive.ClientTagWrite)) else None

    /* read DS and write data into ReleaseBuf when the task needs to replace */
    val releaseBufWrite = Flipped(new MSHRBufWrite()) // s5 & s6

    /* read DS and write data into RefillBuf when Acquire toT hits on B */
    val refillBufWrite = Flipped(new MSHRBufWrite())

    /* read DS and write data into PutDataBuf when req is Put and need to alloc MSHR */
    val putDataBufWrite = Flipped(new LookupBufWrite())

    val nestedwb = Output(new NestedWriteback)
    val nestedwbData = Output(new DSBlock)

    val probeHelperWakeup = Output(new ProbeHelperWakeupInfo) // Only for NINE

    val l1Hint = ValidIO(new L2ToL1Hint())
    val grantBufferHint = Flipped(ValidIO(new L2ToL1Hint()))
    val globalCounter = Input(UInt(log2Ceil(mshrsAll).W))
    /* send prefetchTrain to Prefetch to trigger a prefetch req */
    val prefetchTrain = prefetchOpt.map(_ => DecoupledIO(new PrefetchTrain))

    val toMonitor = Output(new MainpipeMoni())
  })

  val resetFinish = RegInit(false.B)
  val resetIdx = RegInit((cacheParams.sets - 1).U)
  val resetFinishClient = RegInit(false.B)
  val resetIdxClient = RegInit((clientWays - 1).U)
  /* block reqs when reset */
  when(!resetFinish) {
    resetIdx := resetIdx - 1.U
  }
  when(resetIdx === 0.U) {
    resetFinish := true.B
  }

  when(!resetFinishClient) {
    resetIdxClient := resetIdxClient - 1.U
  }
  when(resetIdxClient === 0.U) {
    resetFinishClient := true.B
  } 

  val c_s3, c_s4, c_s5 = Wire(io.toSourceC.cloneType)
  val d_s3, d_s4, d_s5 = Wire(io.toSourceD.cloneType)

  require(cacheParams.inclusionPolicy == "NINE", "For this repo, L3 only support NINE")
  
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

  

  // --------------------------------------------------------------------------
  //  Stage3: 
  // --------------------------------------------------------------------------
  val task_s3 = RegInit(0.U.asTypeOf(Valid(new TaskBundle())))
  task_s3.valid := task_s2.valid
  when(task_s2.valid) {
    task_s3.bits := task_s2.bits
  }

  //  TODO: debug address consider multi-bank
  def restoreAddr(set: UInt, tag: UInt) = {
    (set << offsetBits).asUInt + (tag << (setBits + offsetBits)).asUInt
  }
  val debug_addr_s3 = restoreAddr(task_s3.bits.set, task_s3.bits.tag) // (task_s3.bits.set << offsetBits).asUInt + (task_s3.bits.tag << (setBits + offsetBits)).asUInt
  dontTouch(debug_addr_s3)


  /* ======== Enchantment ======== */
  // self dir result
  val dirResult_s3 = io.dirResp_s3
  val meta_s3 = dirResult_s3.meta
  val meta_error_s3 = dirResult_s3.error

  // client dir result (Only for NINE)
  val clientDirResult_s3 = io.clientDirResult_s3.getOrElse(0.U.asTypeOf(new noninclusive.ClientDirResult))
  val clientMetas_s3 = clientDirResult_s3.metas
  val hasClientHit = clientDirResult_s3.hits.asUInt.orR
  dontTouch(clientDirResult_s3) // TODO: NINE

  val req_s3 = task_s3.bits
  val mshr_req_s3 = req_s3.mshrTask
  val sink_req_s3 = !mshr_req_s3
  val sinkA_req_s3 = !mshr_req_s3 && req_s3.fromA
  val sinkB_req_s3 = !mshr_req_s3 && req_s3.fromB
  val sinkC_req_s3 = !mshr_req_s3 && req_s3.fromC

  val req_needT_s3 = needT(req_s3.opcode, req_s3.param) // require T status to handle req
  val req_acquire_s3 = sinkA_req_s3 && (req_s3.opcode === AcquireBlock || req_s3.opcode === AcquirePerm)
  val req_acquireBlock_s3 = sinkA_req_s3 && req_s3.opcode === AcquireBlock
  val req_prefetch_s3 = sinkA_req_s3 && req_s3.opcode === Hint
  val req_get_s3 = sinkA_req_s3 && req_s3.opcode === Get
  val req_put_full_s3 = sinkA_req_s3 && req_s3.opcode === PutFullData
  val req_put_partial_s3 = sinkA_req_s3 && req_s3.opcode === PutPartialData
  val req_put_s3 = req_put_full_s3 || req_put_partial_s3

  val mshr_grant_s3 = mshr_req_s3 && req_s3.fromA && req_s3.opcode(2, 1) === Grant(2, 1) // Grant or GrantData from mshr
  val mshr_grantdata_s3 = mshr_req_s3 && req_s3.fromA && req_s3.opcode === GrantData
  val mshr_accessackdata_s3 = mshr_req_s3 && req_s3.fromA && req_s3.opcode === AccessAckData
  val mshr_accessack_s3 = mshr_req_s3 && req_s3.fromA && req_s3.opcode === AccessAck
  val mshr_hintack_s3 = mshr_req_s3 && req_s3.fromA && req_s3.opcode === HintAck
  val mshr_probeack_s3 = mshr_req_s3 && req_s3.fromB && req_s3.opcode(2, 1) === ProbeAck(2, 1) // ProbeAck or ProbeAckData from mshr
  val mshr_probeackdata_s3 = mshr_req_s3 && req_s3.fromB && req_s3.opcode === ProbeAckData
  val mshr_release_s3 = mshr_req_s3 && req_s3.opcode(2, 1) === Release(2, 1) // voluntary Release or ReleaseData from mshr
  val mshr_releaseack_s3 = mshr_req_s3 && req_s3.fromC && req_s3.opcode === ReleaseAck // only for NINE
  val mshr_putpartial_s3 = mshr_req_s3 && req_s3.fromA && req_s3.opcode === PutPartialData && req_s3.opcodeIsReq
  val mshr_putfull_s3 = mshr_req_s3 && req_s3.fromA && req_s3.opcode === PutFullData && req_s3.opcodeIsReq
  val mshr_put_s3 = mshr_putpartial_s3 || mshr_putfull_s3

  
  // Clients releted signal
  val reqClient   = Reg(UInt((log2Up(clientBits) + 1).W)) // Which client does this req come from?
  // val reqClientOH = getClientBitOH(task_s3.bits.sourceId) // ! This is only for channel task
  val reqClientOH = Reg(UInt(clientBits.W)) // getClientBitOH(task_s3.bits.sourceId) // ! This is only for channel task
  when(task_s2.valid) {
    val reqClientOHWire = getClientBitOH(task_s2.bits.sourceId)
    reqClientOH := reqClientOHWire
    reqClient := Mux(reqClientOHWire === 0.U, Cat(1.U(1.W), 0.U(log2Up(clientBits).W)), OHToUInt(reqClientOHWire)) // The highest bit of reqClient indicates that req comes from TL-UL node
  }

  // Deal with coherence
  val cohChecker         = Module(new CohChecker())
  val cache_alias        = cohChecker.io.out.flags.cacheAlias
  val need_mshr_s3       = cohChecker.io.out.flags.needMSHR
  val a_need_replacement = cohChecker.io.out.flags.aNeedReplacement
  val c_need_replacement = cohChecker.io.out.flags.cNeedReplacement
  val need_probe_s3_a    = cohChecker.io.out.flags.aNeedProbe
  val need_mshr_s3_a     = cohChecker.io.out.flags.aNeedMSHR
  val need_mshr_s3_b     = cohChecker.io.out.flags.bNeedMSHR
  val need_mshr_s3_c     = cohChecker.io.out.flags.cNeedMSHR
  cohChecker.io.in <> DontCare
  cohChecker.io.in.task <> task_s3
  cohChecker.io.in.dirResult := dirResult_s3
  cohChecker.io.in.clientDirResult.foreach( _ := clientDirResult_s3)
  cohChecker.io.in.clientDirConflict := io.clientDirConflict.getOrElse(false.B)
  io.toMSHRCtl.mshr_alloc_s3 <> cohChecker.io.out.mshrAlloc
  

  /* ======== Resps to SinkA/B/C Reqs ======== */
  val sink_resp_s3 = WireInit(0.U.asTypeOf(Valid(new TaskBundle))) // resp for sinkA/B/C request that does not need to alloc mshr
  val mainpipe_release = a_need_replacement || c_need_replacement
                            
  val sink_resp_s3_a_promoteT = dirResult_s3.hit && isT(meta_s3.state)

  sink_resp_s3.valid := task_s3.valid && !mshr_req_s3 && (!need_mshr_s3 || mainpipe_release)
  sink_resp_s3.bits := task_s3.bits
  sink_resp_s3.bits.mshrId := Mux(
                                  mainpipe_release, 
                                  io.fromMSHRCtl.mshr_alloc_ptr, // for NINE, mainpipe release will alloc a MSHR
                                  (1 << (mshrBits - 1)).U + sink_resp_s3.bits.sourceId // extra id for reqs that do not enter mshr
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
      if(cacheParams.inclusionPolicy == "NINE") {
        when(sinkC_req_s3 && !need_mshr_s3_c) {
          sink_resp_s3.bits.opcode := {
            cacheParams.releaseData match {
              case 0 => Mux(meta_s3.dirty, ReleaseData, Release)
//              case 1 => Mux(meta_s3.dirty && meta_s3.accessed, ReleaseData, Release)
              case 2 => ReleaseData
              case 3 => ReleaseData
            }
          }
          sink_resp_s3.bits.param := Mux(isT(meta_s3.state), TtoN, BtoN)
          // sink_resp_s3.bits.mshrId is changed to mshr_alloc_ptr at stage 4
          // so source of C-Release is correct
          sink_resp_s3.bits.tag := dirResult_s3.tag
          sink_resp_s3.bits.dirty := meta_s3.dirty // TODO:
        }
      }
      
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
  val data_s3 = Mux(io.refillBufResp_s3.valid, io.refillBufResp_s3.bits.data, io.releaseBufResp_s3.bits.data)
  val hasData_s3 = source_req_s3.opcode(0)
  assert(!(io.refillBufResp_s3.valid && io.releaseBufResp_s3.valid), "can not read both refillBuf and releaseBuf at the same time")

  val wen_a = req_put_full_s3 && io.toSinkA.putReqGood_s3
  val wen_c = sinkC_req_s3 && isParamFromT(req_s3.param) && req_s3.opcode(0) && !need_mshr_s3
  val wen = wen_c || wen_a || req_s3.dsWen && (mshr_grant_s3 || mshr_accessackdata_s3 || mshr_probeack_s3 || mshr_hintack_s3 || mshr_put_s3 || mshr_releaseack_s3)

  val need_data_on_hit_a = req_get_s3 || req_acquireBlock_s3 || req_put_partial_s3
  val need_data_on_miss_a = a_need_replacement // read data ahead of time to prepare for ReleaseData later
  val need_data_on_miss_c = c_need_replacement
  val need_data_b = sinkB_req_s3 && dirResult_s3.hit &&
    (meta_s3.state === TRUNK || meta_s3.state === TIP && meta_s3.dirty || req_s3.needProbeAckData)
  val ren = Mux(dirResult_s3.hit, need_data_on_hit_a, need_data_on_miss_a || need_data_on_miss_c) || need_data_b || task_s3.bits.selfHasData && mshr_req_s3
  val bufResp_s3 = io.bufResp.data.asUInt
  val putBufResp_s3 = RegNext(io.putBufResp) // for Put from A-channel
  val putData_s3 = VecInit(putBufResp_s3.map(_.data)).asUInt // only for putFull data
  val putMask_s3 = VecInit(putBufResp_s3.map(_.mask)).asUInt

  def mergePutData(old_data: UInt, new_data: UInt, wmask: UInt): UInt = {
    val full_wmask = FillInterleaved(8, wmask)
    ((~full_wmask & old_data) | (full_wmask & new_data))
  }

  val putOldData_s3 = Mux(io.refillBufResp_s3.valid, io.refillBufResp_s3.bits.data, Mux(io.releaseBufResp_s3.valid, io.releaseBufResp_s3.bits.data, io.putDataBufResp_s3.bits.data))
  val putPartialData = mergePutData(putOldData_s3, putData_s3, putMask_s3) // TODO: put miss should not use putDataBuf
  val putFullData = putData_s3
  val releaseBufData = io.releaseBufResp_s3.bits.data
  val refillBufData = io.refillBufResp_s3.bits.data
  val mshrWrData = ParallelPriorityMux(Seq(
                      mshr_putpartial_s3 -> putPartialData,
                      mshr_putfull_s3 -> putFullData,
                      mshr_releaseack_s3 -> bufResp_s3, // only for NINE
                      req_s3.useProbeData -> releaseBufData,
                      !req_s3.useProbeData -> refillBufData
                    ))
  dontTouch(mshr_putpartial_s3)
  dontTouch(mshr_putfull_s3)

  if(cacheParams.inclusionPolicy == "NINE") {
    // Free sink c buffer when mshr is not allcated, which means that we will not read this buf anymore.
    // TODO: How about s2 and s3 all need to read? ==> for NINE, move this logic into stage 3
    io.bufRead.valid := task_s3.valid && ( 
                          sinkC_req_s3 && task_s3.bits.opcode(0) && !need_mshr_s3 || 
                          mshr_releaseack_s3
                        )
    io.bufRead.bits.bufIdx := task_s3.bits.bufIdx
    // io.bufRead.bits.bufInvalid.get := io.bufRead.valid && (!need_mshr_s3 || mshr_releaseack_s3)
  }

  io.toDS.req_s3.valid := task_s3.valid && (ren || wen)
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
  // A: need_write_releaseBuf indicates that DS should be read and the data will be written into ReleaseBuffer
  //    need_write_releaseBuf is assigned true when:
  //    inner clients' data is needed, but whether the client will ack data is uncertain, so DS data is also needed, or
  val need_write_releaseBuf = need_probe_s3_a && dirResult_s3.hit || need_data_b && need_mshr_s3_b

  // B: need_write_refillBuf when L1 AcquireBlock BtoT
  //    L2 sends AcquirePerm to L3, so GrantData to L1 needs to read DS ahead of time and store in RefillBuffer
  // TODO: how about AcquirePerm BtoT interaction with refill buffer?
  val need_write_refillBuf = sinkA_req_s3 && req_needT_s3 && dirResult_s3.hit && meta_s3.state === BRANCH && !req_put_s3 && !req_prefetch_s3
  val need_write_putDataBuf = sinkA_req_s3 && req_put_partial_s3 && dirResult_s3.hit

  /* ======== Write Directory ======== */
  val metaW_valid_s3_a = sinkA_req_s3 && !need_mshr_s3_a && !req_get_s3 && !req_prefetch_s3 && !req_put_s3 // get & prefetch that hit will not write meta
  val metaW_valid_s3_b = sinkB_req_s3 && !need_mshr_s3_b && dirResult_s3.hit && (meta_s3.state === TIP || meta_s3.state === BRANCH && req_s3.param === toN)
  val metaW_valid_s3_c = sinkC_req_s3 && !need_mshr_s3_c
  val metaW_valid_s3_repl = mainpipe_release
  val metaW_valid_s3_mshr = mshr_req_s3 && req_s3.metaWen
  if (cacheParams.name != "l3") { // L2
    require(clientBits == 1)
  }
  println(s"clientBits: ${clientBits}")


  /* ======== Directory write logic ======== */
  // Get and Prefetch should not change alias bit

  val metaW_s3_a = {
    val selfState = Mux(req_needT_s3 || sink_resp_s3_a_promoteT, TRUNK, meta_s3.state)
    val clientStates = VecInit(meta_s3.clientStates.zip(reqClientOH.asBools).map {
      case (clientState, en) =>
        Mux(en, Mux(req_needT_s3 || sink_resp_s3_a_promoteT, TIP, BRANCH), clientState)
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

    val clientStates = VecInit(meta_s3.clientStates.zip(reqClientOH.asBools).map {
      case (clientState, en) =>
        Mux(en, Mux(isToN(req_s3.param), INVALID, BRANCH), clientState)
    })

    MetaEntry(
      meta_s3.dirty || wen_c,
      selfState,
      clientStates = clientStates,
    )
  }



  val metaW_s3_repl = MetaEntry()
  val metaW_s3_mshr = req_s3.meta

  if(cacheParams.inclusionPolicy == "NINE") {
    require(cacheParams.name == "l3", "Only L3 support NINE inclusion policy!")
  }


  val clientMetaW_valid_s3_a = sinkA_req_s3 && !need_mshr_s3_a && !req_get_s3 && !req_prefetch_s3 && !req_put_s3 && (hasClientHit || !hasClientHit && !io.clientDirConflict.getOrElse(false.B)) // get & prefetch that hit will not write meta
  val clientMetaW_valid_s3_c = sinkC_req_s3 && !need_mshr_s3_c && (hasClientHit || !hasClientHit && !io.clientDirConflict.getOrElse(false.B))
  val clientMetaW_valid_s3_mshr = mshr_req_s3 && req_s3.clientMetaWen

  val clientMetaW_s3_a    = WireInit(VecInit(Seq.fill(clientBits)(0.U.asTypeOf(new noninclusive.ClientMetaEntry))))
  // val clientMetaW_s3_b    = WireInit(VecInit(Seq.fill(clientBits)(0.U.asTypeOf(new noninclusive.ClientMetaEntry))))
  val clientMetaW_s3_c    = WireInit(VecInit(Seq.fill(clientBits)(0.U.asTypeOf(new noninclusive.ClientMetaEntry))))
  // val clientMetaW_s3_repl = WireInit(VecInit(Seq.fill(clientBits)(0.U.asTypeOf(new noninclusive.ClientMetaEntry))))
  val clientMetaW_s3_mshr = WireInit(VecInit(Seq.fill(clientBits)(0.U.asTypeOf(new noninclusive.ClientMetaEntry))))

  clientMetaW_s3_a.zipWithIndex.foreach{
    case(clientMeta, client) =>
      when(reqClient === client.U) {
        clientMeta.state := Mux(sink_resp_s3_a_promoteT || req_s3.param === NtoT || req_s3.param === BtoT, TIP, BRANCH)
      }.otherwise{
        clientMeta.state := clientMetas_s3(client).state
      }
  }
  clientMetaW_s3_c.zipWithIndex.foreach{
    case(clientMeta, client) =>
      when(reqClient === client.U) {
        clientMeta.state := INVALID
      }.otherwise{
        clientMeta.state := clientMetas_s3(client).state
      }
  }
  clientMetaW_s3_mshr := req_s3.clientMeta


  // Write self meta & tag
  io.metaWReq.valid      := !resetFinish || task_s3.valid && (metaW_valid_s3_a || metaW_valid_s3_b || metaW_valid_s3_c || metaW_valid_s3_mshr || metaW_valid_s3_repl)
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

  io.tagWReq.valid     := task_s3.valid && (mshr_grant_s3 || mshr_accessack_s3 || mshr_accessackdata_s3 || mshr_hintack_s3) && req_s3.tagWen
  io.tagWReq.bits.set  := req_s3.set
  io.tagWReq.bits.way  := req_s3.way
  io.tagWReq.bits.wtag := req_s3.tag


  // Write client meta & tag
  io.clientMetaWReq.foreach{
    clientMetaWReq => 
      // clientMetaWReq <> DontCare // TODO: NINE
      clientMetaWReq.valid := !resetFinishClient || task_s3.valid && (clientMetaW_valid_s3_a || clientMetaW_valid_s3_c || clientMetaW_valid_s3_mshr)
      clientMetaWReq.bits.set := Mux(resetFinishClient, Mux(mshr_req_s3, req_s3.clientSet, clientDirResult_s3.set), resetIdxClient)
      clientMetaWReq.bits.wayOH := Mux(resetFinishClient, UIntToOH(Mux(mshr_req_s3, req_s3.clientWay, clientDirResult_s3.way)), Fill(clientWays, true.B))
      clientMetaWReq.bits.wmeta.zipWithIndex.foreach{
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
  }

  io.clientTagWReq.foreach{
    clientTagWReq =>
      // clientTagWReq <> DontCare // TODO: NINE 
      val clientTagW_valid_s3_a = clientMetaW_valid_s3_a && !clientDirResult_s3.tagMatch
      val clientTagW_valid_s3_mshr = (mshr_grant_s3 || mshr_accessack_s3 || mshr_accessackdata_s3 || mshr_hintack_s3) && req_s3.clientTagWen
      clientTagWReq.valid := task_s3.valid && (clientTagW_valid_s3_mshr || clientTagW_valid_s3_a)
      clientTagWReq.bits.apply(
        Cat(req_s3.tag, req_s3.set),
        Mux(clientTagW_valid_s3_mshr, req_s3.clientWay, clientDirResult_s3.way)
      )
  }



  /* ======== Interact with Channels (C & D) ======== */
  val task_ready_s3 = !hasData_s3 || req_s3.fromC || (need_mshr_s3 && !a_need_replacement) || mshr_req_s3 || req_put_s3
  // do not need s4 & s5
  val req_drop_s3 = (!mshr_req_s3 && need_mshr_s3 && !need_write_releaseBuf && !need_write_refillBuf && !need_write_putDataBuf && !mainpipe_release) ||
                    (task_ready_s3 && (c_s3.fire || d_s3.fire)) ||
                    (mshr_req_s3 && req_s3.fromProbeHelper || !mshr_req_s3 && req_s3.fromProbeHelper)  // We won't send resp for the ProbeHepler request, since it is an inner request not an outer request.
                    
  
  if(cacheParams.inclusionPolicy == "NINE") 
    assert(!(mainpipe_release && req_drop_s3 && !mshr_req_s3))
  
  //[Alias] TODO: may change this to ren?
  val data_unready_s3 = hasData_s3 && !mshr_req_s3 || task_s3.bits.selfHasData && mshr_req_s3
              

  c_s3.valid := task_s3.valid && Mux(
    mshr_req_s3,
    mshr_release_s3 && !req_s3.fromC || mshr_probeack_s3 && !req_s3.fromProbeHelper, // We won't send resp for the ProbeHepler request, since it is an inner request not an outer request.
    req_s3.fromB && !need_mshr_s3 && !data_unready_s3 && !req_s3.fromProbeHelper
  )
  
  d_s3.valid := task_s3.valid && Mux(
    mshr_req_s3,
    mshr_grant_s3 & !task_s3.bits.selfHasData || mshr_accessackdata_s3 || mshr_accessack_s3 || mshr_hintack_s3 || mshr_putpartial_s3 || mshr_releaseack_s3,
    req_s3.fromC && !need_mshr_s3 || req_s3.fromA && !need_mshr_s3 && !mainpipe_release &&(!data_unready_s3 || req_put_full_s3)
  )
  

  c_s3.bits.task      := source_req_s3
  c_s3.bits.data.data := data_s3
  d_s3.bits.task      := source_req_s3
  when(mshr_put_s3) {
    d_s3.bits.task.opcode := AccessAck
  }
  d_s3.bits.data.data := data_s3

  /* ======== nested & prefetch ======== */
  io.nestedwb.set := req_s3.set
  io.nestedwb.tag := req_s3.tag
  io.nestedwb.b_toN := task_s3.valid && metaW_valid_s3_b && req_s3.param === toN
  // io.nestedwb.b_toB := task_s3.valid && metaW_valid_s3_b && req_s3.param =/= toB // assume L3 won't send Probe toT
  io.nestedwb.b_toB := task_s3.valid && metaW_valid_s3_b && req_s3.param === toB
  io.nestedwb.b_clr_dirty := task_s3.valid && metaW_valid_s3_b && meta_s3.dirty
  // c_set_dirty is true iff Release has Data
  io.nestedwb.c_set_dirty := task_s3.valid && metaW_valid_s3_c && wen_c
  io.nestedwb.c_toN := task_s3.valid && metaW_valid_s3_c && isToN(task_s3.bits.param)
  io.nestedwb.c_client := reqClientOH & metaW_valid_s3_c

  io.nestedwbData := bufResp_s3.asTypeOf(new DSBlock)

  io.prefetchTrain.foreach {
    train =>
//      train.valid := task_s3.valid && (req_acquire_s3 || req_get_s3) && req_s3.needHint.getOrElse(false.B) &&
//        (!dirResult_s3.hit || meta_s3.prefetch.get)
//      train.bits.tag := req_s3.tag
//      train.bits.set := req_s3.set
//      train.bits.needT := req_needT_s3
//      train.bits.source := req_s3.sourceId
      train <> DontCare

  }


  // Wake up MSHR that waitting for the ProbeHelper task. (Only for NINE)
  io.probeHelperWakeup.valid := mshr_req_s3 && req_s3.fromProbeHelper || !mshr_req_s3 && req_s3.fromProbeHelper && !need_mshr_s3
  io.probeHelperWakeup.set := req_s3.set
  io.probeHelperWakeup.tag := req_s3.tag
  


  // --------------------------------------------------------------------------
  //  Stage4: 
  // --------------------------------------------------------------------------
  val task_s4 = RegInit(0.U.asTypeOf(Valid(new TaskBundle())))
  val data_unready_s4 = RegInit(false.B)
  val data_s4 = Reg(UInt((blockBytes * 8).W))
  val ren_s4 = RegInit(false.B)
  val need_write_releaseBuf_s4 = RegInit(false.B)
  val need_write_refillBuf_s4 = RegInit(false.B)
  val need_write_putDataBuf_s4 = RegInit(false.B)
  task_s4.valid := task_s3.valid && !req_drop_s3
  when (task_s3.valid && !req_drop_s3) {
    task_s4.bits := source_req_s3
    task_s4.bits.mshrId := Mux(!task_s3.bits.mshrTask && need_mshr_s3, io.fromMSHRCtl.mshr_alloc_ptr, source_req_s3.mshrId)
    data_unready_s4 := data_unready_s3
    data_s4 := data_s3
    ren_s4 := ren
    need_write_releaseBuf_s4 := need_write_releaseBuf
    need_write_refillBuf_s4 := need_write_refillBuf
    need_write_putDataBuf_s4 := need_write_putDataBuf
  }
  val isC_s4 = task_s4.bits.opcode(2, 1) === Release(2, 1) && task_s4.bits.fromA ||
                task_s4.bits.opcode(2, 1) === ProbeAck(2, 1) && task_s4.bits.fromB || 
                task_s4.bits.opcode(2, 1) === Release(2, 1) && task_s4.bits.fromC // for C and c_need_replacement
                
  val isD_s4 =  task_s4.bits.opcode(2, 1) =/= Release(2, 1) && task_s4.bits.fromC || 
                  task_s4.bits.fromA && (
                    task_s4.bits.opcode(2, 1) === Grant(2, 1) ||
                    task_s4.bits.opcode(2, 1) === AccessAck(2, 1) ||
                    task_s4.bits.opcode === HintAck
                  )

  val chnl_fire_s4 = c_s4.fire() || d_s4.fire()

  c_s4.valid := task_s4.valid && !data_unready_s4 && isC_s4 && !need_write_releaseBuf_s4 && !need_write_refillBuf_s4 && !need_write_putDataBuf_s4
  d_s4.valid := task_s4.valid && !data_unready_s4 && isD_s4 && !need_write_releaseBuf_s4 && !need_write_refillBuf_s4 && !need_write_putDataBuf_s4
  c_s4.bits.task := task_s4.bits
  c_s4.bits.data.data := data_s4
  d_s4.bits.task := task_s4.bits
  d_s4.bits.data.data := data_s4


  
  // --------------------------------------------------------------------------
  //  Stage5: 
  // --------------------------------------------------------------------------
  val task_s5 = RegInit(0.U.asTypeOf(Valid(new TaskBundle())))
  val ren_s5 = RegInit(false.B)
  val data_s5 = Reg(UInt((blockBytes * 8).W))
  val need_write_releaseBuf_s5 = RegInit(false.B)
  val need_write_refillBuf_s5 = RegInit(false.B)
  val need_write_putDataBuf_s5 = RegInit(false.B)
  val isC_s5, isD_s5 = RegInit(false.B)
  task_s5.valid := task_s4.valid && !chnl_fire_s4
  when (task_s4.valid && !chnl_fire_s4) {
    task_s5.bits := task_s4.bits
    ren_s5 := ren_s4
    data_s5 := data_s4
    need_write_releaseBuf_s5 := need_write_releaseBuf_s4
    need_write_refillBuf_s5 := need_write_refillBuf_s4
    need_write_putDataBuf_s5 := need_write_putDataBuf_s4
    isC_s5 := isC_s4
    isD_s5 := isD_s4
  }
  val rdata_s5 = io.toDS.rdata_s5.data
  task_s5.bits.corrupt := Mux(ren_s5, io.toDS.error_s5, false.B)
  val merged_data_s5 = Mux(ren_s5, rdata_s5, data_s5)
  val chnl_fire_s5 = c_s5.fire() || d_s5.fire()

  val customL1Hint = Module(new CustomL1Hint)

  customL1Hint.io.s1 := io.taskInfo_s1
  customL1Hint.io.s2 := task_s2
  
  customL1Hint.io.s3.task      := task_s3
  customL1Hint.io.s3.d         := d_s3.valid
  customL1Hint.io.s3.need_mshr := need_mshr_s3

  customL1Hint.io.s4.task                  := task_s4
  customL1Hint.io.s4.d                     := d_s4.valid
  customL1Hint.io.s4.need_write_releaseBuf := need_write_releaseBuf_s4
  customL1Hint.io.s4.need_write_refillBuf  := need_write_refillBuf_s4

  customL1Hint.io.s5.task      := task_s5
  customL1Hint.io.s5.d         := d_s5.valid

  customL1Hint.io.globalCounter   := io.globalCounter
  customL1Hint.io.grantBufferHint <> io.grantBufferHint

  customL1Hint.io.l1Hint <> io.l1Hint

  io.releaseBufWrite.valid      := task_s5.valid && need_write_releaseBuf_s5
  io.releaseBufWrite.beat_sel   := Fill(beatSize, 1.U(1.W))
  io.releaseBufWrite.data.data  := merged_data_s5
  io.releaseBufWrite.id         := task_s5.bits.mshrId
  io.releaseBufWrite.corrupt    := task_s5.bits.corrupt // TODO: Ecc
  assert(!(io.releaseBufWrite.valid && !io.releaseBufWrite.ready), "releaseBuf should be ready when given valid")

  io.refillBufWrite.valid     := task_s5.valid && need_write_refillBuf_s5
  io.refillBufWrite.beat_sel  := Fill(beatSize, 1.U(1.W))
  io.refillBufWrite.data.data := merged_data_s5
  io.refillBufWrite.id        := task_s5.bits.mshrId
  io.refillBufWrite.corrupt   := task_s5.bits.corrupt // TODO: Ecc
  assert(!(io.refillBufWrite.valid && !io.refillBufWrite.ready), "releaseBuf should be ready when given valid")

  io.putDataBufWrite.valid        := task_s5.valid && need_write_putDataBuf_s5
  io.putDataBufWrite.beat_sel     := Fill(beatSize, 1.U(1.W))
  io.putDataBufWrite.data.data    := merged_data_s5
  io.putDataBufWrite.id           := task_s5.bits.sourceId // TODO:
  io.putDataBufWrite.corrupt      := task_s5.bits.corrupt || io.toDS.error_s5

  c_s5.valid := task_s5.valid && isC_s5 && !need_write_releaseBuf_s5 && !need_write_refillBuf_s5 && !need_write_putDataBuf_s5
  d_s5.valid := task_s5.valid && isD_s5 && !need_write_releaseBuf_s5 && !need_write_refillBuf_s5 && !need_write_putDataBuf_s5
  c_s5.bits.task := task_s5.bits
  c_s5.bits.data.data := merged_data_s5
  d_s5.bits.task := task_s5.bits
  d_s5.bits.data.data := merged_data_s5



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

  io.toReqArb.blockC_s1 :=
    task_s2.valid && task_s2.bits.set === io.fromReqArb.status_s1.c_set ||
    io.toMSHRCtl.mshr_alloc_s3.valid && task_s3.bits.set === io.fromReqArb.status_s1.c_set
  io.toReqArb.blockB_s1 :=
    task_s2.valid && pipelineBlock('b', task_s2.bits, allTask = true) ||
    task_s3.valid && pipelineBlock('b', task_s3.bits)                 ||
    task_s4.valid && pipelineBlock('b', task_s4.bits, tag = true)     ||
    task_s5.valid && pipelineBlock('b', task_s5.bits, tag = true)
  io.toReqArb.blockA_s1 := io.toReqBuf(0) || io.toReqBuf(1)



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
  io.status_vec(1).valid        := task_s4.valid && isD_s4 && !need_write_releaseBuf_s4 && !need_write_refillBuf_s4
  io.status_vec(1).bits.channel := task_s4.bits.channel
  io.status_vec(2).valid        := d_s5.valid
  io.status_vec(2).bits.channel := task_s5.bits.channel

  // make sure we don't send two reqs continuously with the same set
  assert(!(task_s2.bits.set === task_s3.bits.set &&
    task_s2.valid && !task_s2.bits.mshrTask && task_s2.bits.fromA &&
    task_s3.valid && !task_s3.bits.mshrTask && task_s3.bits.fromA),
    "s2 and s3 task same set, failed in blocking")



  // --------------------------------------------------------------------------
  //  Other Signals Assignment
  // --------------------------------------------------------------------------
  val c = Seq(c_s5, c_s4, c_s3)
  val d = Seq(d_s5, d_s4, d_s3)
  // DO NOT use TLArbiter because TLArbiter will send continuous beats for the same source
  val fifoArbEntries =  5
  val c_arb = Module(new FIFOArbiter(io.toSourceC.bits.cloneType, c.size, fifoArbEntries))
  val d_arb = Module(new FIFOArbiter(io.toSourceD.bits.cloneType, d.size, fifoArbEntries))
  // val c_arb = Module(new Arbiter(io.toSourceC.bits.cloneType, c.size))
  // val d_arb = Module(new Arbiter(io.toSourceD.bits.cloneType, d.size))
  c_arb.io.in <> c
  d_arb.io.in <> d

  io.toSourceC <> c_arb.io.out
  io.toSourceD <> d_arb.io.out

  assert(!(d_s3.valid && d_s3.bits.task.opcode === 7.U), "d_s3 invalid opcode: 7  mshrTask:%d mshrId:%d Tag:0x%x Set:0x%x", req_s3.mshrTask, req_s3.mshrId, req_s3.tag, req_s3.set)
  assert(!(d_s4.valid && d_s4.bits.task.opcode === 7.U), "d_s4 invalid opcode: 7  mshrTask:%d mshrId:%d Tag:0x%x Set:0x%x", task_s4.bits.mshrTask, task_s4.bits.mshrId, task_s4.bits.tag, task_s4.bits.set)
  assert(!(d_s5.valid && d_s5.bits.task.opcode === 7.U), "d_s5 invalid opcode: 7  mshrTask:%d mshrId:%d Tag:0x%x Set:0x%x", task_s5.bits.mshrTask, task_s5.bits.mshrId, task_s5.bits.tag, task_s5.bits.set)



  // --------------------------------------------------------------------------
  //  Performance counters
  // --------------------------------------------------------------------------
  // num of mshr req
  XSPerfAccumulate(cacheParams, "mshr_grant_req", task_s3.valid && mshr_grant_s3)
  XSPerfAccumulate(cacheParams, "mshr_grantdata_req", task_s3.valid && mshr_grantdata_s3)
  XSPerfAccumulate(cacheParams, "mshr_accessackdata_req", task_s3.valid && mshr_accessackdata_s3)
  XSPerfAccumulate(cacheParams, "mshr_accessack_req", task_s3.valid && mshr_accessack_s3)
  XSPerfAccumulate(cacheParams, "mshr_hintack_req", task_s3.valid && mshr_hintack_s3)
  XSPerfAccumulate(cacheParams, "mshr_probeack_req", task_s3.valid && mshr_probeack_s3)
  XSPerfAccumulate(cacheParams, "mshr_probeackdata_req", task_s3.valid && mshr_probeackdata_s3)
  XSPerfAccumulate(cacheParams, "mshr_release_req", task_s3.valid && mshr_release_s3)

  // directory access result
  val hit_s3 = task_s3.valid && !mshr_req_s3 && dirResult_s3.hit
  val miss_s3 = task_s3.valid && !mshr_req_s3 && !dirResult_s3.hit
  XSPerfAccumulate(cacheParams, "a_req_hit", hit_s3 && req_s3.fromA)
  XSPerfAccumulate(cacheParams, "acquire_hit", hit_s3 && req_s3.fromA &&
    (req_s3.opcode === AcquireBlock || req_s3.opcode === AcquirePerm))
  XSPerfAccumulate(cacheParams, "get_hit", hit_s3 && req_s3.fromA && req_s3.opcode === Get)

  XSPerfAccumulate(cacheParams, "a_req_miss", miss_s3 && req_s3.fromA)
  XSPerfAccumulate(cacheParams, "acquire_miss", miss_s3 && req_s3.fromA &&
    (req_s3.opcode === AcquireBlock || req_s3.opcode === AcquirePerm))
  XSPerfAccumulate(cacheParams, "get_miss", miss_s3 && req_s3.fromA && req_s3.opcode === Get)

  // XSPerfAccumulate(cacheParams, "a_req_need_replacement",
  //   io.toMSHRCtl.mshr_alloc_s3.valid && !alloc_state.s_release || task_s3.valid && mainpipe_release)
  XSPerfAccumulate(cacheParams, "a_req_need_replacement",
    io.toMSHRCtl.mshr_alloc_s3.valid && !io.toMSHRCtl.mshr_alloc_s3.bits.state.s_release || task_s3.valid && mainpipe_release)

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

  // XSPerfAccumulate(cacheParams, "a_req_tigger_prefetch", io.prefetchTrain.)
  prefetchOpt.foreach {
    _ =>
      XSPerfAccumulate(cacheParams, "a_req_trigger_prefetch", io.prefetchTrain.get.fire())
      XSPerfAccumulate(cacheParams, "a_req_trigger_prefetch_not_ready", io.prefetchTrain.get.valid && !io.prefetchTrain.get.ready)
      XSPerfAccumulate(cacheParams, "acquire_trigger_prefetch_on_miss", io.prefetchTrain.get.fire() && req_acquire_s3 && !dirResult_s3.hit)
//      XSPerfAccumulate(cacheParams, "acquire_trigger_prefetch_on_hit_pft", io.prefetchTrain.get.fire() && req_acquire_s3 && dirResult_s3.hit && meta_s3.prefetch.get)
//      XSPerfAccumulate(cacheParams, "release_all", mshr_release_s3)
//      XSPerfAccumulate(cacheParams, "release_prefetch_accessed", mshr_release_s3 && meta_s3.prefetch.get && meta_s3.accessed)
//      XSPerfAccumulate(cacheParams, "release_prefetch_not_accessed", mshr_release_s3 && meta_s3.prefetch.get && !meta_s3.accessed)
//      XSPerfAccumulate(cacheParams, "get_trigger_prefetch_on_miss", io.prefetchTrain.get.fire() && req_get_s3 && !dirResult_s3.hit)
//      XSPerfAccumulate(cacheParams, "get_trigger_prefetch_on_hit_pft", io.prefetchTrain.get.fire() && req_get_s3 && dirResult_s3.hit && meta_s3.prefetch.get)
  }

  /* ===== Monitor ===== */
  io.toMonitor.task_s2 := task_s2
  io.toMonitor.task_s3 := task_s3
  io.toMonitor.task_s4 := task_s4
  io.toMonitor.task_s5 := task_s5
  io.toMonitor.dirResult_s3 := dirResult_s3
}
