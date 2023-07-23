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


// Coherence checker (Combinational Logic)
class CohChecker(implicit p: Parameters) extends L2Module {
  val io = IO(new Bundle{
    val in = new Bundle{
      // task info (from MainPipe stage 3)
      val task = Flipped(Valid(new TaskBundle()))

      // directory result (from MainPipe stage 3)
      val dirResult = Input(new DirResult)
      val clientDirResult = if(cacheParams.inclusionPolicy == "NINE") Some(Input(new noninclusive.ClientDirResult)) else None

      // from ProbeHelper, arrive with clientDirResult
      val clientDirConflict = Input(Bool())
    }
   
    val out = new Bundle{
      val mshrAlloc = Valid(new MSHRRequest)
      val flags = Output(new Bundle{
        val cacheAlias = Bool()
        val aNeedReplacement = Bool()
        val cNeedReplacement = Bool()
        val aNeedProbe = Bool()
        val aNeedMSHR = Bool()
        val bNeedMSHR = Bool()
        val cNeedMSHR = Bool()
        val needMSHR = Bool()
      })
    }
  })
  // io.out.mshrAlloc <> DontCare

  // Signal alias
  val task      = io.in.task
  val dirResult = io.in.dirResult
  val meta      = io.in.dirResult.meta
  val metaError = dirResult.error

  val req      = io.in.task.bits
  val reqNeedT = needT(req.opcode, req.param)
  val mshrReq  = req.mshrTask
  val sinkReq  = !mshrReq
  val sinkReqA = !mshrReq && req.fromA
  val sinkReqC = !mshrReq && req.fromC

  val reqAcquire      = sinkReqA && (req.opcode === AcquireBlock || req.opcode === AcquirePerm)
  val reqAcquireBlock = sinkReqA && req.opcode === AcquireBlock
  val reqPrefetch     = sinkReqA && req.opcode === Hint
  val reqGet          = sinkReqA && req.opcode === Get
  val reqPutFull      = sinkReqA && req.opcode === PutFullData
  val reqPutPartial   = sinkReqA && req.opcode === PutPartialData
  val reqPut          = reqPutFull || reqPutPartial


  // Clients releted signal // TODO: passed from outer MainPipe ??
  val reqClient = Wire(UInt((log2Up(clientBits) + 1).W)) // Which client does this req come from?
  val reqClientOH = getClientBitOH(task.bits.sourceId) // ! This is only for channel task
  reqClient := Mux(reqClientOH === 0.U, Cat(1.U(1.W), 0.U(log2Up(clientBits).W)), OHToUInt(reqClientOH)) // The highest bit of reqClient indicates that req comes from TL-UL node


  // client dir result (Only for NINE)
  val clientDirResult = io.in.clientDirResult.getOrElse(0.U.asTypeOf(new noninclusive.ClientDirResult))
  val hasClientHit = clientDirResult.hits.asUInt.orR
  val clientMetas = clientDirResult.metas
  dontTouch(clientDirResult)


  // Client directory info(except ReqClient)
  val exceptReqClientHitOH = clientDirResult.hits.asUInt & ~reqClientOH
  val exceptReqClientMeta = VecInit(exceptReqClientHitOH.asBools.zip(clientDirResult.metas).map {
                                case (en, clientMeta) => 
                                  Mux(en, clientMeta, 0.U.asTypeOf(new noninclusive.ClientMetaEntry))
                              })
  dontTouch(exceptReqClientHitOH) 
  dontTouch(exceptReqClientMeta)


  val highestState = ParallelMax(
    Seq(Mux(dirResult.hit, meta.state, INVALID)) ++
    clientDirResult.hits.zip(clientDirResult.metas).map{
      case(clientHit, clientMeta) => 
        Mux(clientHit, clientMeta.state, INVALID)
    }
  )
  val highestStateExceptReqClient = ParallelMax(
    Seq(Mux(dirResult.hit, meta.state, INVALID)) ++
    clientDirResult.hits.zip(clientDirResult.metas).zipWithIndex.map{
      case ((clientHit, clientMeta), client) => 
        Mux(reqClient === client.U, INVALID, Mux(clientHit, clientMeta.state, INVALID))
    }
  )
  dontTouch(highestState)
  dontTouch(highestStateExceptReqClient)

  
  def restoreAddr(set: UInt, tag: UInt) = {
    (set << offsetBits).asUInt + (tag << (setBits + offsetBits)).asUInt
  }
  val debugAddr = restoreAddr(req.set, req.tag)
  dontTouch(debugAddr)


  // Coherence flag signals
  val cacheAlias       = WireInit(false.B)
  val aNeedReplacement = WireInit(false.B)
  val aNeedAcquire     = WireInit(false.B)
  val aNeedProbe       = WireInit(false.B)
  val aTrigProbeHelper = WireInit(false.B)
  val bNeedProbeackThrough = WireInit(false.B) // This flag indicate that a receiving probeack with self.miss will turn into release requst
  val cNeedReplacement = WireInit(false.B)
  val aNeedMSHR        = WireInit(false.B)
  val bNeedMSHR        = WireInit(false.B)
  val cNeedMSHR        = WireInit(false.B)
  val needMSHR         = WireInit(false.B)


  // Allocation of MSHR: new request only
  val allocState = WireInit(0.U.asTypeOf(new FSMState()))
  allocState.elements.foreach(_._2 := true.B)

  val replaceClientsState = ParallelMax(meta.clientStates)
  val replaceNeedRelease = meta.state > replaceClientsState || meta.dirty && isT(meta.state)
  aNeedReplacement := req.fromA && !dirResult.hit && meta.state =/= INVALID && replaceNeedRelease // && (req_acquireBlock_s3 && !reqNeedT || transmitFromOtherClient)

  cacheAlias := false.B

  aNeedAcquire := Mux(
                      reqAcquire,
                      Mux(reqNeedT, !isT(highestStateExceptReqClient), highestStateExceptReqClient === INVALID), // AcqurieBlock / AcquirePerm
                      Mux(reqNeedT, !isT(highestState), highestState === INVALID) // Put / Get / Prefetch
                  )

  val exceptReqClientMetaHasT = Cat(exceptReqClientMeta.map( meta => isT(meta.state) )).orR
  aNeedProbe := sinkReqA && exceptReqClientHitOH.orR && ( reqNeedT || !dirResult.hit || exceptReqClientMetaHasT )
  aTrigProbeHelper := sinkReqA && dirResult.hit && io.in.clientDirConflict

  bNeedProbeackThrough := !dirResult.hit && dirResult.meta.state =/= INVALID && replaceNeedRelease

  cNeedReplacement := req.fromC && !dirResult.hit && dirResult.meta.state =/= INVALID && replaceNeedRelease

  assert(reqPutPartial =/= true.B, "TODO: reqPutPartial")
  aNeedMSHR := sinkReqA && ( aNeedAcquire || aNeedProbe || aTrigProbeHelper || aNeedReplacement || cacheAlias || reqPutPartial)
  bNeedMSHR := req.fromProbeHelper && req.fromB && hasClientHit
  cNeedMSHR := sinkReqC && cNeedReplacement // TODO: NINE

  needMSHR := (aNeedMSHR || bNeedMSHR || cNeedMSHR) && !metaError

  // s_refill:                            need to schedule GrantData for the reqClient
  // w_grantack:                          need to wait for GrantAck from reqClient
  // s_put_wb:                            TODO: doc
  // w_releaseack:                        need to wait for ReleaseAck from the next level device
  // w_release_sent:                      need to wait for MainPipe issue Release request to the next level device
  // s_acquire:                           need to schedule Acquire to the next level device
  // w_grantfirst, w_grantlast, w_grant:  need to wait for GrantData/Grant from the next level device
  // s_rprobe:                            need to schedule Probe to the clients due to replace release
  // w_rprobeackfirst, w_rprobeacklast:   need to wait for ProbeAck/ProbeAckData from clients
  // TODO: others...
  when(req.fromA) {
    allocState.w_probehelper_done := !io.in.clientDirConflict

    allocState.s_refill := reqPut && dirResult.hit // put request will not cause refill and grnatAck
    allocState.w_grantack := reqPrefetch || reqGet || reqPut
    allocState.s_put_wb := !reqPut
    // need replacement
    when(aNeedReplacement) {
      allocState.w_releaseack := false.B
      allocState.w_release_sent := false.B

      // need rprobe for release
      // Foe NINE, do nothing here.
    }.otherwise {
      allocState.w_release_sent := allocState.s_acquire || allocState.s_release
      assert(allocState.s_acquire || allocState.s_release)
    }
    // need Acquire downwards
    when(aNeedAcquire) {
      allocState.s_acquire := false.B
      allocState.w_grantfirst := false.B
      allocState.w_grantlast := false.B
      allocState.w_grant := false.B
    }
    // need Probe for alias
    // need Probe when Get hits on a TRUNK block
    when(cacheAlias || aNeedProbe) {
      assert(cacheAlias === false.B, "L3 does not have cacheAlias case")

      allocState.s_rprobe := false.B
      allocState.w_rprobeackfirst := false.B
      allocState.w_rprobeacklast := false.B
    }
  }

  when(req.fromB) {
    when(!mshrReq) {
      assert(req.fromProbeHelper, "L3 NINE can only accept b request from ProbeHelper")
    }

    // Only consider the situation when mshr needs to be allocated
    allocState.s_pprobe := false.B
    allocState.w_pprobeackfirst := false.B
    allocState.w_pprobeacklast := false.B
    allocState.w_pprobeack := false.B
    allocState.s_probeack := false.B // Notice: req.fromProbeHelper does not need probeack for the next level device but need to update clientDir

    when(bNeedProbeackThrough) { // turn probeack into release
      allocState.s_release := false.B
      allocState.w_releaseack := false.B

      allocState.s_probeack := true.B // In this case release will help write client dir
    }
  }

  when(req.fromC) {
    when(cNeedReplacement) {
      // allocState.s_release := false.B
      // allocState.w_releaseack := false.B
      allocState.s_releaseack := false.B // Send releaseack and write meta & data
      allocState.w_release_sent := false.B // Waitting for mainpipe send release
      allocState.w_releaseack := false.B // Waitting for receiving ReleaseAck send by mainpipe
    }
  }


  assert(
    RegNext(!(sinkReqC && !clientDirResult.hits.asUInt.orR)),
    "C Release should have some clients hit, Tag:0x%x Set:0x%x Addr:0x%x Source:%d isMSHRTask:%d MSHR:%d",
    RegNext(req.tag), RegNext(req.set), RegNext(debugAddr), RegNext(req.sourceId), RegNext(req.mshrTask), RegNext(req.mshrId)
  )

  assert(
    RegNext(!(task.valid && !mshrReq && dirResult.hit && meta.state === TRUNK && !clientDirResult.hits.asUInt.orR)),
    "Trunk should have some client hit, Tag:0x%x Set:0x%x Addr:0x%x Source:%d isMSHRTask:%d MSHR:%d",
    RegNext(req.tag), RegNext(req.set), RegNext(debugAddr), RegNext(req.sourceId), RegNext(req.mshrTask), RegNext(req.mshrId)
  )


  val mshrTask = Wire(new TaskBundle)
  mshrTask := DontCare
  mshrTask.channel := req.channel
  mshrTask.set := req.set
  mshrTask.tag := req.tag
  mshrTask.off := req.off
  mshrTask.alias.foreach(_ := req.alias.getOrElse(0.U))
  mshrTask.opcode := req.opcode
  mshrTask.param := req.param
  mshrTask.size := req.size
  mshrTask.sourceId := req.sourceId
  mshrTask.needProbeAckData := req.needProbeAckData
  mshrTask.aliasTask.foreach(_ := cacheAlias)
  mshrTask.useProbeData := false.B  
  mshrTask.pbIdx := req.pbIdx // SinkA buf index
  mshrTask.bufIdx := req.bufIdx // SinkC buf index
  mshrTask.fromL2pft.foreach(_ := req.fromL2pft.get)
  mshrTask.needHint.foreach(_ := req.needHint.get)
  mshrTask.fromProbeHelper := req.fromProbeHelper
  mshrTask.way := dirResult.way
  mshrTask.reqSource := req.reqSource

  io.out.mshrAlloc.valid := needMSHR && task.valid && !mshrReq
  io.out.mshrAlloc.bits.task := mshrTask
  io.out.mshrAlloc.bits.dirResult := dirResult
  io.out.mshrAlloc.bits.clientDirResult.foreach( _ := clientDirResult)
  io.out.mshrAlloc.bits.state := allocState

  io.out.flags.cacheAlias := cacheAlias
  io.out.flags.aNeedReplacement := aNeedReplacement
  io.out.flags.cNeedReplacement := cNeedReplacement
  io.out.flags.aNeedProbe := aNeedProbe
  io.out.flags.aNeedMSHR := aNeedMSHR
  io.out.flags.bNeedMSHR := bNeedMSHR
  io.out.flags.cNeedMSHR := cNeedMSHR
  io.out.flags.needMSHR := needMSHR

}