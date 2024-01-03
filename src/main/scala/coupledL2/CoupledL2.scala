/** *************************************************************************************
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
  * *************************************************************************************
  */

// See LICENSE.SiFive for license details.

package coupledL2

import chisel3._
import chisel3.util._
import xs.utils.{DFTResetSignals, FastArbiter, ModuleNode, Pipeline, ResetGen, ResetGenNode}
import freechips.rocketchip.diplomacy._
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tilelink.TLMessages._
import freechips.rocketchip.util._
import org.chipsalliance.cde.config.Parameters
import coupledL2.prefetch._
import xs.utils.mbist.{MBISTInterface, MBISTPipeline}
import xs.utils.perf.{DebugOptionsKey, HasPerfLogging}
import xs.utils.sram.SRAMTemplate
import coupledL2.utils.HasPerfEvents
import freechips.rocketchip.interrupts.{IntSourceNode, IntSourcePortSimple}

trait HasCoupledL2Parameters {
  val p: Parameters
  val cacheParams = p(L2ParamKey)

  val blocks = cacheParams.sets * cacheParams.ways
  val blockBytes = cacheParams.blockBytes
  val beatBytes = cacheParams.channelBytes.d.get
  val beatSize = blockBytes / beatBytes

  val wayBits = log2Ceil(cacheParams.ways)
  val setBits = log2Ceil(cacheParams.sets)
  val offsetBits = log2Ceil(blockBytes)
  val beatBits = offsetBits - log2Ceil(beatBytes)
  val stateBits = MetaData.stateBits
  val aliasBitsOpt = if(cacheParams.clientCaches.isEmpty) None
                  else cacheParams.clientCaches.head.aliasBitsOpt
  val vaddrBitsOpt = if(cacheParams.clientCaches.isEmpty) None
                  else cacheParams.clientCaches.head.vaddrBitsOpt
  val pageOffsetBits = log2Ceil(cacheParams.pageBytes)

  val bufBlocks = 8 // hold data that flows in MainPipe (4)
  val bufIdxBits = log2Up(bufBlocks)

  val enableClockGate = cacheParams.enableClockGate

  val dataEccCode = cacheParams.dataEccCode
  val dataEccEnable = dataEccCode != None && dataEccCode != Some("none")

  // 1 cycle for sram read, and latch for another cycle
  val sramLatency = 2

  val releaseBufWPorts = 3 // sinkC & mainPipe s5 & mainPipe s3 (nested)

  // Prefetch
  val prefetchOpt = cacheParams.prefetch
  val Csr_PfCtrlBits = cacheParams.Csr_PfCtrlBits
  val sppMultiLevelRefillOpt = cacheParams.sppMultiLevelRefill
  val hasPrefetchBit = prefetchOpt.nonEmpty && prefetchOpt.get.hasPrefetchBit
  val topDownOpt = if(cacheParams.elaboratedTopDown) Some(true) else None

  lazy val edgeIn = p(EdgeInKey)
  lazy val edgeOut = p(EdgeOutKey)
  lazy val bankBits = p(BankBitsKey)

  lazy val clientBits = edgeIn.client.clients.count(_.supports.probe)
  lazy val sourceIdBits = edgeIn.bundle.sourceBits // ids of L1
  lazy val msgSizeBits = edgeIn.bundle.sizeBits
  lazy val sourceIdAll = 1 << sourceIdBits

  val mshrsAll = cacheParams.mshrs
  val idsAll = 256// ids of L2 //TODO: Paramterize like this: max(mshrsAll * 2, sourceIdAll * 2)
  val mshrBits = log2Up(idsAll)
  // id of 0XXXX refers to mshrId
  // id of 1XXXX refers to reqs that do not enter mshr
  // require(isPow2(idsAll))

  val grantBufSize = mshrsAll
  val grantBufInflightSize = mshrsAll //TODO: lack or excessive? !! WARNING

  // width params with bank idx (used in prefetcher / ctrl unit)
  lazy val fullAddressBits = edgeOut.bundle.addressBits
  lazy val fullTagBits = fullAddressBits - setBits - offsetBits
  // width params without bank idx (used in slice)
  lazy val addressBits = fullAddressBits - bankBits
  lazy val tagBits = fullTagBits - bankBits

  lazy val outerSinkBits = edgeOut.bundle.sinkBits

  def getClientBitOH(sourceId: UInt): UInt = {
    if (clientBits == 0) {
      0.U
    } else {
      Cat(
        edgeIn.client.clients
          .filter(_.supports.probe)
          .map(c => {
            c.sourceId.contains(sourceId).asInstanceOf[Bool]
          })
          .reverse
      )
    }
  }

  def getSourceId(client: UInt): UInt = {
    if (clientBits == 0) {
      0.U
    } else {
      Mux1H(
        client,
        edgeIn.client.clients
          .filter(_.supports.probe)
          .map(c => c.sourceId.start.U)
      )
    }
  }

  def parseFullAddress(x: UInt): (UInt, UInt, UInt) = {
    val offset = x // TODO: check address mapping
    val set = offset >> offsetBits
    val tag = set >> setBits
    (tag(fullTagBits - 1, 0), set(setBits - 1, 0), offset(offsetBits - 1, 0))
  }

  def parseAddress(x: UInt): (UInt, UInt, UInt) = {
    val offset = x
    val set = offset >> (offsetBits + bankBits)
    val tag = set >> setBits
    (tag(tagBits - 1, 0), set(setBits - 1, 0), offset(offsetBits - 1, 0))
  }

  def getPPN(x: UInt): UInt = {
    x(x.getWidth - 1, pageOffsetBits)
  }

  def fastArb[T <: Bundle](in: Seq[DecoupledIO[T]], out: DecoupledIO[T], name: Option[String] = None): Unit = {
    val arb = Module(new FastArbiter[T](chiselTypeOf(out.bits), in.size))
    if (name.nonEmpty) { arb.suggestName(s"${name.get}_arb") }
    for ((a, req) <- arb.io.in.zip(in)) { a <> req }
    out <> arb.io.out
  }

  def odOpGen(r: UInt) = {
    val grantOp = GrantData
    val opSeq = Seq(AccessAck, AccessAck, AccessAckData, AccessAckData, AccessAckData, HintAck, grantOp, Grant)
    val opToA = VecInit(opSeq)(r)
    opToA
  }
}

class CoupledL2(parentName:String = "L2_")(implicit p: Parameters) extends LazyModule with HasCoupledL2Parameters {

  val xfer = TransferSizes(blockBytes, blockBytes)
  val atom = TransferSizes(1, cacheParams.channelBytes.d.get)
  val access = TransferSizes(1, blockBytes)

  val clientPortParams = (m: TLMasterPortParameters) => TLMasterPortParameters.v2(
    Seq(
      TLMasterParameters.v2(
        name = cacheParams.name,
        supports = TLSlaveToMasterTransferSizes(
          probe = xfer
        ),
        sourceId = {
          println(s"[Diplomacy stage] ${cacheParams.name} client num: ${m.masters.length}")
          println(s"[Diplomacy stage] ${cacheParams.name} client sourceId:")
          m.masters.zipWithIndex.foreach{case(m, i) => println(s"[Diplomacy stage] \t[${i}]${m.name} => start: ${m.sourceId.start} end: ${m.sourceId.end}")}
          val idEnd = 64 // TODO：Parameterize
          println(s"[Diplomacy stage] ${cacheParams.name} sourceId idRange(0, ${idEnd})\n")
          IdRange(0, 64)
        }
        
      )
    ),
    channelBytes = cacheParams.channelBytes,
    minLatency = 1,
    echoFields = cacheParams.echoField,
    requestFields = cacheParams.reqField,
    responseKeys = cacheParams.respKey
  )

  val managerPortParams = (m: TLSlavePortParameters) => TLSlavePortParameters.v1(
    m.managers.map { m =>
      m.v2copy(
        regionType = if (m.regionType >= RegionType.UNCACHED) RegionType.CACHED else m.regionType,
        supports = TLMasterToSlaveTransferSizes(
          acquireB = xfer,
          acquireT = if (m.supportsAcquireT) xfer else TransferSizes.none,
          arithmetic = if (m.supportsAcquireT) atom else TransferSizes.none,
          logical = if (m.supportsAcquireT) atom else TransferSizes.none,
          get = access,
          putFull = if (m.supportsAcquireT) access else TransferSizes.none,
          putPartial = if (m.supportsAcquireT) access else TransferSizes.none,
          hint = access
        ),
        fifoId = None
      )
    },
    beatBytes = 32,
    minLatency = 2,
    responseFields = cacheParams.respField,
    requestKeys = cacheParams.reqKey,
    endSinkId = idsAll
  )

  val node = TLAdapterNode(
    clientFn = clientPortParams,
    managerFn = managerPortParams
  )

 val pf_recv_node: Option[BundleBridgeSink[PrefetchRecv]] = prefetchOpt match {
  case Some(receive: PrefetchReceiverParams) => Some(BundleBridgeSink(Some(() => new PrefetchRecv)))
  case Some(sms_sender_hyper: HyperPrefetchParams) => Some(BundleBridgeSink(Some(() => new PrefetchRecv)))
  case _ => None
}

  val spp_send_node: Option[BundleBridgeSource[LlcPrefetchRecv]] = prefetchOpt match {
    case Some(hyper_pf: HyperPrefetchParams) =>
      sppMultiLevelRefillOpt match{
        case Some(receive: PrefetchReceiverParams) =>
          Some(BundleBridgeSource(() => new LlcPrefetchRecv()))
        case _ => None
      }
    case Some(spp_only: SPPParameters) =>
      sppMultiLevelRefillOpt match{
        case Some(receive: PrefetchReceiverParams) => 
          Some(BundleBridgeSource(Some(() => new LlcPrefetchRecv())))
        case _ => None
      }
    case _ => None //Spp not exist, can not use multl-level refill
  }
  val device = new SimpleDevice("l2", Seq("xiangshan,cpl2"))
  val intNode = IntSourceNode(IntSourcePortSimple(resources = device.int))

  lazy val module = new Impl
  class Impl extends LazyModuleImp(this) with HasPerfLogging with HasPerfEvents{
    val banks = node.in.size
    val bankBits = if (banks == 1) 0 else log2Up(banks)
    val io = IO(new Bundle {
      val dfx_reset = Input(new DFTResetSignals())
      /* debug signals */
//       val fpga_dbg = Vec(banks, Vec(mshrsAll, ValidIO(new L2MSHRDbgSignal)))
      val fpga_dbg = Vec(banks, Vec(mshrsAll, ValidIO(new L2MSHRDbgSignal)))
    })

    // Display info
    val sizeBytes = cacheParams.toCacheParams.capacity.toDouble
    def sizeBytesToStr(sizeBytes: Double): String = sizeBytes match {
      case _ if sizeBytes >= 1024 * 1024 => (sizeBytes / 1024 / 1024) + "MB"
      case _ if sizeBytes >= 1024        => (sizeBytes / 1024) + "KB"
      case _                            => "B"
    }
    val sizeStr = sizeBytesToStr(sizeBytes)
    val prefetch = "prefetch: " + cacheParams.prefetch
    println(s"====== Inclusive ${cacheParams.name} ($sizeStr * $banks-bank) $prefetch ======")
    println(s"bankBits: ${bankBits}")
    println(s"replacement: ${cacheParams.replacement}")
    println(s"replace policy: ${cacheParams.releaseData}")
    println(s"sets:${cacheParams.sets} ways:${cacheParams.ways} blockBytes:${cacheParams.blockBytes}")
    def print_bundle_fields(fs: Seq[BundleFieldBase], prefix: String) = {
      if(fs.nonEmpty){
        println(fs.map{f => s"$prefix/${f.key.name}: (${f.data.getWidth}-bit)"}.mkString("\n"))
      }
    }
    print_bundle_fields(node.in.head._2.bundle.requestFields, "usr")
    print_bundle_fields(node.in.head._2.bundle.echoFields, "echo")

    node.edges.in.headOption.foreach { n =>
      n.client.clients.zipWithIndex.foreach {
        case (c, i) =>
          println(s"\t${i} <= ${c.name}")
      }
    }

    // connection between prefetcher and the slices
    val pftParams: Parameters = p.alterPartial {
      case EdgeInKey => node.in.head._2
      case EdgeOutKey => node.out.head._2
      case BankBitsKey => bankBits
    }
    val prefetcher = prefetchOpt.map(_ => Module(new Prefetcher(parentName + "pft_")(pftParams)))
    val prefetchTrains = prefetchOpt.map(_ => Wire(Vec(banks, DecoupledIO(new PrefetchTrain()(pftParams)))))
    val prefetchResps = prefetchOpt.map(_ => Wire(Vec(banks, DecoupledIO(new PrefetchResp()(pftParams)))))
    val prefetchEvicts = prefetchOpt.map({
      case hyper : HyperPrefetchParams =>
        Some( Wire(Vec(banks, DecoupledIO(new PrefetchEvict()(pftParams)))))
      case _ => None
    })
    val prefetchReqsReady = WireInit(VecInit(Seq.fill(banks)(false.B)))
    prefetchOpt.foreach {
      _ =>
        fastArb(prefetchTrains.get, prefetcher.get.io.train, Some("prefetch_train"))
        prefetcher.get.io.req.ready := Cat(prefetchReqsReady).orR
        fastArb(prefetchResps.get, prefetcher.get.io.resp, Some("prefetch_resp"))
        prefetchEvicts.foreach({
          case Some(evict_wire) => 
            fastArb(evict_wire, prefetcher.get.io.evict.get, Some("prefetch_evict"))
          case None =>
        })
    }

    pf_recv_node match {
      case Some(x) =>
        prefetcher.get.io.recv_addr.valid := x.in.head._1.addr_valid
        prefetcher.get.io.recv_addr.bits := x.in.head._1.addr
        prefetcher.get.io_l2_pf_en := x.in.head._1.l2_pf_en
        prefetcher.get.io_l2_pf_ctrl := x.in.head._1.l2_pf_ctrl
      case None =>
        prefetcher.foreach(_.io.recv_addr := 0.U.asTypeOf(ValidIO(UInt(64.W))))
        prefetcher.foreach(_.io_l2_pf_en := false.B)
        prefetcher.foreach(_.io_l2_pf_ctrl := 0.U(2.W))
    }


    spp_send_node match{
      case Some(sender) =>
        sender.out.head._1.addr       := prefetcher.get.io.hint2llc.get.bits.addr
        sender.out.head._1.addr_valid := prefetcher.get.io.hint2llc.get.valid
        sender.out.head._1.needT      := prefetcher.get.io.hint2llc.get.bits.needT
        sender.out.head._1.source     := prefetcher.get.io.hint2llc.get.bits.source
      case None =>
    }
    def restoreAddress(x: UInt, idx: Int) = {
      restoreAddressUInt(x, idx.U)
    }
    def restoreAddressUInt(x: UInt, idx: UInt) = {
      if(bankBits == 0){
        x
      } else {
        val high = x >> offsetBits
        val low = x(offsetBits - 1, 0)
        Cat(high, idx(bankBits - 1, 0), low)
      }
    }
    def bank_eq(set: UInt, bankId: Int, bankBits: Int): Bool = {
      if(bankBits == 0) true.B else set(bankBits - 1, 0) === bankId.U
    }

    def RegNextN[T <: Data](data: T, n: Int): T = {
      if(n == 1)
        RegNext(data)
      else
        RegNextN(data, n - 1)
    }

    val slices = node.in.zip(node.out).zipWithIndex.map {
      case (((in, edgeIn), (out, edgeOut)), i) =>
        require(in.params.dataBits == out.params.dataBits)
        val slice = Module(new Slice(parentName = parentName + s"slice${i}_")(p.alterPartial {
          case EdgeInKey  => edgeIn
          case EdgeOutKey => edgeOut
          case BankBitsKey => bankBits
          case SliceIdKey => i
        }))

        // debug signals
        io.fpga_dbg(i) := RegNext(slice.io.fpga_dbg)

        slice.io.in <> in
        in.b.bits.address := restoreAddress(slice.io.in.b.bits.address, i)
        out <> slice.io.out
        out.a.bits.address := restoreAddress(slice.io.out.a.bits.address, i)
        out.c.bits.address := restoreAddress(slice.io.out.c.bits.address, i)
        slice.io.sliceId := i.U

        slice.io.prefetch.zip(prefetcher).foreach {
          case (s, p) =>
            s.hint2llc match{
              case Some(x) => x := DontCare
              case _ => None
            }
            s.req.valid := p.io.req.valid && bank_eq(p.io.req.bits.set, i, bankBits)
            s.req.bits := p.io.req.bits
            prefetchReqsReady(i) := s.req.ready && bank_eq(p.io.req.bits.set, i, bankBits)
            val train = Pipeline(s.train)
            val resp = Pipeline(s.resp)
            prefetchTrains.get(i) <> train
            prefetchResps.get(i) <> resp
            prefetchEvicts.foreach({
                  case Some(evict_wire) => 
                    val s_evict = Pipeline(s.evict.get)
                    evict_wire(i) <> s_evict
                    if(bankBits != 0){
                      val evict_full_addr = Cat(
                        s_evict.bits.tag, s_evict.bits.set, i.U(bankBits.W), 0.U(offsetBits.W)
                      )
                      val (evict_tag, evict_set, _) = s.parseFullAddress(evict_full_addr)
                      evict_wire(i).bits.tag := evict_tag
                      evict_wire(i).bits.set := evict_set
                    }
                  case None =>
                })
            // restore to full address
            if(bankBits != 0){
              val train_full_addr = Cat(
                train.bits.tag, train.bits.set, i.U(bankBits.W), 0.U(offsetBits.W)
              )
              val (train_tag, train_set, _) = s.parseFullAddress(train_full_addr)
              val resp_full_addr = Cat(
                resp.bits.tag, resp.bits.set, i.U(bankBits.W), 0.U(offsetBits.W)
              )
              val (resp_tag, resp_set, _) = s.parseFullAddress(resp_full_addr)
              prefetchTrains.get(i).bits.tag := train_tag
              prefetchTrains.get(i).bits.set := train_set
              prefetchResps.get(i).bits.tag := resp_tag
              prefetchResps.get(i).bits.set := resp_set
              // prefetchEvicts match {
              //   case Some(evict_wire) => 
              //     val s_evict = Pipeline(s.evict.get)
              //     val evict_full_addr = Cat(
              //       s_evict.bits.tag, s_evict.bits.set, i.U(bankBits.W), 0.U(offsetBits.W)
              //     )
              //     val (evict_tag, evict_set, _) = s.parseFullAddress(evict_full_addr)
              //     evict_wire(i).bits.tag := evict_tag
              //     evict_wire(i).bits.set := evict_set
              //   case None =>
              // }
            }
        }

        slice
    }

    // TODO: config reg for ECC (enable or disable)
    val slicesECC = VecInit(slices.map( s => RegNext(s.io.eccError)))
    val hasECCError = Cat(slicesECC.asUInt).orR
    intNode.out.foreach(int => int._1.foreach(_ := hasECCError))
    intNode.out.foreach(i => dontTouch(i._1))

    private val mbistPl = MBISTPipeline.PlaceMbistPipeline(Int.MaxValue,
      s"${parentName}_mbistPipe",
      cacheParams.hasMbist && cacheParams.hasShareBus
    )

    private val sigFromSrams = if (cacheParams.hasMbist) Some(SRAMTemplate.genBroadCastBundleTop()) else None
    val dft = if (cacheParams.hasMbist) Some(IO(sigFromSrams.get.cloneType)) else None
    if (cacheParams.hasMbist) {
      dft.get <> sigFromSrams.get
      dontTouch(dft.get)
    }

    private val l2MbistIntf = if (cacheParams.hasMbist && cacheParams.hasShareBus) {
      val params = mbistPl.get.nodeParams
      val intf = Some(Module(new MBISTInterface(
        params = Seq(params),
        ids = Seq(mbistPl.get.childrenIds),
        name = s"MBIST_intf_l2",
        pipelineNum = 1
      )))
      intf.get.toPipeline.head <> mbistPl.get.mbist
      if (cacheParams.hartIds.head == 0) mbistPl.get.genCSV(intf.get.info, "MBIST_L2")
      intf.get.mbist := DontCare
      dontTouch(intf.get.mbist)
      //TODO: add mbist controller connections here
      intf
    } else {
      None
    }

    val topDown = topDownOpt.map(_ => Module(new TopDownMonitor()(p.alterPartial {
      case EdgeInKey => node.in.head._2
      case EdgeOutKey => node.out.head._2
      case BankBitsKey => bankBits
    })))
    topDownOpt.foreach {
      _ => {
        topDown.get.io.msStatus.zip(slices).foreach {
          case (in, s) => in := s.io.msStatus.get
        }
        topDown.get.io.dirResult.zip(slices).foreach {
          case (res, s) => res := s.io.dirResult.get
        }
      }
    }

    // debug signals
//    io.fpga_dbg.zip(slices).foreach {
//      case (dbg, s) => dbg := s.io.fpga_dbg
//    }
//    io.fpga_dbg := DontCare

    if(cacheParams.enablePerf) {
      val grant_fire = slices.map{ slice => {
                          val (_, _, grant_fire_last, _) = node.in.head._2.count(slice.io.in.d)
                          slice.io.in.d.fire && grant_fire_last && slice.io.in.d.bits.opcode === GrantData
                        }}
      XSPerfAccumulate("grant_data_fire", PopCount(VecInit(grant_fire)))
    }

    // TODO: perfEvents
    val allPerfEvents = slices.flatMap(_.getPerfEvents)
    for (((name, inc), i) <- allPerfEvents.zipWithIndex) {
      println(cacheParams.name+" perfEvents Set ", name, inc, i)
    }
    println(cacheParams.name+" perfEvents All: "+cacheParams.getPCntAll)
    val perfEvents = allPerfEvents
    generatePerfEvent()

    val prefetcherSeq = if(prefetcher.isDefined) Seq(ModuleNode(prefetcher.get)) else Seq()
    val mbistSeq = if(mbistPl.isDefined) Seq(ModuleNode(mbistPl.get)) else Seq()
    private val resetTree = ResetGenNode(
      slices.map(s => ResetGenNode(Seq(ModuleNode(s)))) ++ prefetcherSeq ++ mbistSeq
    )
    ResetGen(resetTree, reset, Some(io.dfx_reset), !p(DebugOptionsKey).FPGAPlatform)
  }
}
