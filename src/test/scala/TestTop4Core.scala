package coupledL2
import axi2tl.{AXI2TL, AXI2TLFragmenter, AXI2TLParam, AXI2TLParamKey}
import circt.stage.{ChiselStage, FirtoolOption}
import chisel3._
import chisel3.util._
import org.chipsalliance.cde.config._
import chisel3.stage.ChiselGeneratorAnnotation
import freechips.rocketchip.diplomacy._
import freechips.rocketchip.tilelink._
import freechips.rocketchip.interrupts.{IntSinkNode, IntSinkPortSimple}
import freechips.rocketchip.interrupts.{IntSourceNode, IntSourcePortSimple}
import coupledL2.prefetch._
import coupledL2.utils.HasPerfEvents
import freechips.rocketchip.amba.axi4.{AXI4MasterNode, AXI4MasterParameters, AXI4MasterPortParameters}
import huancun.{CacheCtrl, CacheParameters, HCCacheParameters, HCCacheParamsKey, HuanCun}
import xs.utils.GTimer
import xs.utils.perf.{DebugOptions, DebugOptionsKey}
import utils.{TLClientsMerger}


class TestTop_fullSys_4Core()(implicit p: Parameters) extends LazyModule {
  val delayFactor = 0.2
  val cacheParams = p(L2ParamKey)

  val NumCores = 4
  val nrL2 = NumCores

  val L2NBanks = 2
  val L3NBanks = 4
  val L2BlockSize = 64
  val L3BlockSize = 64

  def createDCacheNode(name: String, sources: Int) = {
    val masterNode = TLClientNode(Seq(
      TLMasterPortParameters.v2(
        masters = Seq(
          TLMasterParameters.v1(
            name = name,
            sourceId = IdRange(0, sources),
            supportsProbe = TransferSizes(cacheParams.blockBytes)
          )
        ),
        channelBytes = TLChannelBeatBytes(cacheParams.blockBytes),
        minLatency = 1,
        echoFields = Nil,
        requestFields = Seq(AliasField(2)),
        responseKeys = cacheParams.respKey
      )
    ))
    masterNode
  }

  def createICacheNode(name: String, source: Int) = {
    val masterNode = TLClientNode(Seq(
      TLMasterPortParameters.v1(
        clients = Seq(TLMasterParameters.v1(
          name = name,
          sourceId = IdRange(0, source)
        ))
      )
    ))
    masterNode
  }

  var master_nodes: Seq[TLClientNode] = Seq()
  var l1xbars: Seq[TLNode] = Seq()
  val l2xbar: TLNode = TLXbar()

  var l2binders: Seq[TLNode] = Seq()
  val l3binder = BankBinder(L3NBanks, L3BlockSize)

  val mem_xbar = TLXbar()
  // val ram = LazyModule(new TLRAM(AddressSet(0, 0xffffffffL), beatBytes = 32)) // Normal rtl-based memory
  val ram = LazyModule(new coupledL2.TLRAM(AddressSet(0, 0xffffffffffL), beatBytes = 32)) // DPI-C memory

  // Create L1 nodes
  (0 until nrL2).foreach{ i =>
    val dcache_idMax = 35
    val icache_idMax = 13
    val l1d = createDCacheNode(s"l1d$i", dcache_idMax)
    val l1i = createICacheNode(s"l1i$i", icache_idMax)
    master_nodes = master_nodes ++ Seq(l1d, l1i)

    val xbar = TLXbar()
    l1xbars = l1xbars ++ Seq(xbar)
    xbar := TLBuffer() := l1i
    xbar := TLBuffer() := l1d
  }

  // Create L2 nodes
  val l2List = (0 until nrL2).map{i =>
    val l2 = LazyModule(new CoupledL2()(new Config((_, _, _) => {
      case L2ParamKey => L2Param(
        name = s"l2$i",
        ways = 8,
        sets = 256,
        clientCaches = Seq(L1Param(aliasBitsOpt = Some(2))),
        echoField = Seq(huancun.DirtyField()),
        // prefetch = Some(BOPParameters(rrTableEntries = 16,rrTagBits = 6))
        prefetch = Some(coupledL2.prefetch.HyperPrefetchParams()), // Some(HyperPrefetchParams()),
        /* del L2 prefetche recv option, move into: prefetch =  PrefetchReceiverParams
        prefetch options:
          SPPParameters          => spp only
          BOPParameters          => bop only
          PrefetchReceiverParams => sms+bop
          HyperPrefetchParams    => spp+bop+sms
        */
        // sppMultiLevelRefill = None, // Some(coupledL2.prefetch.PrefetchReceiverParams()),
        /*must has spp, otherwise Assert Fail
        sppMultiLevelRefill options:
        PrefetchReceiverParams() => spp has cross level refill
        None                     => spp only refill L2 
        */
        elaboratedTopDown = false,
      )
      case DebugOptionsKey => DebugOptions()
    })))
    
    val binder = BankBinder(L2NBanks, L2BlockSize)
    l2binders = l2binders ++ Seq(binder)
    l2.pf_recv_node match {
      case Some(l2Recv) =>
        val l1_sms_send_0_node = LazyModule(new PrefetchSmsOuterNode)
        l2Recv := l1_sms_send_0_node.outNode
      case None =>
    }
    l2xbar := TLBuffer.chainNode(2) := TLClientsMerger() := TLXbar() :=* binder :*= l2.node :*= l1xbars(i)

    l2
  }

  // Create L3 node
  val l3 = LazyModule(new HuanCun()(new Config((_, _, _) => {
    case HCCacheParamsKey => HCCacheParameters(
      name = "L3",
      level = 3,
      ways = 4,
      sets = 2048,
      inclusive = false,
      clientCaches = Seq(CacheParameters(sets = 32, ways = 4, blockGranularity = log2Ceil(32), name = "L2")),
      sramClkDivBy2 = true,
      sramDepthDiv = 8,
      dataBytes = 8,
      simulation = true,
      hasMbist = false,
      prefetch = None,
      prefetchRecv = None, // Some(huancun.prefetch.PrefetchReceiverParams()), // None, //Some(huancun.prefetch.PrefetchReceiverParams()),
      tagECC = Some("secded"),
      dataECC = Some("secded"),
      ctrl = Some(huancun.CacheCtrl(
//        address = 0x3900_0000
        address = 0x3900_0000
      ))
    )
    case DebugOptionsKey => DebugOptions()
  })))

  // println(f"pf_l3recv_node connecting to l3pf_RecvXbar out")
  // val sppHasCrossLevelRefillOpt = p(L2ParamKey).sppMultiLevelRefill
  // println(f"SPP cross level refill: ${sppHasCrossLevelRefillOpt} ")
  // sppHasCrossLevelRefillOpt match{
  //   case Some(x) =>
  //     val l3pf_RecvXbar = LazyModule(new PrefetchReceiverXbar(NumCores))
  //     l2List.zipWithIndex.foreach {
  //       case (l2, i) =>
  //         l2.spp_send_node match {
  //           case Some(l2Send) =>
  //             l3pf_RecvXbar.inNode(i) := l2Send
  //             println(f"spp_send_node${i} connecting to l3pf_RecvXbar")
  //           case None =>
  //       }
  //     }
  //     println(f"pf_l3recv_node connecting to l3pf_RecvXbar out")
  //     l3.pf_l3recv_node.map(l3_recv =>  l3_recv:= l3pf_RecvXbar.outNode.head)
  //   case None =>
  // }
  val ctrl_node = TLClientNode(Seq(TLMasterPortParameters.v2(
      Seq(TLMasterParameters.v1(
        name = "ctrl",
        sourceId = IdRange(0, 16),
        supportsProbe = TransferSizes.none
      )),
      channelBytes = TLChannelBeatBytes(8), // 64bits
      minLatency = 1,
      echoFields = Nil,
    )))
  
  val l3_ecc_int_sink = IntSinkNode(IntSinkPortSimple(1, 1))
  l3.ctlnode.foreach(_ := TLBuffer() := ctrl_node)
  l3.intnode.foreach(l3_ecc_int_sink := _)

  val l2_ecc_int_sinks = Seq.fill(nrL2)(IntSinkNode(IntSinkPortSimple(1, 1)))
  l2List.map(_.intNode).zip(l2_ecc_int_sinks).foreach{ 
    case(source, sink) => sink := source
  }

  val idBits = 13
  val l3FrontendAXI4Node = AXI4MasterNode(Seq(AXI4MasterPortParameters(
    Seq(AXI4MasterParameters(
      name = "dma",
      id = IdRange(0, 1 << idBits),
      maxFlight = Some(16)
    ))
  )))
  l2xbar := TLBuffer() := AXI2TL(16, 16) := AXI2TLFragmenter() := l3FrontendAXI4Node

  ram.node :=
    mem_xbar :=*
    TLXbar() :=*
    TLFragmenter(32, 64) :=*
    TLBuffer.chainNode(2) :=*
    TLCacheCork() :=*
    // TLDelayer(delayFactor) :=*
    l3binder :*=
    l3.node :*=
    l2xbar

  lazy val module = new LazyModuleImp(this) with HasPerfEvents{
    master_nodes.zipWithIndex.foreach {
      case (node, i) =>
        node.makeIOs()(ValName(s"master_port_$i"))
    }
    l3FrontendAXI4Node.makeIOs()(ValName("dma_port"))
    ctrl_node.makeIOs()(ValName("cmo_port"))
    l3_ecc_int_sink.makeIOs()(ValName("l3_int_port"))

    l2_ecc_int_sinks.zipWithIndex.foreach{ case(sink, i) => sink.makeIOs()(ValName("l2_int_port_"+i))}

    val io = IO(new Bundle{
      val perfClean = Input(Bool())
      val perfDump = Input(Bool())
    })

    l2List.foreach(_.module.io.dfx_reset.scan_mode := false.B)
    l2List.foreach(_.module.io.dfx_reset.lgc_rst_n := true.B.asAsyncReset)
    l2List.foreach(_.module.io.dfx_reset.mode := false.B)
    
    val logTimestamp = WireInit(0.U(64.W))
    val perfClean = WireInit(false.B)
    val perfDump = WireInit(false.B)
  
    perfClean := io.perfClean
    perfDump := io.perfDump
  
    val timer = GTimer()

    logTimestamp := timer

    val perfEvents = (l2List.map(_.module)).flatMap(_.getPerfEvents)
    generatePerfEvent()
  }
}


object TestTop_fullSys_4Core extends App {
  val config = new Config((_, _, _) => {
    case L2ParamKey => L2Param(
      clientCaches = Seq(L1Param(aliasBitsOpt = Some(2))),
      echoField = Seq(DirtyField()),
      // prefetch = Some(BOPParameters(rrTableEntries = 16,rrTagBits = 6))
      prefetch = Some(HyperPrefetchParams()), /*
      del L2 prefetche recv option, move into: prefetch =  PrefetchReceiverParams
      prefetch options:
        SPPParameters          => spp only
        BOPParameters          => bop only
        PrefetchReceiverParams => sms+bop
        HyperPrefetchParams    => spp+bop+sms
      */
      sppMultiLevelRefill = Some(coupledL2.prefetch.PrefetchReceiverParams()),
      /*must has spp, otherwise Assert Fail
      sppMultiLevelRefill options:
      PrefetchReceiverParams() => spp has cross level refill
      None                     => spp only refill L2
      */
    )
    case HCCacheParamsKey => HCCacheParameters(
      echoField = Seq(DirtyField())
    )
    case DebugOptionsKey => DebugOptions()
    case AXI2TLParamKey => AXI2TLParam()
  })
  val top = DisableMonitors(p => LazyModule(new TestTop_fullSys_4Core()(p)))(config)

  (new ChiselStage).execute(Array("--target", "verilog") ++ args, Seq(
    FirtoolOption("-O=release"),
    FirtoolOption("--disable-all-randomization"),
    FirtoolOption("--disable-annotation-unknown"),
    FirtoolOption("--strip-debug-info"),
    FirtoolOption("--lower-memories"),
    FirtoolOption("--lowering-options=noAlwaysComb," +
      " disallowPortDeclSharing, disallowLocalVariables," +
      " emittedLineLength=120, explicitBitcast, locationInfoStyle=plain," +
      " disallowExpressionInliningInPorts, disallowMuxInlining"),
    ChiselGeneratorAnnotation(() => top.module),
  ))
}
