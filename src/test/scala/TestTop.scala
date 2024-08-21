package coupledL2
import circt.stage.{ChiselStage, FirtoolOption}
import chisel3._
import chisel3.util._
import org.chipsalliance.cde.config._
import chisel3.stage.ChiselGeneratorAnnotation
import freechips.rocketchip.diplomacy._
import freechips.rocketchip.tilelink._
import freechips.rocketchip.devices.tilelink.{TLError, DevNullParams}
import coupledL2.prefetch._
import xs.utils.{ChiselDB, FileRegisters}
import axi2tl._
import freechips.rocketchip.amba.axi4._
import freechips.rocketchip.interrupts.{IntSinkNode, IntSinkPortSimple}
import freechips.rocketchip.interrupts.{IntSourceNode, IntSourcePortSimple}
import chisel3.util.experimental.BoringUtils
import scala.collection.mutable.ArrayBuffer
import xs.utils.GTimer
import xs.utils.DFTResetSignals
import xs.utils.perf.{DebugOptions,DebugOptionsKey}
import huancun.{HuanCun, HCCacheParameters, HCCacheParamsKey, CacheParameters, CacheCtrl}
import coupledL2.utils.HasPerfEvents

class TestTop_L2()(implicit p: Parameters) extends LazyModule {

  /*   L1D
   *    | 
   *   L2
   */

  val delayFactor = 0.5
  val cacheParams = p(L2ParamKey)

  def createClientNode(name: String, sources: Int) = {
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

  val l1d_nodes = (0 until 1) map( i => createClientNode(s"l1d$i", 32))
  val master_nodes = l1d_nodes

  val l2 = LazyModule(new CoupledL2())
  val xbar = TLXbar()
  val ram = LazyModule(new TLRAM(AddressSet(0, 0xffffL), beatBytes = 32))

  for (l1d <- l1d_nodes) {
    xbar := TLBuffer() := l1d
  }

  ram.node :=
    TLXbar() :=*
      TLFragmenter(32, 64) :=*
      TLCacheCork() :=*
      TLDelayer(delayFactor) :=*
      l2.node :=* xbar

  lazy val module = new LazyModuleImp(this){
    master_nodes.zipWithIndex.foreach{
      case (node, i) =>
        node.makeIOs()(ValName(s"master_port_$i"))
    }
  }

}

class TestTop_L2L3()(implicit p: Parameters) extends LazyModule {
  /* L1I    L1D
   *   \    /
   *     L2
   *      |
   *     L3
   */
  val delayFactor = 0.2
  val cacheParams = p(L2ParamKey)

  def createClientNode(name: String, sources: Int) = {
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
        requestFields = Seq(AliasField(2), PrefetchField()),
        responseKeys = cacheParams.respKey
      )
    ))
    masterNode
  }

  val l1d = createClientNode(s"l1d", 32)
  val l1i = TLClientNode(Seq(
    TLMasterPortParameters.v1(
      clients = Seq(TLMasterParameters.v1(
        name = s"l1i",
        sourceId = IdRange(0, 32)
      ))
    )
  ))
  val master_nodes = Seq(l1d, l1i)

  val l2 = LazyModule(new CoupledL2()(new Config((_, _, _) => {
    case L2ParamKey => L2Param(
      name = s"l2",
      ways = 4,
      sets = 128,
      clientCaches = Seq(L1Param(aliasBitsOpt = Some(2))),
      echoField = Seq(DirtyField()),
      prefetch = Some(BOPParameters(
        rrTableEntries = 16,
        rrTagBits = 6
      ))
    )
  }))).node

  val l3 = LazyModule(new HuanCun()(new Config((_, _, _) => {
    case HCCacheParamsKey => HCCacheParameters(
      name = "l3",
      level = 3,
      ways = 4,
      sets = 128,
      inclusive = false,
      clientCaches = Seq(
        CacheParameters(
          name = s"l2",
          sets = 128,
          ways = 4,
          blockGranularity = log2Ceil(128)
        ),
      ),
      echoField = Seq(DirtyField()),
      simulation = true
    )
  })))

  val xbar = TLXbar()
  val ram = LazyModule(new TLRAM(AddressSet(0, 0xffffL), beatBytes = 32))

  xbar := TLBuffer() := l1i
  xbar := TLBuffer() := l1d

  ram.node :=
    TLXbar() :=*
    TLFragmenter(32, 64) :=*
    TLCacheCork() :=*
    TLDelayer(delayFactor) :=*
    l3.node :=*
    TLBuffer() :=
    l2 :=* xbar

  lazy val module = new LazyModuleImp(this) {
    master_nodes.zipWithIndex.foreach {
      case (node, i) =>
        node.makeIOs()(ValName(s"master_port_$i"))
    }
  }

}

class TestTop_L2_Standalone()(implicit p: Parameters) extends LazyModule {

  /* L1D   L1D (fake)
   *  \    /
   *    L2
   *    |
   *    L3 (fake, used for tl-test with salve)
   */

  val delayFactor = 0.5
  val cacheParams = p(L2ParamKey)

  def createClientNode(name: String, sources: Int) = {
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
        echoFields = cacheParams.echoField,
        requestFields = Seq(AliasField(2)),
        responseKeys = cacheParams.respKey
      )
    ))
    masterNode
  }

  def createManagerNode(name: String, sources: Int) = {
    val xfer = TransferSizes(cacheParams.blockBytes, cacheParams.blockBytes)
    val slaveNode = TLManagerNode(Seq(
      TLSlavePortParameters.v1(Seq(
        TLSlaveParameters.v1(
          address          = Seq(AddressSet(0, 0xffffL)),
          regionType       = RegionType.CACHED,
          executable       = true,
          supportsAcquireT = xfer,
          supportsAcquireB = xfer,
          fifoId           = None
        )),
        beatBytes = 32,
        minLatency = 2,
        responseFields = cacheParams.respField,
        requestKeys = cacheParams.reqKey,
        endSinkId = sources
      ))
    )
    slaveNode
  }

  val l1d_nodes = (0 until 1) map( i => createClientNode(s"l1d$i", 32))
  val master_nodes = l1d_nodes

  val l2 = LazyModule(new CoupledL2())
  val xbar = TLXbar()
  val l3 = createManagerNode("Fake_L3", 16)

  for(i <- 0 until 1) {
    xbar :=* TLBuffer() := l1d_nodes(i)
  }

  l3 :=
    TLBuffer() :=
    TLXbar() :=*
      TLDelayer(delayFactor) :=*
      l2.node :=* xbar

  lazy val module = new LazyModuleImp(this){
    master_nodes.zipWithIndex.foreach{
      case (node, i) =>
        node.makeIOs()(ValName(s"master_port_$i"))
    }
    l3.makeIOs()(ValName(s"slave_port"))
  }

}

class TestTop_L2L3L2()(implicit p: Parameters) extends LazyModule {

  /* L1D   L1D
   *  |     |
   * L2    L2
   *  \    /
   *    L3
   */

  val delayFactor = 0.2
  val cacheParams = p(L2ParamKey)

  val nrL2 = 2

  def createClientNode(name: String, sources: Int) = {
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

  val l1d_nodes = (0 until nrL2).map(i => createClientNode(s"l1d$i", 32))
  val master_nodes = l1d_nodes

  val l2_nodes = (0 until nrL2).map(i => LazyModule(new CoupledL2()(new Config((_, _, _) => {
    case L2ParamKey => L2Param(
      name = s"l2$i",
      ways = 4,
      sets = 128,
      clientCaches = Seq(L1Param(aliasBitsOpt = Some(2))),
      echoField = Seq(DirtyField())
    )
  }))).node)

  val l3 = LazyModule(new HuanCun()(new Config((_, _, _) => {
    case HCCacheParamsKey => HCCacheParameters(
      name = "L3",
      level = 3,
      ways = 4,
      sets = 128,
      inclusive = false,
      clientCaches = (0 until nrL2).map(i =>
        CacheParameters(
          name = s"l2",
          sets = 128,
          ways = 4,
          blockGranularity = log2Ceil(128)
        ),
      ),
      echoField = Seq(DirtyField()),
      simulation = true
    )
  })))

  val xbar = TLXbar()
  val ram = LazyModule(new TLRAM(AddressSet(0, 0xffffL), beatBytes = 32))

  l1d_nodes.zip(l2_nodes).map {
    case (l1d, l2) => l2 := TLBuffer() := l1d
  }

  for (l2 <- l2_nodes) {
    xbar := TLBuffer() := l2
  }

  ram.node :=
    TLXbar() :=*
      TLFragmenter(32, 64) :=*
      TLCacheCork() :=*
      TLDelayer(delayFactor) :=*
      l3.node :=* xbar

  lazy val module = new LazyModuleImp(this) {
    master_nodes.zipWithIndex.foreach {
      case (node, i) =>
        node.makeIOs()(ValName(s"master_port_$i"))
    }
  }
}

// class TestTop_fullSys()(implicit p: Parameters) extends LazyModule {

//   /* L1D L1I L1D L1I (L1I sends Get)
//    *  \  /    \  /
//    *   L2      L2
//    *    \     /
//    *       L3
//    */

//   val delayFactor = 0.2
//   val cacheParams = p(L2ParamKey)

//   val nrL2 = 2

//   def createClientNode(name: String, sources: Int) = {
//     val masterNode = TLClientNode(Seq(
//       TLMasterPortParameters.v2(
//         masters = Seq(
//           TLMasterParameters.v1(
//             name = name,
//             sourceId = IdRange(0, sources),
//             supportsProbe = TransferSizes(cacheParams.blockBytes)
//           )
//         ),
//         channelBytes = TLChannelBeatBytes(cacheParams.blockBytes),
//         minLatency = 1,
//         echoFields = Nil,
//         requestFields = Seq(AliasField(2)),
//         responseKeys = cacheParams.respKey
//       )
//     ))
//     masterNode
//   }

//   val l2xbar = TLXbar()
//   val ram = LazyModule(new TLRAM(AddressSet(0, 0xffffL), beatBytes = 32))
//   var master_nodes: Seq[TLClientNode] = Seq() // TODO

//   (0 until nrL2).map{i =>
//     val l1d = createClientNode(s"l1d$i", 32)
//     val l1i = TLClientNode(Seq(
//       TLMasterPortParameters.v1(
//         clients = Seq(TLMasterParameters.v1(
//           name = s"l1i$i",
//           sourceId = IdRange(0, 32)
//         ))
//       )
//     ))
//     master_nodes = master_nodes ++ Seq(l1d, l1i) // TODO

//     val l1xbar = TLXbar()
//     val l2node = LazyModule(new CoupledL2()(new Config((_, _, _) => {
//       case L2ParamKey => L2Param(
//         name = s"l2$i",
//         ways = 4,
//         sets = 128,
//         clientCaches = Seq(L1Param(aliasBitsOpt = Some(2))),
//         echoField = Seq(DirtyField()),
//         prefetch = Some(BOPParameters(
//           rrTableEntries = 16,
//           rrTagBits = 6
//         ))
//       )
//     }))).node

//     l1xbar := TLBuffer() := l1i
//     l1xbar := TLBuffer() := l1d

//     l2xbar := TLBuffer() := l2node := l1xbar
//   }

//   val l3 = LazyModule(new HuanCun()(new Config((_, _, _) => {
//     case HCCacheParamsKey => HCCacheParameters(
//       name = "L3",
//       level = 3,
//       ways = 4,
//       sets = 128,
//       inclusive = false,
//       clientCaches = (0 until nrL2).map(i =>
//         CacheParameters(
//           name = s"l2",
//           sets = 128,
//           ways = 4,
//           blockGranularity = log2Ceil(128)
//         ),
//       ),
//       echoField = Seq(DirtyField()),
//       simulation = true
//     )
//   })))

//   ram.node :=
//     TLXbar() :=*
//       TLFragmenter(32, 64) :=*
//       TLCacheCork() :=*
//       TLDelayer(delayFactor) :=*
//       l3.node :=* l2xbar

//   lazy val module = new LazyModuleImp(this) {
//     master_nodes.zipWithIndex.foreach {
//       case (node, i) =>
//         node.makeIOs()(ValName(s"master_port_$i"))
//     }
//   }
// }

class TestTop_fullSys()(implicit p: Parameters) extends LazyModule {

  /* L1D L1I L1D L1I (L1I sends Get)
   *  \  /    \  /
   *   L2      L2    DMA(AXItoTL)
   *    \     /     /       
   *         L3
   */

  val delayFactor = 0.2
  val cacheParams = p(L2ParamKey)

  val nrL2 = 2

  def createClientNode(name: String, sources: Int) = {
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

  val l2xbar = TLXbar()
  // val ram = LazyModule(new TLRAM(AddressSet(0, 0xffffffffL), beatBytes = 32)) // Normal rtl-based memory
  // val ram = LazyModule(new coupledL2.TLRAM(AddressSet(0, 0xffffffffffffL), beatBytes = 32)) // DPI-C memory

  var master_nodes: Seq[TLClientNode] = Seq() // TODO
  val NumCores=2
  // val nullNode = LazyModule(new SppSenderNull)
  val l2List = (0 until nrL2).map{i =>
    val l1d = createClientNode(s"l1d$i", 32)
    val l1i = TLClientNode(Seq(
      TLMasterPortParameters.v1(
        clients = Seq(TLMasterParameters.v1(
          name = s"l1i$i",
          sourceId = IdRange(0, 32)
        ))
      )
    ))
    master_nodes = master_nodes ++ Seq(l1d, l1i) // TODO

    val l1xbar = TLXbar()
    val l2 = LazyModule(new CoupledL2()(new Config((_, _, _) => {
      case L2ParamKey => L2Param(
        name = s"l2$i",
        ways = 4,
        sets = 32,
        // ways = 8,
        // sets = 256,
        clientCaches = Seq(L1Param(aliasBitsOpt = Some(2))),
        echoField = Seq(huancun.DirtyField()),
        // prefetch = Some(BOPParameters(rrTableEntries = 16,rrTagBits = 6))
        prefetch = Some(HyperPrefetchParams()),
        /* del L2 prefetche recv option, move into: prefetch =  PrefetchReceiverParams
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
      case DebugOptionsKey => DebugOptions()
    })))
    l1xbar := TLBuffer() := l1i
    l1xbar := TLBuffer() := l1d
    l2.pf_recv_node match{
      case Some(l2Recv) => 
        val l1_sms_send_0_node = LazyModule(new PrefetchSmsOuterNode)
        l2Recv := l1_sms_send_0_node.outNode
      case None =>
    }
    l2xbar := TLBuffer() := l2.node := l1xbar
    l2 // return l2 list
  }

  val l3 = LazyModule(new HuanCun()(new Config((_, _, _) => {
    case HCCacheParamsKey => HCCacheParameters(
      name = "L3",
      level = 3,
      ways = 4,
      sets = 64,
      // sets = 2048,
      inclusive = false,
      clientCaches = Seq(CacheParameters(sets = 32, ways = 4, blockGranularity = log2Ceil(32), name = "L2")),
      sramClkDivBy2 = true,
      sramDepthDiv = 4,
      dataBytes = 8,
      simulation = true,
      hasMbist = false,
      prefetch = None,
      prefetchRecv = Some(huancun.prefetch.PrefetchReceiverParams()), // None, //Some(huancun.prefetch.PrefetchReceiverParams()),
      tagECC = Some("secded"),
      dataECC = Some("secded"),
      ctrl = Some(huancun.CacheCtrl(
//        address = 0x3900_0000
        address = 0x390_0000
      ))
    )
    case DebugOptionsKey => DebugOptions()
  })))

  println(f"pf_l3recv_node connecting to l3pf_RecvXbar out")
  val sppHasCrossLevelRefillOpt = p(L2ParamKey).sppMultiLevelRefill
  println(f"SPP cross level refill: ${sppHasCrossLevelRefillOpt} ")
  sppHasCrossLevelRefillOpt match{
    case Some(x) =>
      val l3pf_RecvXbar = LazyModule(new PrefetchReceiverXbar(NumCores))
      l2List.zipWithIndex.foreach {
        case (l2, i) =>
          l2.spp_send_node match {
            case Some(l2Send) =>
              l3pf_RecvXbar.inNode(i) := l2Send
              println(f"spp_send_node${i} connecting to l3pf_RecvXbar")
            case None =>
        }
      }
      println(f"pf_l3recv_node connecting to l3pf_RecvXbar out")
      l3.pf_l3recv_node.map(l3_recv =>  l3_recv:= l3pf_RecvXbar.outNode.head)
    case None =>
  }
  val ctrl_node = TLClientNode(Seq(TLMasterPortParameters.v2(
      Seq(TLMasterParameters.v1(
        name = "ctrl",
        sourceId = IdRange(0, 64),
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

  val idBits = 14
  val l3FrontendAXI4Node = AXI4MasterNode(Seq(AXI4MasterPortParameters(
    Seq(AXI4MasterParameters(
      name = "dma",
      id = IdRange(0, 1 << idBits),
      maxFlight = Some(16)
    ))
  )))
 l2xbar := TLBuffer() := AXI2TL(16, 16) := AXI2TLFragmenter() := l3FrontendAXI4Node
  // l2xbar :=
  // TLFIFOFixer() :=
  // TLWidthWidget(32) :=
  // TLBuffer() :=
  // AXI4ToTL() :=
  // AXI4Buffer() :=
  // AXI4UserYanker(Some(16)) :=
  // AXI4Fragmenter() :=
  // AXI4Buffer() :=
  // AXI4Buffer() :=
  // AXI4IdIndexer(4) :=
  // l3FrontendAXI4Node

  // has DRAMsim3 (AXI4 RAM)
  val mem_xbar = TLXbar()
  mem_xbar :=*
    TLXbar() :=*
    TLBuffer.chainNode(2) :=*
    TLCacheCork() :=*
    TLDelayer(delayFactor) :=*
    l3.node :=
    l2xbar
  
  val PAddrBits = 37
  val L3OuterBusWidth = 256
  val L2BlockSize = 64
  val L3BlockSize = 64

  val memAddrMask = (1L << PAddrBits) - 1L
  val memRange = AddressSet(0x00000000L, memAddrMask).subtract(AddressSet(0x00000000L, 0x7FFFFFFFL))

  val ram = LazyModule(new AXI4Memory(
    address = memRange, 
    memByte = 16L * 1024 * 1024 * 1024, 
    useBlackBox = true, 
    executable = true,
    beatBytes = L3OuterBusWidth / 8,
    burstLen = L3BlockSize / (L3OuterBusWidth / 8)
  ))

  ram.node :=
    AXI4Buffer() :=
    AXI4Buffer() :=
    AXI4Buffer() :=
    AXI4IdIndexer(idBits = 14) :=
    AXI4UserYanker() :=
    AXI4Deinterleaver(L3BlockSize) :=
    TLToAXI4() :=
    TLSourceShrinker(64) :=
    TLWidthWidget(L3OuterBusWidth / 8) :=
    TLBuffer.chainNode(2) :=
    mem_xbar

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

class TestTop_L3()(implicit p: Parameters) extends LazyModule {

  /*   L2  L2(fake)
   *    \ /
   *     L3
   */

  val delayFactor = 0.5
  val cacheParams = p(L2ParamKey)

  val NumCores = 2
  val nrL2 = NumCores

  val l3Set = 32
  val l3Way = 4
  val l3ClientSet = 32
  val l3ClientWay = 4

  // val L2NBanks = 2
  // val L3NBanks = 4
  val L2BlockSize = 64
  val L3BlockSize = 64

  def createClientNode(name: String, sources: Int) = {
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

  val fake_l2_nodes = (0 until nrL2) map( i => createClientNode(s"l2$i", 32))
  val master_nodes = fake_l2_nodes

  val l3 = LazyModule(new HuanCun()(new Config((_, _, _) => {
    case HCCacheParamsKey => HCCacheParameters(
      name = "L3",
      level = 3,
      ways = l3Way,
      sets = l3Set,
      inclusive = false,
      clientCaches = Seq(CacheParameters(sets = l3ClientSet, ways = l3ClientWay, blockGranularity = log2Ceil(32), name = "L2")),
      sramClkDivBy2 = true,
      sramDepthDiv = 4,
      dataBytes = 8,
      simulation = true,
      hasMbist = false,
      prefetch = None,
      prefetchRecv = None,
      tagECC = Some("secded"),
      dataECC = Some("secded"),
      ctrl = Some(huancun.CacheCtrl(address = 0x390_0000))
    )
    case DebugOptionsKey => DebugOptions()
  })))

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

  val l2xbar = TLXbar()
  val PAddrBits = 37
  val L3OuterBusWidth = 256
  val memAddrMask = (1L << PAddrBits) - 1L
  val memRange = AddressSet(0x00000000L, memAddrMask).subtract(AddressSet(0x00000000L, 0x7FFFFFFFL))

  // has DRAMsim3 (AXI4 RAM)
  val ram = LazyModule(new AXI4Memory(
    address = memRange, 
    memByte = 128L * 1024 * 1024 * 1024, 
    useBlackBox = true, 
    executable = true,
    beatBytes = L3OuterBusWidth / 8,
    burstLen = L3BlockSize / (L3OuterBusWidth / 8)
  ))


  for (l2 <- fake_l2_nodes) {
    l2xbar := TLBuffer() := l2
  }

  ram.node :=
    AXI4Buffer() :=
    AXI4Buffer() :=
    AXI4Buffer() :=
    AXI4IdIndexer(idBits = 14) :=
    AXI4UserYanker() :=
    AXI4Deinterleaver(L3BlockSize) :=
    TLToAXI4() :=
    TLSourceShrinker(64) :=
    TLWidthWidget(L3OuterBusWidth / 8) :=
    TLBuffer.chainNode(2) :=
      TLXbar() :=*
      // TLFragmenter(32, 64) :=*
      TLCacheCork() :=*
      TLDelayer(delayFactor) :=*
      l3.node :=* 
        l2xbar

  lazy val module = new LazyModuleImp(this){
    master_nodes.zipWithIndex.foreach{
      case (node, i) =>
        node.makeIOs()(ValName(s"master_port_$i"))
    }
    ctrl_node.makeIOs()(ValName("cmo_port"))
    l3_ecc_int_sink.makeIOs()(ValName("l3_int_port"))
  }
}

object TestTop_L2 extends App {
  val config = new Config((_, _, _) => {
    case L2ParamKey => L2Param(
      clientCaches = Seq(L1Param(aliasBitsOpt = Some(2))),
      echoField = Seq(DirtyField())
    )
    case DebugOptionsKey => DebugOptions()
  })
  val top = DisableMonitors(p => LazyModule(new TestTop_L2()(p)) )(config)

  (new ChiselStage).execute(Array("--target", "verilog") ++ args, Seq(
    ChiselGeneratorAnnotation(() => top.module),
    FirtoolOption("--disable-annotation-unknown")
  ))

  ChiselDB.init(false)
  ChiselDB.addToFileRegisters
  FileRegisters.write("./build")
}

object TestTop_L2_Standalone extends App {
  val config = new Config((_, _, _) => {
    case L2ParamKey => L2Param(
      clientCaches = Seq(L1Param(aliasBitsOpt = Some(2))),
      echoField = Seq(DirtyField()),
      enablePerf = false
    )
    case DebugOptionsKey => DebugOptions()
  })
  val top = DisableMonitors(p => LazyModule(new TestTop_L2_Standalone()(p)) )(config)

  (new ChiselStage).execute(Array("--target", "verilog") ++ args, Seq(
    ChiselGeneratorAnnotation(() => top.module),
    FirtoolOption("--disable-annotation-unknown")
  ))

  ChiselDB.init(false)
  ChiselDB.addToFileRegisters
  FileRegisters.write("./build")
}

object TestTop_L2L3 extends App {
  val config = new Config((_, _, _) => {
    case L2ParamKey => L2Param(
      clientCaches = Seq(L1Param(aliasBitsOpt = Some(2))),
      echoField = Seq(DirtyField())
    )
    case HCCacheParamsKey => HCCacheParameters(
      echoField = Seq(DirtyField())
    )
    case DebugOptionsKey => DebugOptions()
  })
  val top = DisableMonitors(p => LazyModule(new TestTop_L2L3()(p)) )(config)

  (new ChiselStage).execute(Array("--target", "verilog") ++ args, Seq(
    ChiselGeneratorAnnotation(() => top.module),
    FirtoolOption("--disable-annotation-unknown")
  ))

  ChiselDB.init(false)
  ChiselDB.addToFileRegisters
  FileRegisters.write("./build")
}

object TestTop_L2L3L2 extends App {
  val config = new Config((_, _, _) => {
    case L2ParamKey => L2Param(
      clientCaches = Seq(L1Param(aliasBitsOpt = Some(2))),
     // echoField = Seq(DirtyField())
    )
    case HCCacheParamsKey => HCCacheParameters(
      echoField = Seq(DirtyField())
    )
  })
  val top = DisableMonitors(p => LazyModule(new TestTop_L2L3L2()(p)))(config)

  (new ChiselStage).execute(Array("--target", "verilog") ++ args, Seq(
    ChiselGeneratorAnnotation(() => top.module),
    FirtoolOption("--disable-annotation-unknown")
  ))

  ChiselDB.init(false)
  ChiselDB.addToFileRegisters
  FileRegisters.write("./build")
}

object TestTop_fullSys extends App {
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
  val top = DisableMonitors(p => LazyModule(new TestTop_fullSys()(p)))(config)

  (new ChiselStage).execute(Array("--target", "verilog") ++ args, Seq(
    FirtoolOption("-O=release"),
    FirtoolOption("--disable-all-randomization"),
    FirtoolOption("--disable-annotation-unknown"),
    FirtoolOption("--strip-debug-info"),
    FirtoolOption("--lower-memories"),
    FirtoolOption("--add-vivado-ram-address-conflict-synthesis-bug-workaround"),
    FirtoolOption("--lowering-options=noAlwaysComb," +
      " disallowPortDeclSharing, disallowLocalVariables," +
      " emittedLineLength=120, explicitBitcast, locationInfoStyle=plain," +
      " disallowExpressionInliningInPorts, disallowMuxInlining"),
    FirtoolOption("--split-verilog"),
    FirtoolOption("-o=./build/rtl"),
    ChiselGeneratorAnnotation(() => top.module)
  ))

  ChiselDB.init(false)
  ChiselDB.addToFileRegisters
  FileRegisters.write("./build")
}

class TestTop_l2_for_sysn()(implicit p: Parameters) extends LazyModule {

  /* L1D L1I
   *  \  /
   *   L2
   */

  val delayFactor = 0.2
  val cacheParams = p(L2ParamKey)

  val nrL2 = 1

  def createClientNode(name: String, sources: Int) = {
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

  val l2xbar = TLXbar()
  // val ram = LazyModule(new TLRAM(AddressSet(0, 0xffffL), beatBytes = 32))
  val ram = LazyModule(new TLRAM(AddressSet(0, 0xffffffL), beatBytes = 32))
  var master_nodes: Seq[TLClientNode] = Seq() // TODO

  (0 until nrL2).map{i =>
    val l1d = createClientNode(s"l1d$i", 32)
    val l1i = TLClientNode(Seq(
      TLMasterPortParameters.v1(
        clients = Seq(TLMasterParameters.v1(
          name = s"l1i$i",
          sourceId = IdRange(0, 32)
        ))
      )
    ))
    master_nodes = master_nodes ++ Seq(l1d, l1i) // TODO

    val l1xbar = TLXbar()
    val l2node = LazyModule(new CoupledL2()(new Config((_, _, _) => {
      case L2ParamKey => L2Param(
        name = s"l2$i",
        ways = 8,
        sets = 512,
        clientCaches = Seq(L1Param(aliasBitsOpt = Some(2))),
        echoField = Seq(DirtyField())
      )
    }))).node

    l1xbar := TLBuffer() := l1i
    l1xbar := TLBuffer() := l1d

    l2xbar := TLBuffer() := l2node := l1xbar
  }

  ram.node :=
    TLXbar() :=*
      TLFragmenter(32, 64) :=*
      TLCacheCork() :=*
      TLDelayer(delayFactor) :=*
      l2xbar

  lazy val module = new LazyModuleImp(this) {
    master_nodes.zipWithIndex.foreach {
      case (node, i) =>
        node.makeIOs()(ValName(s"master_port_$i"))
    }
  }
}

object TestTop_l2_for_sysn extends App {
  val config = new Config((_, _, _) => {
    case L2ParamKey => L2Param(
      clientCaches = Seq(L1Param(aliasBitsOpt = Some(2))),
      echoField = Seq(DirtyField())
    )
    case HCCacheParamsKey => HCCacheParameters(
      echoField = Seq(DirtyField())
    )
    case DebugOptionsKey => DebugOptions()
  })
  val top = DisableMonitors(p => LazyModule(new TestTop_l2_for_sysn()(p)))(config)

  (new ChiselStage).execute(Array("--target", "verilog") ++ args, Seq(
    ChiselGeneratorAnnotation(() => top.module),
    FirtoolOption("--disable-annotation-unknown")
  ))

  ChiselDB.init(false)
  ChiselDB.addToFileRegisters
  FileRegisters.write("./build")
}

object TestTop_L3 extends App {
  val config = new Config((_, _, _) => {
    case L2ParamKey => L2Param(
      clientCaches = Seq(L1Param(aliasBitsOpt = Some(2))),
      echoField = Seq(DirtyField())
    )
    case DebugOptionsKey => DebugOptions()
  })
  val top = DisableMonitors(p => LazyModule(new TestTop_L3()(p)) )(config)

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