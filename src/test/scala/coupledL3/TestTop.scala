package coupledL3
import circt.stage.{ChiselStage, FirtoolOption}
import chisel3._
import chisel3.util._
import org.chipsalliance.cde.config._
import chisel3.stage.ChiselGeneratorAnnotation
import freechips.rocketchip.diplomacy._
import freechips.rocketchip.tilelink._
import coupledL2.{CoupledL2, L2ParamKey}
import coupledL2.prefetch._
import huancun.{HuanCun, HCCacheParameters, HCCacheParamsKey, CacheParameters}
import scala.collection.mutable.ArrayBuffer

class TestTop_L3()(implicit p: Parameters) extends LazyModule {

  /*   L2  L2
   *    \ /
   *     L3
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

  val fake_l2_nodes = (0 until 2) map( i => createClientNode(s"l2$i", 32))
  val master_nodes = fake_l2_nodes

  val l3 = LazyModule(new CoupledL3()(new Config((_, _, _) => {
      case L3ParamKey => L3Param(
        name = s"l3",
        ways = 4,
        // sets = 128,
        sets = 32,
        inclusionPolicy = "NINE",
        
        clientCaches = Seq(CacheParameters(
          sets = 32,
          ways = 8,
          aliasBitsOpt = None,
          name = "l2",
          blockGranularity = 64
        )),
        echoField = Seq(DirtyField())
      )
  })))
  val xbar = TLXbar()
  val ram = LazyModule(new TLRAM(AddressSet(0, 0xffffffL), beatBytes = 32))

  for (l2 <- fake_l2_nodes) {
    xbar := TLBuffer() := l2
  }

  // val dma_node = TLClientNode(Seq(TLMasterPortParameters.v2(
  //   Seq(TLMasterParameters.v1(
  //     name = "dma",
  //     sourceId = IdRange(0, 16),
  //     supportsProbe = TransferSizes.none
  //   )),
  //   channelBytes = TLChannelBeatBytes(cacheParams.blockBytes),
  //   minLatency = 1,
  //   echoFields = Nil,
  // )))
  // xbar := TLBuffer() := dma_node

  ram.node :=
    TLXbar() :=*
      TLFragmenter(32, 64) :=*
      TLCacheCork() :=*
      TLDelayer(delayFactor) :=*
      l3.node :=* xbar

  lazy val module = new LazyModuleImp(this){
    master_nodes.zipWithIndex.foreach{
      case (node, i) =>
        node.makeIOs()(ValName(s"master_port_$i"))
    }
    // dma_node.makeIOs()(ValName("dma_port"))
  }
}

class TestTop_L3_for_sysn()(implicit p: Parameters) extends LazyModule {

  /*   L2  L2
   *    \ /
   *     L3
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

  val fake_l2_nodes = (0 until 2) map( i => createClientNode(s"l2$i", 32))
  val master_nodes = fake_l2_nodes

  val l3 = LazyModule(new CoupledL3()(new Config((_, _, _) => {
      case L3ParamKey => L3Param(
        name = s"l3",
        ways = 16,
        sets = 1024,
        clientCaches = Seq(CacheParameters(
          sets = 512,
          ways = 8 * 2 + 2,
          aliasBitsOpt = None,
          name = "l2",
          blockGranularity = 64
        )),
        echoField = Seq(DirtyField())
      )
  })))
  val xbar = TLXbar()
  val ram = LazyModule(new TLRAM(AddressSet(0, 0xffffffL), beatBytes = 32))

  for (l2 <- fake_l2_nodes) {
    xbar := TLBuffer() := l2
  }

  // val dma_node = TLClientNode(Seq(TLMasterPortParameters.v2(
  //   Seq(TLMasterParameters.v1(
  //     name = "dma",
  //     sourceId = IdRange(0, 16),
  //     supportsProbe = TransferSizes.none
  //   )),
  //   channelBytes = TLChannelBeatBytes(cacheParams.blockBytes),
  //   minLatency = 1,
  //   echoFields = Nil,
  // )))
  // xbar := TLBuffer() := dma_node

  ram.node :=
    TLXbar() :=*
      TLFragmenter(32, 64) :=*
      TLCacheCork() :=*
      TLDelayer(delayFactor) :=*
      l3.node :=* xbar

  lazy val module = new LazyModuleImp(this){
    master_nodes.zipWithIndex.foreach{
      case (node, i) =>
        node.makeIOs()(ValName(s"master_port_$i"))
    }
    // dma_node.makeIOs()(ValName("dma_port"))
  }
}


object TestTop_L3 extends App {
  val config = new Config((_, _, _) => {
    case L3ParamKey => L3Param(
      name = s"l3",
      ways = 4,
      // sets = 128,
      sets = 32,
      clientCaches = Nil,
      echoField = Seq(DirtyField())
    )
  })
  val top = DisableMonitors(p => LazyModule(new TestTop_L3()(p)) )(config)

  (new ChiselStage).execute(Array("--target", "verilog") ++ args, Seq(
    ChiselGeneratorAnnotation(() => top.module),
    FirtoolOption("--disable-annotation-unknown")
  ))
}

object TestTop_L3_for_sysn extends App {
  val config = new Config((_, _, _) => {
    case L3ParamKey => L3Param(
      name = s"l3",
      ways = 16,
      sets = 1024,
      clientCaches = Nil,
      echoField = Seq(DirtyField())
    )
  })
  val top = DisableMonitors(p => LazyModule(new TestTop_L3_for_sysn()(p)) )(config)

  (new ChiselStage).execute(Array("--target", "verilog") ++ args, Seq(
    ChiselGeneratorAnnotation(() => top.module),
    FirtoolOption("--disable-annotation-unknown")
  ))
}