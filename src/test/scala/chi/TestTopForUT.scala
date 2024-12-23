package coupledL2

import chisel3._
import chisel3.util._
import org.chipsalliance.cde.config._
import chisel3.stage.{ChiselGeneratorAnnotation, ChiselStage}
import freechips.rocketchip.diplomacy._
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tile.MaxHartIdBits
import huancun._
import utility._
import coupledL2.prefetch._
import coupledL2.tl2chi._
import utility.{ChiselDB, FileRegisters, TLLogger}

class SimpleEndpointCHI()(implicit p: Parameters) extends TL2CHIL2Module {
    val io = IO(new Bundle {
        val chi = Flipped(new PortIO(splitFlit = true))
    })

    val fakeCHIBundle = WireInit(0.U.asTypeOf(new PortIO(splitFlit = true)))
    io.chi <> fakeCHIBundle

    // Keep clock and reset
    val (_, cnt) = Counter(true.B, 10)
    dontTouch(cnt)

    dontTouch(io)
}

class TestTopForUT(numCores: Int = 1, numULAgents: Int = 1, banks: Int = 1)(implicit p: Parameters) extends LazyModule
  with HasCHIMsgParameters {

  override lazy val desiredName: String = "TestTop"
  val delayFactor = 0.5
  val cacheParams = p(L2ParamKey)

  def createClientNode(name: String, sources: Int) = {
    val masterNode = TLClientNode(Seq(
      TLMasterPortParameters.v2(
        masters = Seq(
          TLMasterParameters.v1(
            name = name,
            sourceId = IdRange(0, sources - 1),
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

  val l1d_nodes = (0 until numCores).map(i => createClientNode(s"l1d$i", 16))
  val l1i_nodes = (0 until numCores).map {i =>
    (0 until numULAgents).map { j =>
      TLClientNode(Seq(
        TLMasterPortParameters.v1(
          clients = Seq(TLMasterParameters.v1(
            name = s"l1i${i}_${j}",
            sourceId = IdRange(0, 15)
          ))
        )
      ))
    }
  }

  val l2_nodes = (0 until numCores).map(i => LazyModule(new TL2CHICoupledL2()(new Config((_, _, _) => {
    case L2ParamKey => L2Param(
      name = s"l2$i",
      ways = 4,
      sets = 256,
      clientCaches = Seq(L1Param(aliasBitsOpt = Some(2))),
      // echoField = Seq(DirtyField),
      enablePerf = false,
      enableRollingDB = false,
      enableMonitor = false,
      enableTLLog = false,
      elaboratedTopDown = false,
      FPGAPlatform = false,
      hartId = i,
      splitFlit = true
    )
    case EnableCHI => true
    case BankBitsKey => log2Ceil(banks)
    case MaxHartIdBits => log2Up(numCores)
    case PerfCounterOptionsKey => PerfCounterOptions(false, false, 0)
  }))))

  val bankBinders = (0 until numCores).map(_ => BankBinder(banks, 64))

  l1d_nodes.zip(l2_nodes).zipWithIndex.foreach { case ((l1d, l2), i) =>
    val l1xbar = TLXbar()

    l1xbar := 
      TLLogger(s"L2_L1_CORE${i}_TLC", !cacheParams.FPGAPlatform && cacheParams.enableTLLog) := 
      TLBuffer() := l1d

    l1i_nodes(i).zipWithIndex.foreach { case (l1i, j) =>
      l1xbar :=
        TLLogger(s"L2_L1_CORE${i}_TLUL${j}", !cacheParams.FPGAPlatform && cacheParams.enableTLLog) :=
        TLBuffer() := l1i
    }
    
    l2.managerNode :=
      TLXbar() :=*
      bankBinders(i) :*=
      l2.node :*=
      l1xbar

    val mmioClientNode = TLClientNode(Seq(
      TLMasterPortParameters.v1(
        clients = Seq(TLMasterParameters.v1(
          "uncache"
        ))
      )
    ))

    l2.mmioBridge.mmioNode := mmioClientNode
  }

  lazy val module = new LazyModuleImp(this){
    l1d_nodes.zipWithIndex.foreach{
      case (node, i) =>
        node.makeIOs()(ValName(s"master_port_$i"))
    }

    if (numULAgents != 0) {
      l1i_nodes.zipWithIndex.foreach { case (core, i) =>
        core.zipWithIndex.foreach { case (node, j) =>
          node.makeIOs()(ValName(s"master_ul_port_${i}_${j}"))
        }
      }
    }

    l2_nodes.zipWithIndex.foreach { case (l2, i) =>
      dontTouch(l2.module.io)

      val chiEndpoint = Module(new SimpleEndpointCHI())
      chiEndpoint.io.chi <> l2.module.io_chi

      l2.module.io.hartId := i.U
      l2.module.io_nodeID := i.U(NODEID_WIDTH.W)
      l2.module.io.debugTopDown := DontCare
      l2.module.io.l2_tlb_req <> DontCare
    }
  }

}


object TestTopForUT extends App {

  val config = new Config((_, _, _) => {
    case L2ParamKey => L2Param(
      enablePerf = false,
      enableRollingDB = false,
      enableMonitor = false,
      enableTLLog = false,
      elaboratedTopDown = false,
      FPGAPlatform = true
    )
  })

  val top = DisableMonitors(
    p => LazyModule(
        new TestTopForUT( 
            numCores = 1,
            numULAgents = 1,
            banks = 1
        )(p)
    )
  )(config)

  (new ChiselStage).execute(args, Seq(ChiselGeneratorAnnotation(() => top.module)))
}
