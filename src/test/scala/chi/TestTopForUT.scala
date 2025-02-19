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

class SplitCHIREQ()(implicit p: Parameters) extends TL2CHIL2Module {
  val io = IO(new Bundle {
    val mergedFlit = Input(UInt((new CHIREQ).getWidth.W))
    val splitFlit = Output(new CHIREQ)
  })

  var lsb = 0
  io.splitFlit.getElements.reverse.foreach {
    case e =>
      val elementWidth = e.asUInt.getWidth
      e := io.mergedFlit.asUInt(lsb + elementWidth - 1, lsb).asTypeOf(e.cloneType)
      lsb += elementWidth
  }
}

class SplitCHIRSP(reverse: Boolean = false)(implicit p: Parameters) extends TL2CHIL2Module {
  val io = IO(new Bundle {
    val mergedFlit = if(reverse) Output(UInt((new CHIRSP).getWidth.W)) else Input(UInt((new CHIRSP).getWidth.W))
    val splitFlit = if(reverse) Input(new CHIRSP) else Output(new CHIRSP)
  })

  if(reverse) {
    val mergedBits = io.splitFlit.getElements.map(_.asUInt)
    io.mergedFlit := Cat(mergedBits)
  } else {
    var lsb = 0
    io.splitFlit.getElements.reverse.foreach {
      case e =>
        val elementWidth = e.asUInt.getWidth
        e := io.mergedFlit.asUInt(lsb + elementWidth - 1, lsb).asTypeOf(e.cloneType)
        lsb += elementWidth
    }
  }
}

class SplitCHIDAT(reverse: Boolean = false)(implicit p: Parameters) extends TL2CHIL2Module {
  val io = IO(new Bundle {
    val mergedFlit = if(reverse) Output(UInt((new CHIDAT).getWidth.W)) else Input(UInt((new CHIDAT).getWidth.W))
    val splitFlit = if(reverse) Input(new CHIDAT) else Output(new CHIDAT)
  })

  if(reverse) {
    val mergedBits = io.splitFlit.getElements.map(_.asUInt)
    io.mergedFlit := Cat(mergedBits)
  } else {
    var lsb = 0
    io.splitFlit.getElements.reverse.foreach {
      case e =>
        val elementWidth = e.asUInt.getWidth
        e := io.mergedFlit.asUInt(lsb + elementWidth - 1, lsb).asTypeOf(e.cloneType)
        lsb += elementWidth
    }
  }
}

class SplitCHISNP(reverse: Boolean = false)(implicit p: Parameters) extends TL2CHIL2Module {
  val io = IO(new Bundle {
    val mergedFlit = if(reverse) Output(UInt((new CHISNP).getWidth.W)) else Input(UInt((new CHISNP).getWidth.W))
    val splitFlit = if(reverse) Input(new CHISNP) else Output(new CHISNP)
  })

  if(reverse) {
    val mergedBits = io.splitFlit.getElements.map(_.asUInt)
    io.mergedFlit := Cat(mergedBits)
  } else {
    var lsb = 0
    io.splitFlit.getElements.reverse.foreach {
      case e =>
        val elementWidth = e.asUInt.getWidth
        e := io.mergedFlit.asUInt(lsb + elementWidth - 1, lsb).asTypeOf(e.cloneType)
        lsb += elementWidth
    }
  }
}


class ReverseLinkMonitor(splitFlit: Boolean = false)(implicit p: Parameters) extends L2Module with HasCHIOpcodes {
  val io = IO(new Bundle() {
    val out = new DecoupledPortIO
    val in = Flipped(new PortIO(splitFlit = splitFlit))
    val nodeID = Input(UInt(NODEID_WIDTH.W))
  })

  val txState = RegInit(LinkStates.STOP)
  val rxState = RegInit(LinkStates.STOP)

  Seq(txState, rxState).zip(MixedVecInit(Seq(io.in.tx, io.in.rx))).foreach { case (state, link) =>
    state := MuxLookup(Cat(link.linkactivereq, link.linkactiveack), LinkStates.STOP)(Seq(
      Cat(true.B, false.B) -> LinkStates.ACTIVATE,
      Cat(true.B, true.B) -> LinkStates.RUN,
      Cat(false.B, true.B) -> LinkStates.DEACTIVATE,
      Cat(false.B, false.B) -> LinkStates.STOP
    ))
  }

  val txreqDeact, txrspDeact, txdatDeact = Wire(Bool())
  val txDeact = txreqDeact && txrspDeact && txdatDeact
  LCredit2Decoupled(io.in.tx.req, io.out.tx.req, LinkState(txState), txreqDeact, Some("txreq"), splitFlit = splitFlit)
  LCredit2Decoupled(io.in.tx.rsp, io.out.tx.rsp, LinkState(txState), txrspDeact, Some("txrsp"), splitFlit = splitFlit)
  LCredit2Decoupled(io.in.tx.dat, io.out.tx.dat, LinkState(txState), txdatDeact, Some("txdat"), splitFlit = splitFlit)
  Decoupled2LCredit(setSrcID(io.out.rx.snp, io.nodeID), io.in.rx.snp, LinkState(rxState), Some("rxsnp"), splitFlit = splitFlit)
  Decoupled2LCredit(setSrcID(io.out.rx.rsp, io.nodeID), io.in.rx.rsp, LinkState(rxState), Some("rxrsp"), splitFlit = splitFlit)
  Decoupled2LCredit(setSrcID(io.out.rx.dat, io.nodeID), io.in.rx.dat, LinkState(rxState), Some("rxdat"), splitFlit = splitFlit)

  io.in.rxsactive := true.B
  io.in.rx.linkactivereq := RegNext(true.B, init = false.B)
  io.in.tx.linkactiveack := RegNext(
    next = RegNext(io.in.tx.linkactivereq) || !txDeact,
    init = false.B
  )

  io.in.syscoack := true.B

  def setSrcID[T <: Bundle](in: DecoupledIO[T], srcID: UInt = 0.U): DecoupledIO[T] = {
    val out = Wire(in.cloneType)
    out <> in
    out.bits.elements.filter(_._1 == "srcID").head._2 := srcID
    out
  }
}

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

class CHIEmptyShell(splitFlit: Boolean)(implicit p: Parameters) extends  TL2CHIL2Module {
  val io = IO(new Bundle {
    val chiIn = Flipped(new PortIO(splitFlit = splitFlit))
    val chiOut = new PortIO(splitFlit = splitFlit)
  })

  io.chiIn <> io.chiOut
  dontTouch(io)
  dontTouch(clock)
  dontTouch(reset)
}

class TestTopForUT(numCores: Int = 1, numULAgents: Int = 1, banks: Int = 1, mmioBridgeTop: Boolean = false)(implicit p: Parameters) extends LazyModule
  with HasCHIMsgParameters {

  assert(numCores == 1)

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
        echoFields = Seq(IsKeywordField()),
        requestFields = Seq(AliasField(2), VaddrField(36), PrefetchField()),
        responseKeys = cacheParams.respKey
      )
    ))
    
    masterNode
  }

  val l1d_nodes = (0 until numCores).map(i => createClientNode(s"l1d$i", 64))
  val l1i_nodes = (0 until numCores).map {i =>
    (0 until numULAgents).map { j =>
      TLClientNode(Seq(
        TLMasterPortParameters.v1(
          clients = Seq(TLMasterParameters.v1(
            name = s"l1i${i}_${j}",
            sourceId = IdRange(0, 63)
          ))
        )
      ))
    }
  }

  val l2_nodes = (0 until numCores).map(i => LazyModule(new TL2CHICoupledL2()(new Config((_, _, _) => {
    case L2ParamKey => p(L2ParamKey).copy(
      name = s"l2$i",
      hartId = i
    )
    case EnableCHI => true
    case CHIIssue => p(CHIIssue)
    case BankBitsKey => log2Ceil(banks)
    case MaxHartIdBits => log2Up(numCores)
    case PerfCounterOptionsKey => PerfCounterOptions(false, false, 0)
  }))))

  val bankBinders = (0 until numCores).map(_ => BankBinder(banks, 64))

  var mmioClientNodes: Seq[TLClientNode] = Nil
  var cmoClientNodes: Seq[TLClientNode] = Nil
  l1d_nodes.zip(l2_nodes).zipWithIndex.foreach { case ((l1d, l2), i) =>
    val l1xbar = TLXbar()

    val cmoClientNode = TLClientNode(Seq(
      TLMasterPortParameters.v1(
        clients = Seq(TLMasterParameters.v1(
          name = "cmo",
          sourceId = IdRange(0, 7),
        )),
        requestFields = Nil
      )
    ))

    l1xbar := 
      TLLogger(s"L2_L1_CORE${i}_TLC", !cacheParams.FPGAPlatform && cacheParams.enableTLLog) := 
      TLBuffer() := l1d

    l1i_nodes(i).zipWithIndex.foreach { case (l1i, j) =>
      l1xbar :=
        TLLogger(s"L2_L1_CORE${i}_TLUL${j}", !cacheParams.FPGAPlatform && cacheParams.enableTLLog) :=
        TLBuffer() := l1i
    }

    l1xbar := 
      TLLogger(s"L2_L1_CORE${i}_TLC", !cacheParams.FPGAPlatform && cacheParams.enableTLLog) := 
      TLBuffer() := cmoClientNode
    
    l2.managerNode :=
      TLXbar() :=*
      bankBinders(i) :*=
      l2.node :*=
      l1xbar

    val mmioClientNode = TLClientNode(Seq(
      TLMasterPortParameters.v1(
        clients = Seq(TLMasterParameters.v1(
          name = "mmio",
          sourceId = IdRange(0, 7),
        )),
        requestFields = Seq(MemBackTypeMMField(), MemPageTypeNCField())
      )
    ))

    mmioClientNodes = mmioClientNodes ++ Seq(mmioClientNode)
    cmoClientNodes = cmoClientNodes ++ Seq(cmoClientNode)

    l2.mmioBridge.mmioNode := mmioClientNode
  }

  lazy val module = new LazyModuleImp(this){
    if(!mmioBridgeTop) {
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
    }

    mmioClientNodes.zipWithIndex.foreach { case(node, i) =>
      node.makeIOs()(ValName(s"mmioBridge_${i}_"))
    }

    cmoClientNodes.zipWithIndex.foreach { case(node, i) =>
      node.makeIOs()(ValName(s"cmo_${i}_"))
    }

    val io = IO(new Bundle {
      val chi = if(mmioBridgeTop) Some(new DecoupledPortIO) else None
    })

    l2_nodes.zipWithIndex.foreach { case (l2, i) =>
      dontTouch(l2.module.io)

      val chiEndpoint = if(!mmioBridgeTop) Some(Module(new SimpleEndpointCHI())) else None
      val reverseLinkMonitor = if(mmioBridgeTop) Some(Module(new ReverseLinkMonitor(splitFlit = p(L2ParamKey).splitFlit))) else None
      reverseLinkMonitor.foreach { r =>
        r.io.nodeID := 0.U
        r.io.out <> io.chi.get
      }

      if(p(L2ParamKey).splitFlit) {
        if(!mmioBridgeTop) {
          chiEndpoint.get.io.chi <> l2.module.io_chi
        } else {
          reverseLinkMonitor.get.io.in <> l2.module.io_chi
        }
      } else {
        if(!mmioBridgeTop) {
          val chiEmptyShell = Module(new CHIEmptyShell(p(L2ParamKey).splitFlit))
          chiEmptyShell.io.chiIn <> l2.module.io_chi

          chiEndpoint.get.io.chi.rxsactive <> chiEmptyShell.io.chiOut.rxsactive
          chiEndpoint.get.io.chi.txsactive <> chiEmptyShell.io.chiOut.txsactive
          chiEndpoint.get.io.chi.syscoack <> chiEmptyShell.io.chiOut.syscoack
          chiEndpoint.get.io.chi.syscoreq <> chiEmptyShell.io.chiOut.syscoreq
          chiEndpoint.get.io.chi.tx.linkactiveack <> chiEmptyShell.io.chiOut.tx.linkactiveack
          chiEndpoint.get.io.chi.tx.linkactivereq <> chiEmptyShell.io.chiOut.tx.linkactivereq
          chiEndpoint.get.io.chi.rx.linkactiveack <> chiEmptyShell.io.chiOut.rx.linkactiveack
          chiEndpoint.get.io.chi.rx.linkactivereq <> chiEmptyShell.io.chiOut.rx.linkactivereq

          val in_rx = chiEndpoint.get.io.chi.rx
          val out_rx = chiEmptyShell.io.chiOut.rx

          in_rx.rsp.flitpend <> out_rx.rsp.flitpend
          in_rx.rsp.flitv <> out_rx.rsp.flitv
          in_rx.rsp.lcrdv <> out_rx.rsp.lcrdv
          val splitRXRSP = Module(new SplitCHIRSP(reverse = true))
          out_rx.rsp.flit := splitRXRSP.io.mergedFlit
          splitRXRSP.io.splitFlit := in_rx.rsp.flit


          in_rx.dat.flitpend <> out_rx.dat.flitpend
          in_rx.dat.flitv <> out_rx.dat.flitv
          in_rx.dat.lcrdv <> out_rx.dat.lcrdv
          val splitRXDAT = Module(new SplitCHIDAT(reverse = true))
          out_rx.dat.flit := splitRXDAT.io.mergedFlit
          splitRXDAT.io.splitFlit := in_rx.dat.flit

          
          in_rx.snp.flitpend <> out_rx.snp.flitpend
          in_rx.snp.flitv <> out_rx.snp.flitv
          in_rx.snp.lcrdv <> out_rx.snp.lcrdv
          val splitRXSNP = Module(new SplitCHISNP(reverse = true))
          out_rx.snp.flit := splitRXSNP.io.mergedFlit
          splitRXSNP.io.splitFlit := in_rx.snp.flit


          val in_tx = chiEndpoint.get.io.chi.tx
          val out_tx = chiEmptyShell.io.chiOut.tx
          in_tx.req.flitpend <> out_tx.req.flitpend
          in_tx.req.flitv <> out_tx.req.flitv
          in_tx.req.lcrdv <> out_tx.req.lcrdv
          val splitTXREQ = Module(new SplitCHIREQ)
          splitTXREQ.io.mergedFlit := out_tx.req.flit
          in_tx.req.flit := splitTXREQ.io.splitFlit


          in_tx.rsp.flitpend <> out_tx.rsp.flitpend
          in_tx.rsp.flitv <> out_tx.rsp.flitv
          in_tx.rsp.lcrdv <> out_tx.rsp.lcrdv
          val splitTXRSP = Module(new SplitCHIRSP)
          splitTXRSP.io.mergedFlit := out_tx.rsp.flit
          in_tx.rsp.flit := splitTXRSP.io.splitFlit


          in_tx.dat.flitpend <> out_tx.dat.flitpend
          in_tx.dat.flitv <> out_tx.dat.flitv
          in_tx.dat.lcrdv <> out_tx.dat.lcrdv
          val splitTXDAT = Module(new SplitCHIDAT)
          splitTXDAT.io.mergedFlit := out_tx.dat.flit
          in_tx.dat.flit := splitTXDAT.io.splitFlit
        } else {
          reverseLinkMonitor.get.io.in <> l2.module.io_chi
        }
      }

      l2.module.io.hartId := i.U
      l2.module.io_nodeID := i.U(NODEID_WIDTH.W)
      l2.module.io.debugTopDown := DontCare
      l2.module.io.pfCtrlFromCore := DontCare
      l2.module.io.l2_tlb_req <> DontCare

      dontTouch(l2.module.io_nodeID)
    }
  }

}

class MMIOBridgeTop()(implicit p: Parameters) extends LazyModule {
  val mmioClientNode = TLClientNode(Seq(
    TLMasterPortParameters.v1(
      clients = Seq(TLMasterParameters.v1(
        name = "mmio",
        sourceId = IdRange(0, 7),
      )),
      requestFields = Seq(MemBackTypeMMField(), MemPageTypeNCField())
    )
  ))

  val mmioBridge = LazyModule(new MMIOBridge())

  mmioBridge.mmioNode := mmioClientNode

  lazy val module = new LazyModuleImp(this) {
    val io = IO(new DecoupledNoSnpPortIO)
    val io_pCrd = IO(Vec(p(L2ParamKey).mmioBridgeSize, new PCrdQueryBundle))
    
    mmioClientNode.makeIOs()(ValName("mmioClient"))

    mmioBridge.module.io <> io
    mmioBridge.module.io_pCrd <> io_pCrd
  }
}

object TestTopForUT extends App {

  val isMMIOBridgeTop = sys.env.getOrElse("MMIOBRIDGE_TOP", "0") == "1"
  val isReleaseRTL = sys.env.getOrElse("RELEASE_RTL", "0") == "1"
  println(s"isMMIOBridgeTop: $isMMIOBridgeTop, isReleaseRTL: $isReleaseRTL")

  Constantin.init(false)

  val config = new Config((_, _, _) => {
    case L2ParamKey => L2Param(
      ways = 4,
      sets = 256,
      clientCaches = Seq(L1Param(
        aliasBitsOpt = Some(2),
        // vaddrBitsOpt = Some(36),
        // isKeywordBitsOpt = Some(true)
      )),
      // reqField = Seq(utility.ReqSourceField()),
      // echoField = Seq(huancun.DirtyField()),
      // tagECC = Some("secded"),
      // dataECC = Some("secded"),
      // enableTagECC = true,
      // enableDataECC = true,
      dataCheck = Some("none"), // TODO:
      enablePoison = false, // TODO: 

      enablePerf = false, 
      enableRollingDB = false,
      enableMonitor = false,
      enableTLLog = false,
      elaboratedTopDown = false, 
      FPGAPlatform = false,
      splitFlit = false,

      // prefetch = Seq(BOPParameters()),
    )
    case CHIIssue => if(isReleaseRTL) "E.b" else "E.b"
  })

  val top = DisableMonitors(
    p => LazyModule(
        new TestTopForUT( 
            numCores = 1,
            numULAgents = 1,
            banks = if(isReleaseRTL) 4 else 1,
            isMMIOBridgeTop
        )(p)
    )
  )(config)

  (new ChiselStage).execute(args, Seq(ChiselGeneratorAnnotation(() => top.module)))
}

object MMIOBridgeTop extends App {
  val config = new Config((_, _, _) => {
    case L2ParamKey => L2Param(
      ways = 2,
      sets = 2,
      mshrs = 4,
      mmioBridgeSize = 8,
      enablePerf = false,
      enableRollingDB = false,
      enableMonitor = false,
      enableTLLog = false,
      elaboratedTopDown = false,
      FPGAPlatform = false,
      splitFlit = true,
      dataCheck = Some("none")
    )
    case CHIIssue => "E.b"
  })

  val top = DisableMonitors(
    p => LazyModule(
      new MMIOBridgeTop()(p)
    )
  )(config)

  (new ChiselStage).execute(args, Seq(ChiselGeneratorAnnotation(() => top.module)))
}