// package coupledL2.prefetch.intel_spp

// import org.chipsalliance.cde.config.Parameters
// import chisel3._
// import chisel3.util._
// import freechips.rocketchip.tilelink._
// import coupledL2._
// import coupledL2.HasCoupledL2Parameters
// import xs.utils.perf.HasPerfLogging
// import xs.utils.SRAMQueue
// import coupledL2.prefetch.{PrefetchParameters,HasPrefetchParameters,ReplaceableQueueV2}
// import coupledL2.prefetch.{PrefetchReq,PrefetchTrain,PrefetchResp,PrefetchEvict}
// import coupledL2.prefetch.{BestOffsetPrefetch,BOPParameters,PrefetchReceiver,PrefetchReceiverParams}
// case class HyperPrefetchParams(
//   fTableEntries: Int = 32,
//   pTableQueueEntries: Int = 2,
//   fTableQueueEntries: Int = 256
// )
//     extends PrefetchParameters {
//   override val hasPrefetchBit:  Boolean = true
//   override val inflightEntries: Int = 64
// }

// trait HasHyperPrefetcherParams extends HasCoupledL2Parameters {
//   val hyperPrefetchParams = HyperPrefetchParams()

//   val pageAddrBits = fullAddressBits - pageOffsetBits
//   val blkOffsetBits = pageOffsetBits - offsetBits

//   val fTableEntries = hyperPrefetchParams.fTableEntries
//   val fTagBits = pageAddrBits - log2Up(fTableEntries)
//   val pTableQueueEntries = hyperPrefetchParams.pTableQueueEntries
//   val fTableQueueEntries = hyperPrefetchParams.fTableQueueEntries
// }

// abstract class PrefetchBranchV2Module(implicit val p: Parameters) extends Module with HasHyperPrefetcherParams
// abstract class PrefetchBranchV2Bundle(implicit val p: Parameters) extends Bundle with HasHyperPrefetcherParams

// object PrefetcherId {
//   val bits = 2

//   def BOP           = 0.U(bits.W)
//   def SMS           = 1.U(bits.W)
//   def SPP           = 2.U(bits.W)
//   def OHTERS        = 3.U(bits.W)
// }

// class FilterV2(parentName:String = "Unknown")(implicit p: Parameters) extends PrefetchBranchV2Module with HasPerfLogging{
//   val io = IO(new Bundle() {
//     val req = Flipped(DecoupledIO(new PrefetchReq))
//     val resp = DecoupledIO(new PrefetchReq)
//     val evict = Flipped(DecoupledIO(new PrefetchEvict))
//     val pf_Id = Input(UInt(2.W))
//   })

//   def idx(addr:      UInt) = addr(log2Up(fTableEntries) - 1, 0)
//   def tag(addr:      UInt) = addr(pageAddrBits - 1, log2Up(fTableEntries))

//   def fTableEntry() = new Bundle {
//     val valid = Bool()
//     val tag = UInt(fTagBits.W)
//     val bitMap = Vec(64, Bool())
//   }

//   val fTable = RegInit(VecInit(Seq.fill(fTableEntries)(0.U.asTypeOf(fTableEntry()))))
//   val q = Module(new ReplaceableQueueV2(UInt(fullAddressBits.W), fTableQueueEntries))

//   val oldAddr = io.req.bits.addr
//   val blkAddr = oldAddr(fullAddressBits - 1, offsetBits)
//   val pageAddr = oldAddr(fullAddressBits - 1, pageOffsetBits)
//   val blkOffset = oldAddr(pageOffsetBits - 1, offsetBits)

//   //read fTable
//   val hit = Wire(Bool())
//   val readResult = Wire(fTableEntry())
//   readResult := fTable(idx(pageAddr))
//   hit := readResult.valid && tag(pageAddr) === readResult.tag
//   val hitForMap = hit && readResult.bitMap(blkOffset)

//   // filter sms and spp, only skip bop
//   io.resp.valid := io.req.fire && (io.pf_Id === PrefetcherId.BOP || !hitForMap)
//   io.resp.bits := io.req.bits

//   val wData = Wire(fTableEntry())
//   val newBitMap = readResult.bitMap.zipWithIndex.map{ case (b, i) => Mux(i.asUInt === blkOffset, true.B, false.B) }
  
//   wData.valid := true.B
//   wData.tag := tag(pageAddr)
//   wData.bitMap := newBitMap
//   when(io.req.fire) {
//     when(hit) {
//       fTable(idx(pageAddr)).bitMap(blkOffset) := true.B
//     } .otherwise {
//       fTable(idx(pageAddr)) := wData
//     }
//   }

//   q.io.enq.valid := io.req.fire && !hitForMap
//   q.io.enq.bits := io.req.bits.addr
//   q.io.deq.ready := q.io.full && q.io.enq.fire

//   val evictAddr = q.io.deq.bits
//   val evictPageAddr = evictAddr(fullAddressBits - 1, pageOffsetBits)
//   val evictBlkOffset = evictAddr(pageOffsetBits - 1, offsetBits)
//   val evictBlkAddr = evictAddr(fullAddressBits - 1, offsetBits)
//   val readEvict = Wire(fTableEntry())
//   val hitEvict = Wire(Bool())
//   val conflict = io.req.fire && blkAddr === evictBlkAddr
//   readEvict := fTable(idx(evictPageAddr))
//   hitEvict := q.io.deq.fire && readEvict.valid && tag(evictPageAddr) === readEvict.tag && readEvict.bitMap(evictBlkOffset) && !conflict
//   when(hitEvict) {
//     fTable(idx(evictPageAddr)).bitMap(evictBlkOffset) := false.B
//   }

//   /*
//   val evictAddr = io.evict.bits.addr
//   val evictPageAddr = evictAddr(fullAddressBits - 1, pageOffsetBits)
//   val evictBlkOffset = evictAddr(pageOffsetBits - 1, offsetBits)
//   val evictBlkAddr = evictAddr(fullAddressBits - 1, offsetBits)
//   val readEvict = Wire(fTableEntry())
//   val hitEvict = Wire(Bool())
//   val conflict = io.req.fire && blkAddr === evictBlkAddr
//   readEvict := fTable(idx(evictPageAddr))
//   hitEvict := io.evict.valid && readEvict.valid && tag(evictPageAddr) === readEvict.tag && readEvict.bitMap(evictBlkOffset) && !conflict
//   when(hitEvict) {
//     fTable(idx(evictPageAddr)).bitMap(evictBlkOffset) := false.B
//   }*/

//   io.req.ready := true.B
//   io.evict.ready := true.B
//   XSPerfAccumulate("hyper_filter_nums",io.req.fire && hitForMap)
//   XSPerfAccumulate("hyper_filter_input",io.req.fire)
//   XSPerfAccumulate("hyper_filter_output",io.resp.fire)
//   XSPerfAccumulate("hyper_filter_bop_req",io.resp.valid && io.pf_Id === PrefetcherId.BOP)
//   XSPerfAccumulate("hyper_filter_sms_req",io.resp.valid && io.pf_Id === PrefetcherId.SMS)
//   XSPerfAccumulate("hyper_filter_spp_req",io.resp.valid && io.pf_Id === PrefetcherId.SPP)
// }

// //Only used for hybrid spp and bop
// class HyperPrefetcher(parentName:String = "Unknown")(implicit p: Parameters) extends PrefetchBranchV2Module with HasPerfLogging{
//   val io = IO(new Bundle() {
//     val train = Flipped(DecoupledIO(new PrefetchTrain))
//     val req = DecoupledIO(new PrefetchReq)
//     val resp = Flipped(DecoupledIO(new PrefetchResp))
//     val evict = Flipped(DecoupledIO(new PrefetchEvict))
//     val recv_addr = Flipped(ValidIO(UInt(64.W)))
//     val hint2llc = ValidIO(new PrefetchReq)
//     val db_degree = Flipped(ValidIO(UInt(2.W)))
//     val queue_used = Input(UInt(6.W))
//   })

//   val fTable = Module(new FilterV2(parentName + "ftable_"))

//   val spp = Module(new SignaturePathPrefetch(parentName = parentName + "spp_")(p.alterPartial({
//         case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(SPPParameters()))
//   })))
//   val bop = Module(new BestOffsetPrefetch()(p.alterPartial({
//         case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(BOPParameters()))
//   })))
//   val sms = Module(new PrefetchReceiver()(p.alterPartial({
//         case L2ParamKey => p(L2ParamKey).copy(prefetch = Some(PrefetchReceiverParams()))
//   })))

//   val q_sms = Module(new ReplaceableQueueV2(chiselTypeOf(sms.io.req.bits), pTableQueueEntries))
//   val q_spp = Module(new ReplaceableQueueV2(chiselTypeOf(spp.io.req.bits), pTableQueueEntries))
//   q_sms.io.enq <> sms.io.req
//   q_sms.io.deq.ready := !bop.io.req.valid

//   q_spp.io.enq <> spp.io.req
//   q_spp.io.deq.ready := !q_sms.io.deq.fire && !bop.io.req.valid

//   //TODO: SPP need to be trained on any AceessState including MISS,PF_HIT,CACHE_HIT,LATE_HIT
//   // spp.io.train.valid := io.train.valid && io.train.bits.state === AccessState.MISS
//   spp.io.train.valid := io.train.valid
//   spp.io.train.bits := io.train.bits
//   spp.io.hint_req.ready := true.B

//   val train_for_bop = RegInit(0.U.asTypeOf(new PrefetchTrain))
//   val train_for_bop_valid = RegInit(false.B)
  
//   when(io.train.valid && !bop.io.train.ready) {
//     train_for_bop := io.train.bits
//     train_for_bop_valid := true.B
//   }
//   bop.io.train.valid := false.B //io.train.valid || train_for_bop_valid
//   bop.io.train.bits := Mux(io.train.valid, io.train.bits, train_for_bop)
//   when(bop.io.train.fire && !io.train.valid) {
//     train_for_bop_valid := false.B
//   }

//   bop.io.resp <> io.resp
//   spp.io.resp.bits.tag := 0.U
//   spp.io.resp.bits.set := 0.U
//   spp.io.resp.valid := false.B

//   spp.io.req.ready := true.B
//   bop.io.req.ready := true.B

//   sms.io.recv_addr.valid := io.recv_addr.valid
//   sms.io.recv_addr.bits := io.recv_addr.bits
//   sms.io.req.ready := true.B
//   spp.io.from_ghr := 0.U.asTypeOf(spp.io.from_ghr.cloneType)
//   // spp.io.from_ghr.bits.deadCov_state := pf_deadCov_state
//   // spp.io.from_ghr.bits.hitAcc_state := ghr.l2pf_hitAccState
//   // spp.io.from_ghr.bits.shareBO := ghr.shareBO
//   // spp.io.from_ghr.bits.global_queue_used := MLFQ_1.io.used
//   // fTable.io.req.valid := q_spp.io.deq.fire || q_sms.io.deq.fire || bop.io.req.valid
//   // fTable.io.req.bits := Mux(bop.io.req.valid, bop.io.req.bits, 
//   //                         Mux(q_sms.io.deq.fire, q_sms.io.deq.bits, q_spp.io.deq.bits))
//   // fTable.io.pf_Id := Mux(bop.io.req.valid,PrefetcherId.BOP,
//   //                         Mux(q_sms.io.deq.fire, PrefetcherId.SMS, PrefetcherId.SPP))           
//   // fTable.io.spp2llc := Mux(bop.io.req.valid, false.B,
//   //                         Mux(q_sms.io.deq.fire, false.B, spp_hint2llc))

//   when(bop.io.req.valid) {
//     fTable.io.req.valid := bop.io.req.valid
//     fTable.io.req.bits := bop.io.req.bits
//     fTable.io.pf_Id := PrefetcherId.BOP
//     // fTable.io.spp2llc := false.B
//   }.elsewhen(q_sms.io.deq.fire) {
//     fTable.io.req.valid := q_sms.io.deq.valid
//     fTable.io.req.bits := q_sms.io.deq.bits
//     fTable.io.pf_Id := PrefetcherId.SMS
//     // fTable.io.spp2llc := false.B
//   }.otherwise {
//     fTable.io.req.valid := q_spp.io.deq.valid
//     fTable.io.req.bits.tag := q_spp.io.deq.bits.tag
//     fTable.io.req.bits.set := q_spp.io.deq.bits.set
//     // fTable.io.req.bits.isBOP := q_spp.io.deq.bits.isBOP
//     fTable.io.req.bits.source := q_spp.io.deq.bits.source
//     fTable.io.req.bits.needT := q_spp.io.deq.bits.needT
//     fTable.io.pf_Id := PrefetcherId.SPP
//     // fTable.io.spp2llc := q_spp.io.deq.bits.hint2llc
//   }

//   io.req <> fTable.io.resp
//   // io.hint2llc := fTable.io.hint2llc;dontTouch(io.hint2llc)
//   io.hint2llc := 0.U.asTypeOf(Valid(new PrefetchReq))
//   fTable.io.evict.valid := io.evict.valid
//   fTable.io.evict.bits := io.evict.bits
//   io.evict.ready := fTable.io.evict.ready

//   // fTable.io.from_bop := bop.io.req.valid

//   io.train.ready := true.B
//   spp.io.db_degree.valid := io.db_degree.valid
//   spp.io.db_degree.bits := io.db_degree.bits
//   spp.io.queue_used := io.queue_used
//   fTable.io.req.bits.pfVec := 0.U
//   spp.io.resp.bits := 0.U.asTypeOf(spp.io.resp.bits.cloneType)
//   XSPerfAccumulate("bop_send2_queue", bop.io.req.valid)
//   XSPerfAccumulate("sms_send2_queue", q_sms.io.enq.fire)
//   XSPerfAccumulate("spp_send2_queue", q_spp.io.enq.fire)
//   XSPerfAccumulate("sms_q_deq", q_sms.io.deq.fire)
//   XSPerfAccumulate("spp_q_deq", q_spp.io.deq.fire)
//   XSPerfAccumulate("hyper_overlapped", (bop.io.req.valid || q_spp.io.deq.valid || q_sms.io.deq.valid) && fTable.io.req.ready)
//   XSPerfAccumulate("prefetcher_has_evict", io.evict.fire)
// }