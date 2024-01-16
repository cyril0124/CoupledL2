#include <stdio.h>
#ifdef __cplusplus
#include <map>
#include <unordered_map>
#endif

#include <cassert>

typedef uint64_t paddr_t;

// std::unordered_map<paddr_t, uint64_t> mem;
std::map<paddr_t, uint64_t> mem;


uint64_t _ram_read(uint64_t rIdx) {
  uint64_t rdata = 0;
  rdata = mem[rIdx];
  return rdata;
}

extern "C" uint64_t ram_read_helper(uint8_t en, uint64_t rIdx) {
  if (!en)
    return 0;
  // printf("read idx:0x%lx\n", rIdx);
  return _ram_read(rIdx);
}

void _ram_write(uint64_t wIdx, uint64_t wdata, uint64_t wmask) {
  mem[wIdx] = (mem[wIdx] & ~wmask) | (wdata & wmask);
}

extern "C" void ram_write_helper(uint64_t wIdx, uint64_t wdata, uint64_t wmask, uint8_t wen) {
  if (wen) {
    _ram_write(wIdx, wdata, wmask);
  }
}

#ifdef WITH_DRAMSIM3
#include "cosimulation.h"
CoDRAMsim3 *dram = NULL;

struct dramsim3_meta {
  uint32_t id;
};

extern "C" {
void dramsim3_init() {
#if !defined(DRAMSIM3_CONFIG) || !defined(DRAMSIM3_OUTDIR)
  #error DRAMSIM3_CONFIG or DRAMSIM3_OUTDIR is not defined
#endif
  assert(dram == NULL);
  dram = new ComplexCoDRAMsim3(DRAMSIM3_CONFIG, DRAMSIM3_OUTDIR);
  // dram = new SimpleCoDRAMsim3(90);
}

void dramsim3_step() {
  dram->tick();
}

void dramsim3_finish() {
  printf("enter dramsim3_finish()\n");
  delete dram;
  dram = NULL;
}


uint64_t memory_response(bool isWrite) {
  auto response = (isWrite) ? dram->check_write_response() : dram->check_read_response();
  if (response) {
    auto meta = static_cast<dramsim3_meta *>(response->req->meta);
    uint64_t response_value = meta->id | (1UL << 32);
    delete meta;
    delete response;
    return response_value;
  }
  return 0;
}

bool memory_request(uint64_t address, uint32_t id, bool isWrite) {
  if (dram->will_accept(address, isWrite)) {
    auto req = new CoDRAMRequest();
    auto meta = new dramsim3_meta;
    req->address = address;
    req->is_write = isWrite;
    meta->id = id;
    req->meta = meta;
    dram->add_request(req);
    return true;
  }
  return false;
}
}


#endif