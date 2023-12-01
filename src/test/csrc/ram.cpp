#include <stdio.h>
#ifdef __cplusplus
#include <map>
#include <unordered_map>
#endif

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