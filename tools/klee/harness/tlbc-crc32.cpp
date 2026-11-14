// td::crc32 for tlbc (tools/klee/build.sh builds tlbc to generate block-auto.cpp/h for tonops):
// tdutils takes it from zlib, which the build does not use. CRC-32 (IEEE 802.3, reflected,
// polynomial 0xEDB88320), as zlib's crc32(0, data, size): tlbc derives constructor tags from it.
#include "td/utils/Slice.h"
#include "td/utils/int_types.h"

namespace td {
uint32 crc32(Slice data) {
  uint32 c = 0xFFFFFFFFu;
  for (unsigned char b : data) {
    c ^= b;
    for (int k = 0; k < 8; k++) {
      c = (c >> 1) ^ (0xEDB88320u & (0u - (c & 1u)));
    }
  }
  return c ^ 0xFFFFFFFFu;
}
}  // namespace td
