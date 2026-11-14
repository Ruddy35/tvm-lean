// The two calls tdutils makes into google/crc32c (td/utils/crypto.cpp), in software: CRC-32C
// (Castagnoli, reflected polynomial 0x82f63b78), as BOC parsing checks it.
#pragma once
#include <cstddef>
#include <cstdint>

namespace crc32c {
inline uint32_t Extend(uint32_t crc, const uint8_t* data, size_t n) {
  crc = ~crc;
  for (size_t i = 0; i < n; i++) {
    crc ^= data[i];
    for (int k = 0; k < 8; k++) {
      crc = (crc >> 1) ^ (0x82f63b78u & (0u - (crc & 1u)));
    }
  }
  return ~crc;
}
inline uint32_t Crc32c(const char* data, size_t n) {
  return Extend(0, reinterpret_cast<const uint8_t*>(data), n);
}
inline uint32_t Crc32c(const uint8_t* data, size_t n) {
  return Extend(0, data, n);
}
}  // namespace crc32c
