// tdutils' generated config (td/utils/config.h.in) for the KLEE build: no OpenSSL in tdutils (the
// VM's digests come from crypto/openssl/digest.hpp, faked in stubs.cpp); crc32c from
// compat/crc32c (software).
#pragma once

#define TD_HAVE_OPENSSL 0
#define TD_HAVE_ZLIB 0
#define TD_HAVE_CRC32C 1
#define TD_HAVE_LZ4 0
#define TD_HAVE_ABSL 0
#define TD_FD_DEBUG 0
