// tdutils' config for tonops.cpp and tonops-stubs.cpp (tools/klee/build.sh, TONOPS=1): as
// td-config, but with TD_HAVE_OPENSSL, which crypto/Ed25519.h needs to declare td::Ed25519 (CHKSIGNU,
// CHKSIGNS). No OpenSSL code is compiled or linked: tonops-stubs.cpp defines what tonops calls.
#pragma once

#define TD_HAVE_OPENSSL 1
#define TD_HAVE_ZLIB 0
#define TD_HAVE_CRC32C 1
#define TD_HAVE_LZ4 0
#define TD_HAVE_ABSL 0
#define TD_FD_DEBUG 0
