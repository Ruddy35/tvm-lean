// Stand-ins for what the KLEE build of the C++ TVM leaves out (tools/klee/build.sh).
//
// Digests. The VM hashes every cell it creates (DataCell, via crypto/openssl/digest.hpp ->
// OpenSSL SHA256_* / EVP_*). Real SHA-256 over symbolic cell data would swamp the solver and is
// checked elsewhere, so a digest here is a per-process counter: every hash computation returns a
// fresh 32-byte value. Consequence: two distinct cells with equal contents get distinct hashes,
// unlike the real VM (relevant only where the VM compares hashes: the reload price of a cell
// loaded twice, HASHCU and the like; none of the pilot handlers).
//
// tonops (TON-specific opcodes: crypto, config, messages) is not compiled: register_ton_ops
// registers nothing. sodium_init is the VM's only libsodium call.
#include <openssl/evp.h>
#include <openssl/sha.h>

#include <cstdlib>
#include <cstring>

#include "vm/opctable.h"

namespace {
unsigned long long g_digest_counter = 0;

void fake_digest(unsigned char* out, unsigned len) {
  unsigned long long v = ++g_digest_counter;
  std::memset(out, 0, len);
  for (unsigned i = 0; i < 8 && i < len; i++) {
    out[i] = (unsigned char)(v >> (8 * i));
  }
  if (len > 8) {
    out[len - 1] = 0xa5;  // not all-zero: a zero hash means "no hash" in places
  }
}

struct FakeMdCtx {
  int bytes;
};
struct FakeMd {
  int bytes;
};
const FakeMd md_sha1{20}, md_sha256{32}, md_sha512{64};
}  // namespace

namespace vm {
void register_ton_ops(OpcodeTable&) {
}
}  // namespace vm

extern "C" {

int sodium_init(void) {
  return 0;
}

int SHA256_Init(SHA256_CTX* c) {
  std::memset(c, 0, sizeof(*c));
  return 1;
}
int SHA256_Update(SHA256_CTX*, const void*, size_t) {
  return 1;
}
int SHA256_Final(unsigned char* md, SHA256_CTX*) {
  fake_digest(md, 32);
  return 1;
}
unsigned char* SHA256(const unsigned char*, size_t, unsigned char* md) {
  fake_digest(md, 32);
  return md;
}

const EVP_MD* EVP_sha1(void) {
  return reinterpret_cast<const EVP_MD*>(&md_sha1);
}
const EVP_MD* EVP_sha256(void) {
  return reinterpret_cast<const EVP_MD*>(&md_sha256);
}
const EVP_MD* EVP_sha512(void) {
  return reinterpret_cast<const EVP_MD*>(&md_sha512);
}
EVP_MD_CTX* EVP_MD_CTX_new(void) {
  auto* c = static_cast<FakeMdCtx*>(std::calloc(1, sizeof(FakeMdCtx)));
  return reinterpret_cast<EVP_MD_CTX*>(c);
}
void EVP_MD_CTX_free(EVP_MD_CTX* c) {
  std::free(c);
}
int EVP_DigestInit_ex(EVP_MD_CTX* c, const EVP_MD* md, ENGINE*) {
  reinterpret_cast<FakeMdCtx*>(c)->bytes = md ? reinterpret_cast<const FakeMd*>(md)->bytes : 32;
  return 1;
}
int EVP_MD_CTX_copy_ex(EVP_MD_CTX* out, const EVP_MD_CTX* in) {
  *reinterpret_cast<FakeMdCtx*>(out) = *reinterpret_cast<const FakeMdCtx*>(in);
  return 1;
}
int EVP_DigestUpdate(EVP_MD_CTX*, const void*, size_t) {
  return 1;
}
int EVP_DigestFinal_ex(EVP_MD_CTX* c, unsigned char* md, unsigned int* s) {
  int n = reinterpret_cast<FakeMdCtx*>(c)->bytes;
  fake_digest(md, (unsigned)n);
  if (s) {
    *s = (unsigned)n;
  }
  return 1;
}

}  // extern "C"
