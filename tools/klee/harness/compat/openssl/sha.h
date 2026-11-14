// Declarations of the OpenSSL digest calls of crypto/openssl/digest.hpp; harness/stubs.cpp defines
// them (a counter, not SHA-256: see there).
#pragma once
#include <stddef.h>
#ifdef __cplusplus
extern "C" {
#endif
typedef unsigned int SHA_LONG;
typedef struct SHA256state_st {
  SHA_LONG h[8];
  SHA_LONG Nl, Nh;
  SHA_LONG data[16];
  unsigned int num, md_len;
} SHA256_CTX;
#define SHA256_DIGEST_LENGTH 32
int SHA256_Init(SHA256_CTX* c);
int SHA256_Update(SHA256_CTX* c, const void* data, size_t len);
int SHA256_Final(unsigned char* md, SHA256_CTX* c);
unsigned char* SHA256(const unsigned char* d, size_t n, unsigned char* md);
#ifdef __cplusplus
}
#endif
