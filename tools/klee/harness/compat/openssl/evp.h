// Declarations of the OpenSSL EVP digest calls of crypto/openssl/digest.hpp; harness/stubs.cpp
// defines them (a counter, not a real digest: see there).
#pragma once
#include <stddef.h>
#ifdef __cplusplus
extern "C" {
#endif
typedef struct evp_md_st EVP_MD;
typedef struct evp_md_ctx_st EVP_MD_CTX;
typedef struct engine_st ENGINE;
const EVP_MD* EVP_sha1(void);
const EVP_MD* EVP_sha256(void);
const EVP_MD* EVP_sha512(void);
const EVP_MD* EVP_blake2b512(void);  // vm/Hasher.cpp (HASHEXT, tonops)
int EVP_MD_CTX_size(const EVP_MD_CTX* ctx);
EVP_MD_CTX* EVP_MD_CTX_new(void);
void EVP_MD_CTX_free(EVP_MD_CTX* ctx);
#define EVP_MD_CTX_create() EVP_MD_CTX_new()
#define EVP_MD_CTX_destroy(ctx) EVP_MD_CTX_free((ctx))
int EVP_DigestInit_ex(EVP_MD_CTX* ctx, const EVP_MD* type, ENGINE* impl);
int EVP_MD_CTX_copy_ex(EVP_MD_CTX* out, const EVP_MD_CTX* in);
int EVP_DigestUpdate(EVP_MD_CTX* ctx, const void* d, size_t cnt);
int EVP_DigestFinal_ex(EVP_MD_CTX* ctx, unsigned char* md, unsigned int* s);
#ifdef __cplusplus
}
#endif
