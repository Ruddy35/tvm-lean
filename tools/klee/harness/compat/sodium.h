// The libsodium calls of the VM: sodium_init() (vm.cpp, init_vm; stubs.cpp) and the ristretto255
// operations of tonops (RIST255_*; tonops-stubs.cpp: stand-ins, not the group operations).
#pragma once
#include <stddef.h>
#ifdef __cplusplus
extern "C" {
#endif
int sodium_init(void);
#define crypto_scalarmult_ristretto255_BYTES 32U
#define crypto_scalarmult_ristretto255_SCALARBYTES 32U
#define crypto_core_ristretto255_BYTES 32U
#define crypto_core_ristretto255_HASHBYTES 64U
#define crypto_core_ristretto255_SCALARBYTES 32U
#define crypto_core_ristretto255_NONREDUCEDSCALARBYTES 64U
int crypto_core_ristretto255_is_valid_point(const unsigned char* p);
int crypto_core_ristretto255_from_hash(unsigned char* p, const unsigned char* r);
int crypto_core_ristretto255_add(unsigned char* r, const unsigned char* p, const unsigned char* q);
int crypto_core_ristretto255_sub(unsigned char* r, const unsigned char* p, const unsigned char* q);
int crypto_scalarmult_ristretto255(unsigned char* q, const unsigned char* n, const unsigned char* p);
int crypto_scalarmult_ristretto255_base(unsigned char* q, const unsigned char* n);
#ifdef __cplusplus
}
#endif
