// Stand-ins for the cryptography tonops.cpp calls (tools/klee/build.sh, TONOPS=1): Ed25519, P-256
// and secp256k1 signatures, ristretto255 (libsodium) and BLS12-381 (blst) are left out of the
// bitcode. Each stand-in decides from its input bytes (a signature, a point, a scalar) whether it
// succeeds, so that KLEE, with those bytes symbolic, takes the handler down both its success and
// its failure paths; what it returns is a fixed function of the input, not the group operation.
// The rule throughout: an input is "valid" when its first byte is even. The real C++ (fift, the
// oracle) decides with real cryptography: a KLEE case may take another handler path there.
#include <cstring>
#include <sodium.h>

#include "Ed25519.h"
#include "crypto/ellcurve/p256.h"
#include "crypto/ellcurve/secp256k1.h"
#include "td/utils/Status.h"
#include "vm/bls.h"

namespace {
bool ok_byte(const unsigned char* p) {
  return (p[0] & 1) == 0;
}
bool all_zero(const unsigned char* p, size_t n) {
  unsigned char a = 0;
  for (size_t i = 0; i < n; i++) {
    a |= p[i];
  }
  return a == 0;
}
template <class T>
bool ok_bits(const T& x) {
  return (x.data()[0] & 1) == 0;
}
template <class T>
T xor_of(const T& a, const T& b) {
  T r;
  for (size_t i = 0; i < sizeof(T); i++) {
    r.data()[i] = (unsigned char)(a.data()[i] ^ b.data()[i]);
  }
  r.data()[0] &= 0xfe;
  return r;
}
}  // namespace

namespace td {
Ed25519::PublicKey::PublicKey(SecureString octet_string) : octet_string_(std::move(octet_string)) {
}
Status Ed25519::PublicKey::verify_signature(Slice data, Slice signature) const {
  if (signature.size() > 0 && ok_byte(signature.ubegin())) {
    return Status::OK();
  }
  return Status::Error("invalid signature (stand-in)");
}
Status p256_check_signature(Slice data, Slice public_key, Slice signature) {
  if (signature.size() > 0 && ok_byte(signature.ubegin())) {
    return Status::OK();
  }
  return Status::Error("invalid signature (stand-in)");
}
namespace secp256k1 {
bool ecrecover(const unsigned char* hash, const unsigned char* signature, unsigned char* public_key) {
  if (!ok_byte(signature)) {
    return false;
  }
  public_key[0] = 4;
  std::memcpy(public_key + 1, hash, 32);
  std::memcpy(public_key + 33, signature, 32);
  return true;
}
bool xonly_pubkey_tweak_add(const unsigned char* xonly_pubkey_bytes, const unsigned char* tweak,
                            unsigned char* output_pubkey_bytes) {
  if (!ok_byte(xonly_pubkey_bytes)) {
    return false;
  }
  output_pubkey_bytes[0] = 4;
  std::memcpy(output_pubkey_bytes + 1, xonly_pubkey_bytes, 32);
  std::memcpy(output_pubkey_bytes + 33, tweak, 32);
  return true;
}
}  // namespace secp256k1
}  // namespace td

extern "C" {
int crypto_core_ristretto255_is_valid_point(const unsigned char* p) {
  return ok_byte(p) ? 1 : 0;
}
int crypto_core_ristretto255_from_hash(unsigned char* p, const unsigned char* r) {
  std::memcpy(p, r, 32);
  p[0] &= 0xfe;
  return 0;
}
static int rist_op(unsigned char* r, const unsigned char* p, const unsigned char* q) {
  if (!ok_byte(p) || !ok_byte(q)) {
    return -1;
  }
  for (int i = 0; i < 32; i++) {
    r[i] = (unsigned char)(p[i] ^ q[i]);
  }
  r[0] &= 0xfe;
  return 0;
}
int crypto_core_ristretto255_add(unsigned char* r, const unsigned char* p, const unsigned char* q) {
  return rist_op(r, p, q);
}
int crypto_core_ristretto255_sub(unsigned char* r, const unsigned char* p, const unsigned char* q) {
  return rist_op(r, p, q);
}
// libsodium: -1 for an invalid point and for the identity as the result (a zero scalar here)
int crypto_scalarmult_ristretto255(unsigned char* q, const unsigned char* n, const unsigned char* p) {
  if (all_zero(n, 32)) {
    return -1;
  }
  if (!ok_byte(p)) {
    return -1;
  }
  for (int i = 0; i < 32; i++) {
    q[i] = (unsigned char)(p[i] ^ n[i]);
  }
  q[0] &= 0xfe;
  return 0;
}
int crypto_scalarmult_ristretto255_base(unsigned char* q, const unsigned char* n) {
  if (all_zero(n, 32)) {
    return -1;
  }
  std::memcpy(q, n, 32);
  q[0] &= 0xfe;
  return 0;
}
}  // extern "C"

namespace vm {
namespace bls {
bool verify(const P1& pub, td::Slice msg, const P2& sig) {
  return ok_bits(sig);
}
P2 aggregate(const std::vector<P2>& sig) {
  P2 r = sig.empty() ? P2{} : sig[0];
  for (size_t i = 1; i < sig.size(); i++) {
    r = xor_of(r, sig[i]);
  }
  return r;
}
bool fast_aggregate_verify(const std::vector<P1>& pubs, td::Slice msg, const P2& sig) {
  return !pubs.empty() && ok_bits(sig);
}
bool aggregate_verify(const std::vector<std::pair<P1, td::BufferSlice>>& pubs_msgs, const P2& sig) {
  return !pubs_msgs.empty() && ok_bits(sig);
}
P1 g1_add(const P1& a, const P1& b) {
  return xor_of(a, b);
}
P1 g1_sub(const P1& a, const P1& b) {
  return xor_of(a, b);
}
P1 g1_neg(const P1& a) {
  return a;
}
P1 g1_mul(const P1& p, const td::RefInt256& x) {
  return p;
}
P1 g1_multiexp(const std::vector<std::pair<P1, td::RefInt256>>& ps) {
  P1 r = g1_zero();
  for (const auto& p : ps) {
    r = xor_of(r, p.first);
  }
  return r;
}
P1 g1_zero() {
  P1 r;
  r.set_zero();
  r.data()[0] = 0xc0;
  return r;
}
P1 map_to_g1(const FP& a) {
  P1 r;
  std::memcpy(r.data(), a.data(), FP_SIZE);
  r.data()[0] &= 0xfe;
  return r;
}
bool g1_in_group(const P1& a) {
  return ok_bits(a);
}
bool g1_is_zero(const P1& a) {
  return a == g1_zero();
}
P2 g2_add(const P2& a, const P2& b) {
  return xor_of(a, b);
}
P2 g2_sub(const P2& a, const P2& b) {
  return xor_of(a, b);
}
P2 g2_neg(const P2& a) {
  return a;
}
P2 g2_mul(const P2& p, const td::RefInt256& x) {
  return p;
}
P2 g2_multiexp(const std::vector<std::pair<P2, td::RefInt256>>& ps) {
  P2 r = g2_zero();
  for (const auto& p : ps) {
    r = xor_of(r, p.first);
  }
  return r;
}
P2 g2_zero() {
  P2 r;
  r.set_zero();
  r.data()[0] = 0xc0;
  return r;
}
P2 map_to_g2(const FP2& a) {
  P2 r;
  std::memcpy(r.data(), a.data(), 2 * FP_SIZE);
  r.data()[0] &= 0xfe;
  return r;
}
bool g2_in_group(const P2& a) {
  return ok_bits(a);
}
bool g2_is_zero(const P2& a) {
  return a == g2_zero();
}
bool pairing(const std::vector<std::pair<P1, P2>>& ps) {
  return ps.empty() || ok_bits(ps[0].first);
}
td::RefInt256 get_r() {  // the order of the BLS12-381 groups
  return td::hex_string_to_int256(td::Slice("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"));
}
}  // namespace bls
}  // namespace vm
