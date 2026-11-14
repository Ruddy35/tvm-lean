// KLEE harness for the C++ TVM of the reference (ton @ 3d478cb): one instruction, run through the
// real dispatch (VmState::run on a one-instruction code cell), on a symbolic input of bounded
// shape. Built twice (tools/klee/build.sh):
//
//  * TVM_KLEE_SYMBOLIC: the KLEE entry point. `klee ... harness.bc <SPEC>` explores every
//    feasible path of the instruction family <SPEC> (table `kSpecs` below) and writes one .ktest
//    per path.
//  * TVM_KLEE_NATIVE: the replay binary `replay`, linked natively from the same instrumented TON
//    bitcode.
//      replay ktest <SPEC> <file.ktest>...  rebuild each test's input (the same code as under
//          KLEE, the values read from the .ktest), run it, check the path signature against the
//          one KLEE recorded, print the case: id, signature, version, gas, code BOC, stack tokens
//      replay cases <SPEC> <cases.tsv>      run cases given as code BOC + oracle stack tokens
//          (from the Lean dumper or from `replay ktest`), print the signature of every execution
//          of <SPEC>'s opcodes in each
//
// Input shape: the global version (0..16, symbolic), the gas limit (0..400 symbolic, or 10^6;
// `<SPEC>+G`: 10^6 only), one of the spec's opcodes with its immediate arguments (enumerated: each
// a path of its own), the stack depth (one of the spec's depths) and every stack entry the
// instruction can read: its type from the spec's set, an integer of one of the spec's shapes
// (symbolic int16, int64, +-2^k+d near the word and 257-bit bounds, any 257-bit value; NaN; for
// stack indices, bit widths and key lengths one of a list of values around their bounds), a
// cell/slice/builder of a bit length from a set of boundary lengths with symbolic bits and 0/1/3/4
// references, a dictionary from a few concrete ones. Entries below the ones the spec lists are
// concrete integers.
//
// Path signature: every basic block of the TON code calls tvm_cov(id) (cov_instrument.py).
// VmState::step() calls tvm_klee_step_hook() first, and the step ends (tvm_klee_step_end) after
// the gas check that follows it in run_inner or where run_inner/run catch what it threw. Over a
// step that starts with one of the spec's opcodes the block ids are hashed: the C++ path of that
// execution of the instruction (dispatch, handler, the throw if any, the gas check), not of the
// VM's generic exception handling after it. Two hashes: of the block sequence (the exact path)
// and of the set of block-to-block edges (the path up to loop iteration counts, the one compared
// with the existing suites). Under KLEE the harness ends by constraining symbolic `sig` and
// `esig` to them, so each .ktest carries the signatures of its path.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <functional>
#include <memory>
#include <vector>
#include <unistd.h>
#ifdef TVM_KLEE_NATIVE
#include <sys/wait.h>
#endif

#include "common/refint.h"
#include "td/utils/misc.h"
#include "vm/boc.h"
#include "vm/continuation.h"
#include "vm/cp0.h"
#include "vm/dict.h"
#include "vm/stack.hpp"
#include "vm/vm.h"

using td::Ref;
using td::RefInt256;

// ---------------------------------------------------------------- symbolic inputs
#ifdef TVM_KLEE_SYMBOLIC
extern "C" {
void klee_make_symbolic(void* addr, size_t nbytes, const char* name);
void klee_assume(uintptr_t condition);
__attribute__((noreturn)) void klee_silent_exit(int status);
}
#else
namespace replay {
struct Obj {
  std::string name;
  std::vector<unsigned char> bytes;
};
std::vector<Obj> objs;
size_t next_obj = 0;
bool bad = false;
std::string why;

bool load_ktest(const char* path) {
  objs.clear();
  next_obj = 0;
  bad = false;
  why.clear();
  FILE* f = std::fopen(path, "rb");
  if (!f) {
    return false;
  }
  auto u32 = [&](unsigned& v) {
    unsigned char b[4];
    if (std::fread(b, 1, 4, f) != 4) return false;
    v = (unsigned)b[0] << 24 | (unsigned)b[1] << 16 | (unsigned)b[2] << 8 | b[3];
    return true;
  };
  auto blob = [&](std::vector<unsigned char>& out) {
    unsigned n;
    if (!u32(n)) return false;
    out.resize(n);
    return n == 0 || std::fread(out.data(), 1, n, f) == n;
  };
  char magic[5];
  unsigned version, nargs, nobjs, x;
  bool ok = std::fread(magic, 1, 5, f) == 5 && u32(version) && u32(nargs);
  for (unsigned i = 0; ok && i < nargs; i++) {
    std::vector<unsigned char> a;
    ok = blob(a);
  }
  if (ok && version >= 2) {
    ok = u32(x) && u32(x);
  }
  ok = ok && u32(nobjs);
  for (unsigned i = 0; ok && i < nobjs; i++) {
    Obj o;
    std::vector<unsigned char> nm;
    ok = blob(nm) && blob(o.bytes);
    o.name.assign(nm.begin(), nm.end());
    objs.push_back(std::move(o));
  }
  std::fclose(f);
  return ok;
}
}  // namespace replay

struct SilentExit {};
extern "C" {
// Objects are matched by position and size, not by name: KLEE writes a test's object names from
// the memory objects, and a stack slot the optimizer reuses for several klee_make_symbolic calls
// (sym<T>'s local in a loop) carries the last name given to it, while the values stay distinct.
void klee_make_symbolic(void* addr, size_t nbytes, const char* name) {
  using namespace replay;
  if (next_obj >= objs.size() || objs[next_obj].bytes.size() != nbytes) {
    if (!bad) {
      why = std::string("object mismatch at ") + name;
    }
    bad = true;
    std::memset(addr, 0, nbytes);
    return;
  }
  std::memcpy(addr, objs[next_obj].bytes.data(), nbytes);
  next_obj++;
}
void klee_assume(uintptr_t condition) {
  if (!condition) {
    if (!replay::bad) {
      replay::why = "assumption violated";
    }
    replay::bad = true;
  }
}
__attribute__((noreturn)) void klee_silent_exit(int) {
  throw SilentExit{};
}
}
#endif

template <class T>
static T sym(const char* name) {
  T v;
  klee_make_symbolic(&v, sizeof(v), name);
  return v;
}

static int sym_range(int lo, int hi, const char* name) {
  int v = sym<int>(name);
  klee_assume((v >= lo) & (v <= hi));
  return v;
}

// one of `vals`, concrete on each path (KLEE forks once per value), chosen bit by bit: log2(n)
// forks deep with small solver queries, not a chain of n comparisons
static int pick(const int* vals, int n, const char* name) {
  int i = sym_range(0, n - 1, name);
  volatile int r = 0;  // volatile: a branch per bit, not a select the optimizer folds back into i
  for (int b = 30; b >= 0; b--) {
    if ((n - 1) >> b) {
      if (i & (1 << b)) {
        r = r | (1 << b);
      }
    }
  }
  return vals[r];
}

// ---------------------------------------------------------------- path signature
static bool g_rec = false;
struct Sig {
  uint64_t seq;    // hash of the sequence of blocks: the exact path
  uint64_t edges;  // hash of the set of block-to-block edges: the path up to loop iteration counts
};
static Sig g_sig;
static std::vector<Sig> g_sigs;
static uint32_t g_prev;

// the window's edge set: open addressing, cleared by bumping the generation
constexpr unsigned kEdgeSlots = 4096;
static uint64_t g_edge_key[kEdgeSlots];
static uint32_t g_edge_gen[kEdgeSlots];
static uint32_t g_gen = 0;
static unsigned g_edge_count = 0;

static inline uint64_t mix64(uint64_t x) {
  x ^= x >> 33;
  x *= 0xff51afd7ed558ccdULL;
  x ^= x >> 33;
  x *= 0xc4ceb9fe1a85ec53ULL;
  x ^= x >> 33;
  return x;
}

struct Alt {
  unsigned lo, hi;  // opcode range (inclusive), as a `bits`-bit number
  int bits;
  // every opcode of the range concrete, one path each: symbolic opcode bits make the dispatch's
  // binary search (compiled to selects) a symbolic index into the whole opcode table
  bool enumerate = true;
};
static const std::vector<Alt>* g_target = nullptr;

extern "C" void tvm_cov(uint32_t id) {
  if (!g_rec) {
    return;
  }
  g_sig.seq = (g_sig.seq ^ id) * 0x100000001b3ULL;
  uint64_t e = ((uint64_t)g_prev << 32) | id;
  g_prev = id;
  if (g_edge_count >= kEdgeSlots / 2) {  // more distinct edges than a handler has: fold the rest in
    g_sig.edges ^= mix64(e ^ 0x5bd1e995);
    return;
  }
  unsigned h = (unsigned)mix64(e) & (kEdgeSlots - 1);
  while (g_edge_gen[h] == g_gen) {
    if (g_edge_key[h] == e) {
      return;
    }
    h = (h + 1) & (kEdgeSlots - 1);
  }
  g_edge_gen[h] = g_gen;
  g_edge_key[h] = e;
  g_edge_count++;
  g_sig.edges += mix64(e);
}

static bool code_matches(const vm::CellSlice& cs) {
  if (!g_target) {
    return false;
  }
  for (const Alt& a : *g_target) {
    if (cs.size() >= (unsigned)a.bits) {
      unsigned long long v = cs.prefetch_ulong(a.bits);
      if (v >= a.lo && v <= a.hi) {
        return true;
      }
    }
  }
  return false;
}

static void end_windows() {
  if (g_rec) {
    g_sigs.push_back(g_sig);
    g_rec = false;
  }
}

extern "C" void tvm_klee_step_end() {
  end_windows();
}

extern "C" void tvm_klee_step_hook(const vm::CellSlice* code) {
  end_windows();
  if (code && code_matches(*code)) {
    g_rec = true;
    g_sig = {0xcbf29ce484222325ULL, 0};
    g_prev = 0;
    g_gen++;
    g_edge_count = 0;
  }
}

// ---------------------------------------------------------------- specs
enum Kind : unsigned { K_INT = 1, K_NULL = 2, K_CELL = 4, K_SLICE = 8, K_BUILDER = 16, K_TUPLE = 32, K_CONT = 64, K_DICT = 128 };
enum Shape : unsigned { S_SMALL = 1, S_I64 = 2, S_BIG = 4, S_FULL = 8, S_NAN = 16, S_ENUM = 32, S_WIDTH = 64 };
constexpr unsigned S_ALL = S_SMALL | S_I64 | S_BIG | S_FULL | S_NAN;
constexpr unsigned S_NOFULL = S_SMALL | S_I64 | S_BIG | S_NAN;
constexpr unsigned S_COUNT = S_SMALL | S_NAN;  // a count no stack access depends on (CHKDEPTH)
// Stack positions: a symbolic index into the stack makes every later access of the stack a
// symbolic-pointer resolution and the solver the bottleneck (XCHG s(i),s(j) did 8 paths in 17
// minutes). Operands and arguments that index the stack are enumerated instead: every value
// around the stack depths of the spec, and the bounds of the range checks.
constexpr unsigned S_INDEX = S_ENUM | S_NAN;
// Bit widths and key lengths from the stack: a symbolic width makes every bit access of a slice a
// symbolic-offset read of its data (LDIX, DICTGET: a few paths in 15 minutes); enumerated likewise.
constexpr unsigned S_WIDTHS = S_WIDTH | S_NAN;

struct SlotSpec {
  unsigned kinds;
  unsigned shapes;
};

struct Spec {
  const char* name;
  std::vector<Alt> alts;
  std::vector<int> depths;  // the stack depths tried (each a path of its own)
  std::vector<SlotSpec> slots;  // slots[i]: stack entry s(i) (s0 = top)
};

static std::vector<int> upto(int n) {
  std::vector<int> v;
  for (int d = 0; d <= n; d++) {
    v.push_back(d);
  }
  return v;
}

// The MULRSHIFT family: the shift amount from the stack (0xa9ax, quiet 0xb7a9ax: the 4-bit mode
// enumerated) or in the opcode (0xa9b + mode:4 + (amount-1):8): every mode with the amounts 1, 2,
// 52, 64, 255 and 256.
static std::vector<Alt> mulshr_alts() {
  std::vector<Alt> v{{0xa9a0, 0xa9af, 16, true}, {0xb7a9a0, 0xb7a9af, 24, true}};
  for (unsigned mode = 0; mode < 16; mode++) {
    for (unsigned z : {1, 2, 52, 64, 255, 256}) {
      unsigned op = 0xa9b000 | (mode << 8) | (z - 1);
      v.push_back({op, op, 24});
    }
  }
  return v;
}

static const std::vector<Spec> kSpecs = {
    // stack
    // (depths: each side of every bound the arguments can set)
    {"XCHG_IJ", {{0x1000, 0x10ff, 16, true}}, {0, 1, 2, 15, 16}, {}},
    {"BLKSWAP", {{0x5500, 0x55ff, 16, true}}, {0, 2, 31, 32}, {}},
    {"ROLLX", {{0x61, 0x61, 8}}, upto(12), {{K_INT | K_NULL, S_INDEX}}},
    {"BLKSWX", {{0x63, 0x63, 8}}, {0, 1, 2, 3, 6, 12}, {{K_INT | K_NULL, S_INDEX}, {K_INT | K_NULL, S_INDEX}}},
    {"CHKDEPTH", {{0x69, 0x69, 8}}, upto(10), {{K_INT | K_NULL, S_COUNT}}},
    // arithmetic (with the quiet forms)
    {"ADD", {{0xa0, 0xa0, 8}, {0xb7a0, 0xb7a0, 16}}, upto(2), {{K_INT | K_NULL, S_ALL}, {K_INT | K_NULL, S_ALL}}},
    {"MUL", {{0xa8, 0xa8, 8}, {0xb7a8, 0xb7a8, 16}}, upto(2), {{K_INT | K_NULL, S_NOFULL}, {K_INT | K_NULL, S_NOFULL}}},
    {"MULDIVMOD",
     {{0xa980, 0xa98f, 16}, {0xb7a980, 0xb7a98f, 24}},
     upto(4),
     {{K_INT | K_NULL, S_NOFULL}, {K_INT, S_NOFULL}, {K_INT, S_NOFULL}, {K_INT, S_NOFULL}}},
    // shift amounts as widths (a symbolic shift amount: the solver bottleneck); s0 is the amount of
    // MULRSHIFT with it from the stack, an operand of the forms with it in the opcode
    {"MULSHRMOD", mulshr_alts(), upto(4),
     {{K_INT | K_NULL, S_WIDTHS | S_I64 | S_BIG}, {K_INT, S_NOFULL}, {K_INT, S_NOFULL}, {K_INT, S_NOFULL}}},
    // LSHIFT/RSHIFT and their quiet forms are four entries of the opcode table: enumerated (a
    // symbolic choice between entries is a symbolic read of the whole table)
    {"SHIFTX",
     {{0xac, 0xad, 8, true}, {0xb7ac, 0xb7ad, 16, true}},
     upto(2),
     {{K_INT | K_NULL, S_WIDTHS | S_I64}, {K_INT | K_NULL, S_ALL}}},
    // cells, slices, builders
    {"STIX", {{0xcf00, 0xcf07, 16}}, upto(3),
     {{K_INT | K_NULL, S_WIDTHS}, {K_INT | K_BUILDER, S_ALL}, {K_INT | K_BUILDER, S_ALL}}},
    {"LDIX", {{0xd700, 0xd707, 16}}, upto(2), {{K_INT | K_NULL, S_WIDTHS}, {K_SLICE | K_NULL, 0}}},
    {"STSLICE",
     {{0xce, 0xce, 8}, {0xcf12, 0xcf12, 16}, {0xcf16, 0xcf16, 16}, {0xcf1a, 0xcf1a, 16}, {0xcf1e, 0xcf1e, 16}},
     upto(2),
     {{K_SLICE | K_BUILDER | K_NULL, 0}, {K_SLICE | K_BUILDER | K_NULL, 0}}},
    // dictionaries
    {"DICTGET", {{0xf40a, 0xf40f, 16}}, upto(3),
     {{K_INT | K_NULL, S_WIDTHS}, {K_DICT | K_NULL | K_SLICE, 0}, {K_INT | K_SLICE | K_NULL, S_SMALL | S_I64 | S_NAN}}},
};

// "<SPEC>+G": the same family with the large gas limit only. Depth-first, KLEE spends its time on
// the first subtree it enters; with the small limits first, a family whose operands make many
// input combinations (MULDIVMOD, DICTGET) stays among the out-of-gas paths for the whole run.
static bool g_big_gas_only = false;

static const Spec* find_spec(const char* name) {
  std::string n = name;
  if (n.size() > 2 && n.compare(n.size() - 2, 2, "+G") == 0) {
    g_big_gas_only = true;
    n.resize(n.size() - 2);
  }
  for (const Spec& s : kSpecs) {
    if (n == s.name) {
      return &s;
    }
  }
  return nullptr;
}

// ---------------------------------------------------------------- input construction
static const int kCellLens[] = {0, 1, 7, 8, 9, 64, 255, 256, 257, 1023};
static const int kBuilderLens[] = {0, 1, 7, 8, 9, 766, 767, 768, 1015, 1022, 1023};
static const int kRefCounts[] = {0, 1, 3, 4};
static const int kPow2[] = {51, 52, 63, 64, 128, 255, 256};

static Ref<vm::Cell> ref_cell(int i) {
  vm::CellBuilder cb;
  cb.store_long(i, 8);
  return cb.finalize();
}

static void fill(vm::CellBuilder& cb, const char* tag, const int* lens, int nlens) {
  std::string t(tag);
  int len = pick(lens, nlens, (t + ".len").c_str());
  int nrefs = pick(kRefCounts, 4, (t + ".refs").c_str());
  if (len > 0) {
    // an object of its own, of the exact size: KLEE makes whole objects symbolic
    std::unique_ptr<unsigned char[]> data{new unsigned char[(len + 7) / 8]};
    klee_make_symbolic(data.get(), (len + 7) / 8, (t + ".bits").c_str());
    cb.store_bits(data.get(), len);
  }
  for (int i = 0; i < nrefs; i++) {
    cb.store_ref(ref_cell(i));
  }
}

static RefInt256 make_int(const std::string& t, unsigned shapes, bool& nan) {
  int opts[7], n = 0;
  for (unsigned s : {S_SMALL, S_I64, S_BIG, S_FULL, S_NAN, S_ENUM, S_WIDTH}) {
    if (shapes & s) {
      opts[n++] = (int)s;
    }
  }
  int shape = pick(opts, n, (t + ".shape").c_str());
  switch (shape) {
    case S_ENUM: {  // stack positions and counts: around the depths, the range bounds (255, 2^30-1)
      static const int kIndexVals[] = {-1, 0,   1,   2,   3,      5,     6,          11,
                                       12, 13,  255, 256, 257,    -32768, 32767,     (1 << 30) - 1,
                                       1 << 30};
      return td::make_refint(pick(kIndexVals, sizeof(kIndexVals) / sizeof(int), (t + ".enum").c_str()));
    }
    case S_WIDTH: {  // bit widths and key lengths: each side of the byte, word and range bounds
      static const int kWidthVals[] = {-1, 0, 1, 3, 4, 5, 7, 8, 9, 63, 64, 65, 255, 256, 257, 258, 1023, 1024};
      return td::make_refint(pick(kWidthVals, sizeof(kWidthVals) / sizeof(int), (t + ".width").c_str()));
    }
    case S_SMALL:
      return td::make_refint((long long)sym<int16_t>((t + ".i16").c_str()));
    case S_I64:
      return td::make_refint((long long)sym<int64_t>((t + ".i64").c_str()));
    case S_BIG: {
      int k = pick(kPow2, sizeof(kPow2) / sizeof(kPow2[0]), (t + ".k").c_str());
      int neg = sym_range(0, 1, (t + ".neg").c_str());
      long long d = sym<int16_t>((t + ".d").c_str());
      RefInt256 x = td::make_refint(1) << k;
      if (neg) {
        x = -x;
      }
      x += td::make_refint(d);
      if (!x->signed_fits_bits(257)) {
        klee_silent_exit(0);
      }
      return x;
    }
    case S_FULL: {
      unsigned char b[33];
      klee_make_symbolic(b, sizeof(b), (t + ".i257").c_str());
      klee_assume((b[0] == 0) | (b[0] == 0xff));
      RefInt256 x{true};
      x.write().import_bytes(b, sizeof(b), true);
      return x;
    }
    default:
      nan = true;
      return td::nan_refint();
  }
}

static Ref<vm::Cell> make_dict(const std::string& t) {
  // concrete dictionaries with 4-bit keys: slice values, cell values, one-entry
  int which = sym_range(0, 2, (t + ".dict").c_str());
  vm::Dictionary dict{4};
  unsigned char key[1];
  if (which == 0) {
    for (int k : {0x0, 0x5, 0x6, 0xf}) {
      key[0] = (unsigned char)(k << 4);
      vm::CellBuilder cb;
      cb.store_long(0x100 + k, 12);
      dict.set(td::ConstBitPtr{key}, 4, vm::load_cell_slice_ref(cb.finalize()));
    }
  } else if (which == 1) {
    for (int k : {0x3, 0xc}) {
      key[0] = (unsigned char)(k << 4);
      dict.set_ref(td::ConstBitPtr{key}, 4, ref_cell(k));
    }
  } else {
    key[0] = 0xa0;
    vm::CellBuilder cb;
    cb.store_long(0x7, 3);
    dict.set(td::ConstBitPtr{key}, 4, vm::load_cell_slice_ref(cb.finalize()));
  }
  return dict.get_root_cell();
}

struct Input {
  int version = 16;
  long long gas = 1000000;
  Ref<vm::Cell> code;
  std::vector<vm::StackEntry> stack;  // bottom first
};

static vm::StackEntry make_entry(const std::string& t, const SlotSpec& sp, bool& nan) {
  int opts[8], n = 0;
  for (unsigned k : {K_INT, K_NULL, K_CELL, K_SLICE, K_BUILDER, K_TUPLE, K_CONT, K_DICT}) {
    if (sp.kinds & k) {
      opts[n++] = (int)k;
    }
  }
  int kind = pick(opts, n, (t + ".kind").c_str());
  switch (kind) {
    case K_INT:
      return make_int(t, sp.shapes, nan);
    case K_NULL:
      return vm::StackEntry{};
    case K_CELL: {
      vm::CellBuilder cb;
      fill(cb, t.c_str(), kCellLens, sizeof(kCellLens) / sizeof(int));
      return Ref<vm::Cell>{cb.finalize()};
    }
    case K_SLICE: {
      vm::CellBuilder cb;
      fill(cb, t.c_str(), kCellLens, sizeof(kCellLens) / sizeof(int));
      return vm::load_cell_slice_ref(cb.finalize());
    }
    case K_BUILDER: {
      Ref<vm::CellBuilder> b{true};
      fill(b.write(), t.c_str(), kBuilderLens, sizeof(kBuilderLens) / sizeof(int));
      return b;
    }
    case K_TUPLE:
      return vm::StackEntry{Ref<vm::Tuple>{true}};
    case K_CONT:
      return vm::StackEntry{Ref<vm::Continuation>{Ref<vm::QuitCont>{true, 0}}};
    default:
      return make_dict(t);
  }
}

static Input make_input(const Spec& spec) {
  Input in;
  in.version = sym_range(0, 16, "version");
  bool small_gas = !g_big_gas_only && !sym_range(0, 1, "gas.big");
  if (small_gas) {
    in.gas = sym_range(0, 400, "gas");
  }
  // The entries the instruction reads first, then the opcode and the stack depth: depth-first,
  // KLEE varies the last choices fastest, so a run cut by its time limit has tried every opcode
  // and depth on the entries it got to, instead of every entry on the first opcode and depth.
  std::vector<vm::StackEntry> entries(spec.slots.size());
  std::vector<bool> nans(spec.slots.size());
  for (int i = (int)spec.slots.size() - 1; i >= 0; i--) {
    bool nan = false;
    entries[i] = make_entry("s" + std::to_string(i), spec.slots[i], nan);
    nans[i] = nan;
  }
  int ai = 0;
  if (spec.alts.size() > 1) {
    std::vector<int> idx;
    for (size_t i = 0; i < spec.alts.size(); i++) {
      idx.push_back((int)i);
    }
    ai = pick(idx.data(), (int)idx.size(), "alt");
  }
  const Alt& a = spec.alts[ai];
  unsigned op = a.lo;
  if (a.hi > a.lo && a.enumerate) {
    std::vector<int> ops;
    for (unsigned v = a.lo; v <= a.hi; v++) {
      ops.push_back((int)v);
    }
    op = (unsigned)pick(ops.data(), (int)ops.size(), "opcode");
  } else if (a.hi > a.lo) {
    op = sym<unsigned>("opcode");
    klee_assume((op >= a.lo) & (op <= a.hi));
  }
  vm::CellBuilder cb;
  cb.store_long(op, a.bits);
  in.code = cb.finalize();
  int depth = pick(spec.depths.data(), (int)spec.depths.size(), "depth");
  bool nan = false;
  for (int i = depth - 1; i >= 0; i--) {
    if (i < (int)spec.slots.size()) {
      in.stack.push_back(entries[i]);
      nan = nan || nans[i];
    } else {
      in.stack.push_back(td::make_refint(1000 + i));
    }
  }
  // NaN reaches the oracle through a code prelude (Tests/Harness/OracleHarness.lean) that costs
  // gas: NaN inputs run with the large limit only (Input's default).
  if (nan && small_gas) {
    klee_silent_exit(0);
  }
  return in;
}

// The first cell and builder initialize function-local statics of TON (td's thread-safe counters,
// CellBuilder.h and DataCell.h: some 10^8 KLEE instructions of memset). Done before any symbolic
// input, they are paid once, not on every path.
static void warm_up() {
  vm::CellBuilder cb;
  cb.store_long(1, 8);
  Ref<vm::Cell> c = cb.finalize();
  Ref<vm::CellSlice> cs = vm::load_cell_slice_ref(c);
  Ref<vm::CellBuilder> b{true};
  b.write().append_cellslice(*cs);
}

static int run_vm(const Input& in) {
  Ref<vm::Stack> stack{true};
  for (const auto& e : in.stack) {
    stack.write().push(e);
  }
  Ref<vm::CellSlice> code{true, vm::NoVmOrd(), in.code};
  // never destroyed: under KLEE the path ends right after the run (_exit), and tearing the VM
  // down would only cost time; the replay process ends too
  auto* st = new vm::VmState{code, in.version, std::move(stack), vm::GasLimits{in.gas, in.gas}, 0,
                             vm::CellBuilder{}.finalize(), vm::VmLog::Null(), {}, Ref<vm::Tuple>{}};
  g_sigs.clear();
  g_rec = false;
  int res = st->run();
  end_windows();
  return res;
}

#ifdef TVM_KLEE_SYMBOLIC
int main(int argc, char** argv) {
  const Spec* spec = argc > 1 ? find_spec(argv[1]) : nullptr;
  if (!spec) {
    std::fprintf(stderr, "usage: harness <SPEC>\n");
    return 2;
  }
  vm::init_vm(false).ensure();
  warm_up();
  g_target = &spec->alts;
  Input in = make_input(*spec);
  run_vm(in);
  Sig s = g_sigs.size() == 1 ? g_sigs[0] : Sig{0, 0};
  uint64_t out = sym<uint64_t>("sig");
  klee_assume(out == s.seq);
  uint64_t out_edges = sym<uint64_t>("esig");
  klee_assume(out_edges == s.edges);
  _exit(0);  // no destructors of the input, the VM or the opcode tables: the path is complete
}
#else
// ---------------------------------------------------------------- native: tokens
static std::string hex(td::Slice s) {
  static const char* d = "0123456789abcdef";
  std::string r;
  for (unsigned char c : s) {
    r += d[c >> 4];
    r += d[c & 15];
  }
  return r;
}

static std::string boc_hex(Ref<vm::Cell> c) {
  return hex(vm::std_boc_serialize(std::move(c)).move_as_ok().as_slice());
}

static std::string token(const vm::StackEntry& e) {
  switch (e.type()) {
    case vm::StackEntry::t_null:
      return "N";
    case vm::StackEntry::t_int: {
      auto x = e.as_int();
      return x->is_valid() ? td::dec_string(x) : "NaN";
    }
    case vm::StackEntry::t_cell:
      return "CB:" + boc_hex(e.as_cell());
    case vm::StackEntry::t_slice: {
      vm::CellBuilder cb;
      cb.append_cellslice(*e.as_slice());
      return "SB:" + boc_hex(cb.finalize());
    }
    case vm::StackEntry::t_builder: {
      auto b = e.as_builder();
      if (!b->size() && !b->size_refs()) {
        return "B";
      }
      return "BB:" + boc_hex(b->finalize_copy());
    }
    case vm::StackEntry::t_tuple: {
      auto t = e.as_tuple();
      if (t->empty()) {
        return "T";
      }
      std::string r;
      for (const auto& x : *t) {
        r += token(x) + " ";
      }
      return r + "TUP:" + std::to_string(t->size());
    }
    case vm::StackEntry::t_vmcont:
      return "K";
    default:
      return "?";
  }
}

static bool parse_hex(const std::string& h, std::string& out) {
  if (h.size() % 2) {
    return false;
  }
  out.clear();
  for (size_t i = 0; i < h.size(); i += 2) {
    auto v = [](char c) { return c >= 'a' ? c - 'a' + 10 : c >= 'A' ? c - 'A' + 10 : c - '0'; };
    out += (char)(v(h[i]) * 16 + v(h[i + 1]));
  }
  return true;
}

static Ref<vm::Cell> boc_cell(const std::string& h) {
  std::string bytes;
  if (!parse_hex(h, bytes)) {
    return {};
  }
  auto r = vm::std_boc_deserialize(td::Slice{bytes});
  return r.is_ok() ? r.move_as_ok() : Ref<vm::Cell>{};
}

// oracle stack tokens (oracle/fif/ton_oracle_runvm.fif, OracleHarness.lean valueToTokens)
static bool parse_tokens(const std::vector<std::string>& toks, std::vector<vm::StackEntry>& st,
                         Ref<vm::Tuple>& c7) {
  for (const auto& t : toks) {
    if (t == "N") {
      st.emplace_back();
    } else if (t == "NaN") {
      st.emplace_back(td::nan_refint());
    } else if (t == "I") {
      st.emplace_back(td::make_refint(0));
    } else if (t == "C") {
      st.emplace_back(Ref<vm::Cell>{vm::CellBuilder{}.finalize()});
    } else if (t == "S") {
      st.emplace_back(vm::load_cell_slice_ref(vm::CellBuilder{}.finalize()));
    } else if (t == "B") {
      st.emplace_back(Ref<vm::CellBuilder>{true});
    } else if (t == "T") {
      st.emplace_back(Ref<vm::Tuple>{true});
    } else if (t == "K") {
      st.emplace_back(Ref<vm::Continuation>{Ref<vm::QuitCont>{true, 0}});
    } else if (t.rfind("CB:", 0) == 0 || t.rfind("SB:", 0) == 0 || t.rfind("BB:", 0) == 0) {
      auto c = boc_cell(t.substr(3));
      if (c.is_null()) {
        return false;
      }
      if (t[0] == 'C') {
        st.emplace_back(c);
      } else if (t[0] == 'S') {
        st.emplace_back(vm::load_cell_slice_ref(c));
      } else {
        Ref<vm::CellBuilder> b{true};
        b.write().append_cellslice(vm::load_cell_slice(c));
        st.emplace_back(b);
      }
    } else if (t.rfind("TUP:", 0) == 0) {
      size_t n = std::stoul(t.substr(4));
      if (n > st.size()) {
        return false;
      }
      std::vector<vm::StackEntry> v(st.end() - n, st.end());
      st.resize(st.size() - n);
      st.emplace_back(Ref<vm::Tuple>{true, std::move(v)});
    } else if (t == "TPUSH") {
      if (st.size() < 2 || !st[st.size() - 2].is_tuple()) {
        return false;
      }
      auto x = st.back();
      st.pop_back();
      auto tup = st.back().as_tuple();
      st.pop_back();
      std::vector<vm::StackEntry> v(tup->begin(), tup->end());
      v.push_back(x);
      st.emplace_back(Ref<vm::Tuple>{true, std::move(v)});
    } else if (t == "SETC7") {
      if (st.empty() || !st.back().is_tuple()) {
        return false;
      }
      c7 = st.back().as_tuple();
      st.pop_back();
    } else {
      auto x = td::dec_string_to_int256(t);
      if (x.is_null() || !x->is_valid()) {
        return false;
      }
      st.emplace_back(x);
    }
  }
  return true;
}

static std::vector<std::string> split(const std::string& s, char sep) {
  std::vector<std::string> r;
  size_t p = 0;
  while (true) {
    size_t q = s.find(sep, p);
    r.push_back(s.substr(p, q == std::string::npos ? std::string::npos : q - p));
    if (q == std::string::npos) {
      break;
    }
    p = q + 1;
  }
  return r;
}

static std::string sig_hex(uint64_t s) {
  char b[17];
  std::snprintf(b, sizeof(b), "%016llx", (unsigned long long)s);
  return b;
}

static int run_case(const std::vector<std::string>& cols) {
  Input in;
  in.version = std::stoi(cols[1]);
  in.gas = std::stoll(cols[2]);
  in.code = boc_cell(cols[3]);
  Ref<vm::Tuple> c7;
  std::vector<std::string> toks;
  for (auto& t : split(cols[4], ' ')) {
    if (!t.empty()) {
      toks.push_back(t);
    }
  }
  if (in.code.is_null() || !parse_tokens(toks, in.stack, c7)) {
    std::printf("%s\tERROR\tunparsable case\n", cols[0].c_str());
    return 1;
  }
  Ref<vm::Stack> stack{true};
  for (const auto& e : in.stack) {
    stack.write().push(e);
  }
  Ref<vm::CellSlice> code{true, vm::NoVmOrd(), in.code};
  vm::VmState st{code, in.version, std::move(stack), vm::GasLimits{in.gas, in.gas}, 0,
                 vm::CellBuilder{}.finalize(), vm::VmLog::Null(), {}, c7};
  g_sigs.clear();
  g_rec = false;
  int res = st.run();
  end_windows();
  std::string sigs;
  for (auto s : g_sigs) {
    sigs += (sigs.empty() ? "" : " ") + sig_hex(s.seq) + ":" + sig_hex(s.edges);
  }
  std::printf("%s\t%d\t%s\n", cols[0].c_str(), res, sigs.empty() ? "-" : sigs.c_str());
  return 0;
}

// each test or case runs in a forked copy of the process as it is after init_vm: no state of one
// run (the digest counter, caches) reaches the next, as in KLEE where every path starts afresh
static int isolated(const char* id, const std::function<int()>& body) {
  std::fflush(stdout);
  pid_t pid = fork();
  if (pid == 0) {
    int r = body();
    std::fflush(stdout);
    _exit(r);
  }
  int status = 0;
  waitpid(pid, &status, 0);
  if (WIFEXITED(status)) {
    return WEXITSTATUS(status) ? 1 : 0;
  }
  std::printf("%s\tERROR\tcrashed (signal %d)\n", id, WTERMSIG(status));
  return 1;
}

int main(int argc, char** argv) {
  if (argc < 3 || (argc < 4 && std::strcmp(argv[1], "ranges"))) {
    std::fprintf(stderr,
                 "usage: replay ktest <SPEC> <file.ktest>... | replay cases <SPEC> <cases.tsv> | "
                 "replay ranges <SPEC>\n");
    return 2;
  }
  const Spec* spec = find_spec(argv[2]);
  if (!spec) {
    std::fprintf(stderr, "unknown spec %s\n", argv[2]);
    return 2;
  }
  std::string mode = argv[1];
  if (mode == "ranges") {  // the spec's opcode ranges as 24-bit [min, max): for picking suites
    for (const Alt& a : spec->alts) {
      std::printf("%u %u\n", a.lo << (24 - a.bits), (a.hi + 1) << (24 - a.bits));
    }
    return 0;
  }
  vm::init_vm(false).ensure();
  warm_up();
  g_target = &spec->alts;
  if (mode == "ktest") {
    int bad = 0;
    for (int i = 3; i < argc; i++) {
      bad += isolated(argv[i], [&]() {
        if (!replay::load_ktest(argv[i])) {
          std::printf("%s\tERROR\tunreadable ktest\n", argv[i]);
          return 1;
        }
        Input in;
        try {
          in = make_input(*spec);
        } catch (SilentExit&) {
          std::printf("%s\tERROR\tsilent exit while building the input\n", argv[i]);
          return 1;
        }
        run_vm(in);
        Sig s = g_sigs.size() == 1 ? g_sigs[0] : Sig{0, 0};
        if (replay::bad) {
          std::printf("%s\tERROR\t%s\n", argv[i], replay::why.c_str());
          return 1;
        }
        uint64_t out = sym<uint64_t>("sig");
        uint64_t out_edges = sym<uint64_t>("esig");
        if (replay::bad || out != s.seq || out_edges != s.edges) {
          std::printf("%s\tERROR\tpath differs from KLEE's (KLEE %s, replay %s, windows %zu)\n", argv[i],
                      sig_hex(out).c_str(), sig_hex(s.seq).c_str(), g_sigs.size());
          return 1;
        }
        std::string toks;
        for (const auto& e : in.stack) {
          toks += (toks.empty() ? "" : " ") + token(e);
        }
        std::printf("%s\t%s\t%s\t%d\t%lld\t%s\t%s\n", argv[i], sig_hex(s.seq).c_str(),
                    sig_hex(s.edges).c_str(), in.version, in.gas, boc_hex(in.code).c_str(), toks.c_str());
        return 0;
      });
    }
    return bad ? 1 : 0;
  }
  if (mode == "cases") {
    FILE* f = std::fopen(argv[3], "r");
    if (!f) {
      return 2;
    }
    std::string line;
    int c;
    int bad = 0;
    auto flush = [&]() {
      if (line.empty()) {
        return;
      }
      // id \t version \t gas \t code_hex \t tokens (space separated)
      auto cols = split(line, '\t');
      line.clear();
      if (cols.size() < 5) {
        std::printf("%s\tERROR\tbad line\n", cols[0].c_str());
        bad++;
        return;
      }
      bad += isolated(cols[0].c_str(), [&]() { return run_case(cols); });
    };
    while ((c = std::fgetc(f)) != EOF) {
      if (c == '\n') {
        flush();
      } else {
        line += (char)c;
      }
    }
    flush();
    std::fclose(f);
    return bad ? 1 : 0;
  }
  return 2;
}
#endif
