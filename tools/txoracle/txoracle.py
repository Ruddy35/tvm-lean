#!/usr/bin/env python3
"""C++ oracle for whole transactions: the TON transaction emulator (`emulator/emulator-extern.cpp`,
`TransactionEmulator::emulate_transaction`, which runs the phases of `crypto/block/transaction.cpp`
as the collator does) through `libemulator.so` of the reference build.

Reads one JSON object per line on stdin and writes one per line on stdout:
  in:  {"config": <b64 BOC of the config dictionary>, "account": <b64 BOC of a ShardAccount>,
        "msg": <b64 BOC of a Message>, "utime": n, "lt": n, "rand_seed": <64 hex digits>,
        "libs": <b64 BOC of the library dictionary, optional>, "ignore_chksig": bool (optional)}
  out: the emulator's JSON answer: {"success": true, "transaction": b64, "shard_account": b64, ...},
       {"success": false, "external_not_accepted": true, "vm_exit_code": n, ...} or
       {"success": false, "error": "..."}
The library: TVMLEAN_EMULATOR_LIB (default: libemulator.so of TVMLEAN_TON_BUILD/emulator)."""
import ctypes
import json
import os
import sys


def load():
    path = os.environ.get("TVMLEAN_EMULATOR_LIB") or os.path.join(
        os.environ.get("TVMLEAN_TON_BUILD", ""), "emulator", "libemulator.so")
    lib = ctypes.CDLL(path)
    lib.transaction_emulator_create.restype = ctypes.c_void_p
    lib.transaction_emulator_create.argtypes = [ctypes.c_char_p, ctypes.c_int]
    for name, args in [("transaction_emulator_set_unixtime", [ctypes.c_void_p, ctypes.c_uint32]),
                       ("transaction_emulator_set_lt", [ctypes.c_void_p, ctypes.c_uint64]),
                       ("transaction_emulator_set_rand_seed", [ctypes.c_void_p, ctypes.c_char_p]),
                       ("transaction_emulator_set_libs", [ctypes.c_void_p, ctypes.c_char_p]),
                       ("transaction_emulator_set_ignore_chksig", [ctypes.c_void_p, ctypes.c_bool]),
                       ("transaction_emulator_set_config", [ctypes.c_void_p, ctypes.c_char_p])]:
        f = getattr(lib, name)
        f.restype = ctypes.c_bool
        f.argtypes = args
    lib.transaction_emulator_emulate_transaction.restype = ctypes.c_void_p
    lib.transaction_emulator_emulate_transaction.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]
    lib.transaction_emulator_destroy.argtypes = [ctypes.c_void_p]
    lib.string_destroy.argtypes = [ctypes.c_void_p]
    lib.emulator_set_verbosity_level.argtypes = [ctypes.c_int]
    lib.emulator_set_verbosity_level(0)
    return lib


def emulate(lib, req):
    em = lib.transaction_emulator_create(req["config"].encode(), 0)
    if not em:
        return {"success": False, "error": "cannot create the emulator (config)"}
    try:
        ok = (lib.transaction_emulator_set_unixtime(em, req["utime"])
              and lib.transaction_emulator_set_lt(em, req["lt"])
              and lib.transaction_emulator_set_rand_seed(em, req["rand_seed"].encode())
              and lib.transaction_emulator_set_ignore_chksig(em, bool(req.get("ignore_chksig", False)))
              and (not req.get("libs") or lib.transaction_emulator_set_libs(em, req["libs"].encode())))
        if not ok:
            return {"success": False, "error": "cannot set the emulator parameters"}
        p = lib.transaction_emulator_emulate_transaction(em, req["account"].encode(), req["msg"].encode())
        res = json.loads(ctypes.string_at(p).decode())
        lib.string_destroy(p)
        res.pop("vm_log", None)
        return res
    finally:
        lib.transaction_emulator_destroy(em)


def main():
    lib = load()
    for line in sys.stdin:
        if line.strip():
            print(json.dumps(emulate(lib, json.loads(line))), flush=True)


if __name__ == "__main__":
    main()
