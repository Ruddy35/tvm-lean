# Рабочее пространство

## Сервер сборки и сверки

Все тяжёлые сборки Lean и прогоны сверки — на сервере, все ядра (`lake` параллелит сам, проверка
отдельного файла — `lake env lean -j $(nproc)`). Доступ — SSH поверх WebSocket (мост и ключ
передаются владельцем отдельно); код между средой разработчика и сервером синхронизируется только
через git (форк `Ruddy35/tvm-lean`, удалённый репозиторий `origin` рабочей копии на сервере).

| Путь | Что |
|---|---|
| `~/ws/tvm-lean` | этот репозиторий (рабочая копия, сборки) |
| `~/ws/ton-src` | исходники C++ эталонного коммита (`3d478cb`, неглубокий клон с подмодулями) |
| `~/ws/ton-bin` | `fift`/`fiftx` эталонного коммита и библиотека `fift` |
| `~/ws/ton-build` | Release-сборка `ton` эталонного коммита: криптобиблиотеки для модели (`TVMLEAN_TON_BUILD`) |
| `~/ws/ton-build-cov` | сборка `fift` с покрытием (gcov); её библиотеки для модели не годятся |
| `~/ws/fixtures` | наборы дифференциальных фикстур |
| `~/ws/runs` | логи прогонов |

## Криптография модели на Linux

Нативная криптография модели (`c/tvmlean_crypto_ext.c`: BLS12-381) собирается и линкуется с тем же
blst, что и C++ TVM, если заданы `TVMLEAN_TON_BUILD` (каталог cmake-сборки `ton`, не сборки с
покрытием) и `TVMLEAN_TON_SRC` (исходники, для заголовков blst). Без них эти операции — заглушки (их
случаи оракула не проходят). На Lean, без внешних функций: Ed25519 (`CHKSIGNU/S`,
`TvmLean/Model/Crypto/Ed25519.lean`), хеши `HASHEXT`/`SHA256U` (SHA-256/512 в
`TvmLean/Model/Basics/Bytes.lean`, `Blake2b.lean`, `Keccak.lean`), secp256k1 (`ECRECOVER`,
`SECP256K1_XONLY_PUBKEY_TWEAK_ADD`, `Secp256k1.lean`), P-256 (`P256_CHKSIGNU/S`, `P256.lean`) и
ristretto255 (`RIST255_*`, `Ristretto255.lean`) в `TvmLean/Model/Crypto/`.

## Полная сверка

```sh
cd ~/ws/tvm-lean
export PATH=$HOME/.elan/bin:$PATH TON_FIFT_BIN=~/ws/ton-bin/fiftx TON_FIFT_LIB=~/ws/ton-bin/lib \
  TVMLEAN_TON_BUILD=~/ws/ton-build TVMLEAN_TON_SRC=~/ws/ton-src
FIXTURES=~/ws/fixtures OUT=~/ws/runs/$(date +%F-%H%M) scripts/verify-all.sh
```

## Тестовые векторы криптографии

`tools/crypto/*.py` — независимые реализации на Python (Ed25519, ECDSA secp256k1 и P-256,
ristretto255, BLS12-381 через `py_ecc`); `python3 tools/crypto/gen_lean_vectors.py >
Tests/Harness/Gen/CryptoVectors.lean` пересоздаёт таблицы векторов для тестов.
