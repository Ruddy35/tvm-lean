# Изменения модели относительно исходного tvm-lean

Каждое изменение — отдельный коммит ветки `formal-tvm`; подробности в сообщениях коммитов (`git log e1f334f..`).

База: `Gusarich/tvm-lean`, коммит `e1f334f`.
Эталон C++: `ton-blockchain/ton`, коммит `3d478cb` (сборка `fift`, на которой работает оракул).

## Сверка (на этой ветке)

| Проверка | Результат |
|---|---|
| Сборка всех библиотек и тестов | 2673 задачи, без ошибок |
| Unit-тесты, все 919 наборов | 5967 / 5967 |
| Оракул против C++, полный набор, глобальная версия 13 | 25 760 / 25 760 |
| Оракул против C++, полный набор, глобальная версия 16 | 25 760 / 25 760 |
| Дифференциальные прогоны реального байткода | 35 889 / 35 889 |

## 1. Поведение, исправленное по C++ (найдено сверкой)

| Файл | Что изменено | Основание в C++ |
|---|---|---|
| `Model/State/VmState.lean`, `Exec/Flow/Runvm.lean` | поле `globalVersion` (по умолчанию 13); передаётся в дочернюю VM | `VmState::global_version` |
| `Model/Cont/Cregs.lean`, `Continuation.lean`, `Exec/Cont/{SaveCtr,SetContCtr,ChangeExt}.lean` | с версии 14 запись в уже заданный регистр — молчаливый no-op | `ControlRegs::define` |
| `Exec/Arith/{LshiftConst,RshiftConst}.lean` | с версии 14 NaN остаётся NaN | `exec_lshift/rshift` |
| `Exec/Arith/Ext.lean` | `SHRMOD` в тихом режиме с версии 14 | `exec_shrmod` |
| `Exec/Crypto/{ChkSignU,ChkSignS}.lean` | с версии 14 отклоняются нулевой и единичный ключи ed25519 | `exec_ed25519_check_signature` |
| `Exec/Crypto/Ext.lean` | `ECRECOVER` с `v = 27/28`; `ristretto255_mul` по правилам версии 14 | `exec_ecrecover`, `exec_ristretto255_mul` |
| `Exec/Msg/SendMsg.lean` | с версии 14 пользовательский `fwd_fee` игнорируется | `exec_send_message` |
| `Exec/TonEnv/StdAddr.lean` | тихий `STSTDADDR` с версии 14 возвращает исходное значение | `exec_store_std_address` |
| `Instr/Codepage/Cp0.lean`, `Instr/Ast.lean`, `Exec/Arith/Ext.lean` | **ошибка исходной модели:** режим округления 3 в семействах деления декодируется (длина как в C++) и выполняется как `inv_opcode` после газа инструкции (`invalidArgs`); `F2F6` недопустим; `EXTCALL` удалён | `OpcodeInstrFixed::dispatch`, `exec_divmod` & co., `mkfixedrange(0xf2f0, 0xf2f6)` |
| `Exec/Arith/Qpow2.lean` | **ошибка исходной модели:** с версии 13 `QPOW2` вне `0..1023` даёт NaN, а не `range_chk` | `exec_pow2` (`arithops.cpp:847`) |

### 1.1. Найдено сверкой криптографии и газа (2026-10-19, вторая сессия)

| Файл | Что изменено | Основание в C++ |
|---|---|---|
| `Model/Crypto/Ed25519.lean` (новый), `Exec/Crypto/{ChkSignU,ChkSignS}.lean` | **ошибка исходной модели:** подпись ed25519 проверялась libsodium (отвергает ключи и `R` малого порядка, неканонические ключи); теперь — на Lean, как OpenSSL: строгое уравнение без проверок малого порядка. Внешняя функция `ed25519Verify` удалена | `crypto/Ed25519.cpp` → `EVP_DigestVerify` → `ossl_ed25519_verify` |
| `Model/State/VmState.lean`, `VM/Ops/Gas.lean`, `Exec/Flow/Runvm.lean` | **ошибка:** не было бесплатного газа: бесплатные проверки подписи копят `free_gas_consumed`, `RUNVM` с изоляцией газа списывает его с родителя; счётчики передаются дочерней VM и обратно | `register_chksgn_call`, `run_child_vm`, `restore_parent_vm` |
| `Exec/TonEnv/GetExtraBalance.lean` | **ошибка:** не было «дешёвых» вызовов (первые 5: загрузки не дороже 200, остальное — бесплатный газ); короткий кортеж баланса — `range_chk`, а не 0; загрузки до ошибки словаря списываются | `exec_get_extra_currency_balance`, `tuple_index` |
| `Exec/Crypto/Ext.lean` | **ошибка:** не было начальной `check_underflow` у `ECRECOVER`, `SECP256K1_XONLY_PUBKEY_TWEAK_ADD`, `P256_CHKSIGN*`, `RIST255_{FROMHASH,ADD,SUB,MUL}`; ошибки blst давали код 15 вместо `unknown` (11) | `tonops.cpp`, `crypto/vm/bls.cpp` |
| `c/tvmlean_crypto_ext.c` | **ошибка:** сложение, вычитание и агрегирование BLS принимали точки вне подгруппы | `blst::P1/P2::aggregate` (`blst_p*_affine_in_g*`) |
| `Step/Step.lean`, `Step/Trace.lean`, `Exec/Flow/Runvm.lean` (`raiseException`), `Exec/Common.lean` (`VM.throwToHandler`, все `THROW*`) | **ошибка исходной модели:** если обработчик `c2` — замыкание, ждущее больше двух аргументов, прыжок в него из `throw_exception` бросает stk_und; это исключение при обработке исключения завершает VM с кодом stk_und (у `THROW*` — после второго газа исключения). Модель запускала обработчик | `VmState::run_inner` («exception while handling exception»), `throw_exception`, `adjust_jump_cont` (`vm.cpp`) |
| `Exec/Crypto/HashExt.lean`, `Exec/CellOp/Ext.lean` (`ENDXC`), `Exec/TonEnv/SetRand.lean`, `Exec/Crypto/Ext.lean` (34 цены), `Step/Step.lean` (недопустимый опкод; газ стека замыкания при прыжке) | **ошибки газа:** списание без немедленной проверки лимита там, где после него в той же инструкции есть ещё списание или исключение; разбор всех мест — `docs/audit/gas-charges.md` | `consume_gas` → `consume_chk`; `opctable.cpp`; `adjust_jump_cont` |

## 2. Тотальность (поведение не меняется)

Цель — чтобы все определения модели были тотальными и вычислимыми ядром Lean, без `partial` и без
недоказуемых циклов.

| Где | Что | Статус доказательства |
|---|---|---|
| `Basics/Bytes.lean` | циклы SHA-256/512 и упаковки битов через `List.range'` | **доказано** равенство исходному определению (`ModelEquiv`) |
| `Basics/Bytes.lean` | `countWhile` вместо циклов `while` (`SDCNT*`) | **доказано** `countWhile_eq` |
| `Cell/Primitives.lean` | поиск в словаре — структурная рекурсия | **доказаны** исходные уравнения (`*_eq`, `*_fuel`) |
| `Cell/Primitives.lean` | `dictLabelMatches` через `allBelow` | **доказано** равенство исходному |
| `Cell/Cell.lean` | `Cell.beq`, `computeLevelInfo?` — структурная взаимная рекурсия | частично; **не доказана** неподвижная точка |
| `Instr/Codepage/Cp0.lean` | `takeRefsInv` вместо четырёх циклов в декодере `PUSHCONT` | **не доказано** |
| `Exec/Dict/Ext.lean`, `Exec/Misc.lean`, `Value/Value.lean`, `Cont/Continuation.lean` | `partial` → тотальные с доказанным завершением | исходник `partial` не имеет логического содержания; проверено тестами |
| `Exec/Crypto/HashExt.lean`, `Exec/Msg/SendMsg.lean`, `Exec/Arith/Ext.lean`, `Exec/Crypto/Ext.lean` | циклы с явной границей | **не доказано**; проверено тестами |

## 3. Инфраструктура

- `Semantics/Contract.lean` — фаза исполнения (`computePhase`): начальное состояние, фиксация `c4/c5`, откат. Используется дифференциальным тестированием.
- `Proofs/ModelEquiv.lean` — доказательства из раздела 2.
- `Proofs/DecEq.lean` — разрешимое равенство для ячеек и инструкций.
- `Apps/TestsSubset.lean` — прогон тестов изменённых инструкций.
- `Validation/{Diff,Oracle}/Runner.lean`, `oracle/fif/ton_oracle_runvm_lib.fif` — выбор глобальной версии в сверке.

## Вынесено из модели (отдельный архив)

60 файлов доказательств путей контракта TON Storage, библиотека лемм об исполнении инструкций
(12 файлов) и генератор фикстур этого контракта. К модели TVM они не относятся.

## Открытые пункты на пути к полной модели

1. Доказать равенства, помеченные «не доказано» в разделе 2.
2. Аудит по исходникам C++ `3d478cb`: полный список опкодов и ветвей против модели; инструкции `EXTCALL`, `XCHG_IJ`, `SETCP_SHORT`.
3. Глобальные версии ниже 13.
4. Криптография и хэши, которые сейчас — внешние функции `Host`: secp256k1, P-256, ristretto255, BLS12-381, blake2b, keccak (ed25519 и SHA-2 — уже на Lean).
5. Фазы транзакции: хранение, кредит, действия, bounce.
6. Замер покрытия ветвей C++ при сверке (`gcov`).
