# Аудит ширины целых в коде транзакции

Эталон: `ton-blockchain/ton` @ `3d478cb`. Дата: 2026-10-23.

## Правило

Каждый шаг арифметики над значением, которое задают конфигурация, счёт или сообщение, сверен с
моделью (`TvmLean/Transaction/*`, инструкции цен в `TvmLean/Semantics/Exec/TonEnv`). C++ считает
часть таких шагов в `td::uint64`, `long long`, `int`, `unsigned`: сложение и умножение по модулю
2^64 (2^32), приведение `td::uint64` → `long long` (отрицательно от 2^63), `to_long()` (−2^63 вне
`long long`), `td::RefInt256 ± long long` (`add_tiny` и `normalize` в `long long`: на 2^64 меньше,
когда младшая 52-битная цифра плюс число доходит до 2^63 − 2^51; `refIntAddLong`),
`operator*(RefInt256, long long)` (точно, но со знаком). Остальное — `td::RefInt256`, точно.

Итог в столбце: **то же** — модель считает так же; **исправлено** — расхождение, исправлено по C++
со случаями (`Tests/Tx/Coverage.lean`, пулы оракула) и строкой `docs/model-changes.md`;
**недостижимо** — C++ не выходит за ширину при допустимых входах (почему — в строке).

## Фаза хранения

| C++ | Модель | Итог |
|---|---|---|
| `add_partial_storage_payment` (transaction.cpp:757-774): `mul_short(price)` берёт цену `td::uint64` как `long long` | `storagePartial` (`Run.lean`) | **исправлено**: цены от 2^63 отрицательны (`cov/storage64/`) |
| там же, 771: отрицательная доля → `FAIL_UNLESS` → `compute_storage_fees` возвращает пустое число (807-810), 1060: `+ due_payment` через пустой `Ref` — аварийный останов | `storageFeesAbort`, `Tx.storageAborts` (`Emulate.lean`) | **исправлено**: «не поддержано»; случая нет (останов кончает оракул) |
| там же: `(long long)storage_used.cells/bits` | `storagePartial` | недостижимо: статистика — `VarUInteger 7`, меньше 2^56 |
| `compute_storage_fees` (790-813): `valid_until - upto` (`uint32`), выбор цены | `storagePartials` | то же: разность положительна; цены упорядочены по ключу (mc-config.cpp:757) |
| там же, 813: `td::rshift(total, 16, 1)` | `storageFees` | то же |
| `prepare_storage_phase` (1056-1132): `now < last_paid` (`uint32`), сравнения с `freeze_due_limit`/`delete_due_limit` (`make_refint(uint64)`, целиком) | `Tx.storagePhaseRun` | то же |
| `calculate_storage_fee` (`GETSTORAGEFEE`, tonops.cpp:2621-2638): `make_refint(cells) * price` — `operator*(RefInt256, long long)` | `GetStorageFee.lean` | **исправлено**: цены от 2^63 отрицательны (пул `cfg-storage-high`) |

## Входящее сообщение, логическое время, эмулятор

| C++ | Модель | Итог |
|---|---|---|
| `Transaction::Transaction` (860-861): `start_lt = max(lt, last_trans_end_lt)`, `end_lt = start_lt + 1`, `td::uint64` | `newTx` (`Emulate.lean`) | **исправлено**: `end_lt` по модулю 2^64 (`cov/lt64/account-max`) |
| `unpack_input_msg` (921-924): `start_lt = created_lt + 1`, `end_lt = start_lt + 1` | `Tx.unpackInputMsg` (`Run.lean`) | **исправлено** (`cov/lt64/created-max`, `created-near-max`) |
| `commit` (4071): `last_trans_end_lt <= start_lt && start_lt < end_lt` | `Tx.commitLtValid` | **исправлено**: проверка добавлена (без переноса всегда выполнена) |
| transaction-emulator.cpp:39-45: без логического времени — блок после последней транзакции счёта, `td::uint64` | `newTx` | **исправлено** (`cov/lt64/emulator-lt-zero`, `-wrap`) |
| transaction-emulator.cpp:31-36: без времени — `std::time(nullptr)` | — | не моделируется: время недетерминировано; сверка всегда задаёт время |
| `Account::unpack` (493): `max(storage.last_trans_lt, 1) > last_trans_lt` (`td::uint64`) | `Account.unpack` | то же |
| `Account::unpack_storage_info` (292-295): `cells`, `bits` — `VarUInteger 7` как `td::uint64` | `Account.unpack` | то же: меньше 2^56 |
| `unpack_input_msg` (958-959): `sstat.bits -= cs.size(); sstat.cells--` (`td::uint64`) | `sliceStorage` | недостижимо: корень входит в счёт |
| 903-918: `ihr_fee`, `extra_flags`, `msg_balance_remaining += ihr_fee` (`RefInt256`) | `Tx.unpackInputMsg` | то же |
| 973-985: сбор ввоза внешнего сообщения | `MsgPrices.fwdFees` | исправлено ранее (раздел 1.8) |
| `prepare_vm_c7` (1520-1567), `prepare_in_msg_params_tuple` (1594-1608): `make_refint(start_lt)`, `block_lt`, `created_lt`, `created_at`, `precompiled_gas_usage` (`td::uint64` целиком) | `Tx.c7`, `Tx.inMsgParams` | то же (логическое время — после исправления выше) |

## Фаза кредита и фаза вычислений

| C++ | Модель | Итог |
|---|---|---|
| `prepare_credit_phase` (1134-1155): `RefInt256`, `CurrencyCollection` | `Tx.creditPhaseRun` | то же |
| `compute_max_gas_threshold`, `gas_bought_for`, `compute_gas_price` (1268-1318, 1395-1416) | `GasPrices.*` | исправлено ранее (раздел 1.8) |
| `compute_gas_limits` (1427-1450): минимумы `td::uint64` | `Tx.computePhaseRun` | то же |
| `vm::GasLimits` из `td::uint64` (1938, 1955-1956), `gas_used` (2016) | `Tx.runVm`, `computePhaseRun` | исправлено ранее (разделы 1.6, 1.8) |
| 2057-2058: `exit_arg` только при `signed_fits_bits(32)` | `computePhaseRun` | то же |
| 1898-1899: `fixed_prefix_length > static_cast<int>(max_acc_fixed_prefix_length)` (поле `uint8`) | `computePhaseRun` | то же |
| 2014: `vm_steps = (int)get_steps_count()` | `computePhaseRun` | недостижимо: 2^31 шагов |
| `run_precompiled_contract` (1764-1838) | — | недостижимо: в эталонной сборке нет реализаций предкомпилированных контрактов |
| 2061-2072: плата за газ, баланс | `Tx.gasFeesNegative`, `Tx.payGas` | исправлено ранее (раздел 1.8) |

## Фаза действий

| C++ | Модель | Итог |
|---|---|---|
| 2156: `n > max_actions` (`int`, всегда 255) | `Tx.actionPhaseRun` | то же |
| 2250, 2281: `action_fine = min(action_fine + fail_action_fine, balance)` (`RefInt256`) | `Tx.actionPhaseRun` | то же |
| 2279: `end_lt = start_lt + 1` | `Tx.actionPhaseRun` | **исправлено** (по модулю 2^64) |
| 2827: `fine_per_cell = (cell_price >> 16) / 4` (`td::uint64`) | `Tx.actionSendMsg` | то же |
| 2854: `funds->cmp(max_cells * fine_per_cell)` — произведение `td::uint64` по модулю 2^64, сравнение как `long long` | `Tx.actionSendMsg` | **исправлено** (`cov/fine64/cmp-wrap`) |
| 2855: `(unsigned)((funds / fine_per_cell)->to_long())` | `Tx.actionSendMsg` | то же: частное меньше 2^31, когда условие выполнено |
| 2874-2875: `fine = fine_per_cell * min(max_cells, cells)` (`td::uint64`) | `Tx.actionSendMsg` | **исправлено** (по модулю 2^64; перенос — от 2^18 ячеек) |
| 2876-2883: `collect_fine` — сравнение `cmp(long long)`, `to_long()`, `+=`/`-=` с `long long` | `collectFine` | то же ниже 2^63 − 2^52 (там `refIntAddLong` точно); **исправлено**: штраф от 2^63 − 2^52 (от 2^17 ячеек при наибольшей цене) — «не поддержано»; случая нет |
| 3148: `fail_action_fine += fine` (`long long`) | `Tx.actionSendMsg` | то же (там же) |
| 2911-2916: сборы сообщения против вычисленных как `long long` | `Tx.actionSendMsg` | исправлено ранее (раздел 1.8) |
| 2432-2438, 2469-2476: сборы пересылки `td::uint64` | `MsgPrices.fwdFees` | исправлено ранее (раздел 1.8) |
| 2940-2990, 3058: `req_grams`, `fees_total`, `remaining_balance` (`RefInt256`) | `Tx.actionSendMsg` | то же |
| 3015-3016: `get_first_part(RefInt256)` (`* first_frac >> 16`, точно) | `Tx.actionSendMsg` | то же |
| 3040-3041, 3092-3093: `tot_msg_bits + bits + new_bits` против `max_total_msg_*` | `Tx.actionSendMsg` | недостижимо: суммы много меньше 2^64 |
| 3129: `ap.end_lt++` | `Tx.actionSendMsg` | **исправлено** (по модулю 2^64) |
| `try_action_reserve_currency` (3163-3250): `RefInt256`, `CurrencyCollection` | `Tx.actionReserve` | то же |
| `try_action_change_library` (2344-2420), 2402: `sstat.cells > max_library_cells` | `Tx.actionChangeLibrary` | то же |
| `check_state_limits` (3309-3366): счётчики ячеек и библиотек (`uint32`) | `Tx.checkStateLimits` | то же |
| `add_extra_currency`, `sub_extra_currency` (block.cpp:1932-1954): `RefInt256`, `VarUInteger 32` | `Extra.lean` | то же |

## Фаза возврата, состояние, запись

| C++ | Модель | Итог |
|---|---|---|
| 3450-3460, 3466-3484: сбор, «нет средств» как `long long`, значение и `fwd_fee` возвращаемого сообщения | `Tx.bouncePhaseRun` | исправлено ранее (раздел 1.8) |
| 3474-3475: `created_lt = start_lt + 1 + out_msgs.size()`, `end_lt++` | `Tx.bouncePhaseRun` | **исправлено** (по модулю 2^64) |
| 3423: `min((int)cs.size(), bounce_msg_body)` | `Tx.bouncePhaseRun` | то же |
| 2496-2498: `get_first_part(td::uint64)` (`uint128`, `.lo()`) | `Tx.bouncePhaseRun` | то же: `first_frac` не больше 2^16 |
| `compute_state` (3688-3705): статистика хранения, `bits -= old; += new` (`td::uint64`) | `Tx.storageStat` | исправлено ранее (раздел 1.6) |
| 3572, 3763: `store_long(end_lt, 64)`, `store_long(start_lt)` | `Tx.computeState`, `Tx.serialize` | то же: модель пишет младшие 64 бита |
| `serialize` (3746-4017): ширины полей | `Tx.serialize` | исправлено ранее (раздел 1.6) |

## Конфигурация

| C++ | Модель | Итог |
|---|---|---|
| mc-config.cpp:2052-2096 (параметр 43): `static_cast<td::uint16>` полей `uint16`, `(td::uint32)prefetch_long(32)` | `Config.sizeLimits` | то же: те же биты |
| transaction.cpp:4302-4312 (параметры 24, 25): `(unsigned)first_frac`, `next_frac` (`uint16`) | `Config.msgPrices` | то же |
| mc-config.cpp:744-774 (параметр 18): цены `td::uint64` | `Config.storagePrices` | то же (знак — при использовании, выше) |
| transaction.cpp:1204-1233 (параметры 20, 21) | `Config.gasPrices` | то же |

## Инструкции цен

| C++ | Модель | Итог |
|---|---|---|
| `GETSTORAGEFEE` | `GetStorageFee.lean` | **исправлено** (выше) |
| `GETFORWARDFEE` (`compute_fwd_fees256`: `make_refint(uint64)` целиком, `* bits` до 2^63 − 1) | `GetForwardFee.lean` | то же (пул `cfg-storage-high`: цены 2^63 и 2^64 − 1) |
| `GETFORWARDFEESIMPLE`, `GETGASFEESIMPLE` | `GetForwardFeeSimple.lean`, `GetGasFeeSimple.lean` | то же |
| `GETORIGINALFWDFEE` (`muldiv(fwd, 2^16, 2^16 - first_frac)`, `first_frac` до 65535) | `GetOriginalFwdFee.lean` | то же |
| `GETGASFEE`, `SENDMSG` (`compute_fees`) | `GetGasFee.lean`, `SendMsg.lean` | исправлено ранее (раздел 1.8) |
