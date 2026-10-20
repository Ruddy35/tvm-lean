# Изменения модели относительно исходного tvm-lean

Каждое изменение — отдельный коммит ветки `formal-tvm`; подробности в сообщениях коммитов (`git log e1f334f..`).

База: `Gusarich/tvm-lean`, коммит `e1f334f`.
Эталон C++: `ton-blockchain/ton`, коммит `3d478cb` (сборка `fift`, на которой работает оракул).

## Сверка (на этой ветке)

| Проверка | Результат |
|---|---|
| Сборка всех библиотек и тестов | без ошибок |
| Unit-тесты, все 919 наборов | 5989 / 5989 |
| Оракул против C++, полный набор, глобальная версия 13 | 46 824 / 46 824 |
| Оракул против C++, полный набор, глобальная версия 16 | 46 824 / 46 824 |
| Fuzz против C++, версии 13 и 16 | 405 676 / 405 676 каждая |
| Дифференциальные прогоны реального байткода | 35 889 / 35 889 |

Проверено на `a5f0b60`.

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

### 1.2. Найдено по покрытию ветвей C++ (2026-10-20)

Источник — ветви `crypto/vm`, которые полный прогон с покрытием не прошёл (`docs/coverage/`):
для каждой построены случаи оракула, расхождения исправлены.

| Файл | Что изменено | Основание в C++ |
|---|---|---|
| `VM/Ops/State.lean` (`VmState.tryCommit`), `Model/Cell/Cell.lean` (`Cell.depthLe`), `Step/Run.lean`, `Exec/TonEnv/Commit.lean`, `Exec/Flow/Runvm.lean` | **ошибка исходной модели:** `c4`/`c5` фиксируются, только если оба глубиной не больше 512 и уровня 0; `depthLe n` означал глубину `< n` (ячейка ровно 512 не фиксировалась), уровень не проверялся (обрезанная ветвь фиксировалась) | `VmState::try_commit`, `force_commit`, `run` (`vm.cpp`) |
| `Exec/Msg/SendMsg.lean` | **ошибки:** порядок чтения цен и ограничений размера, их ошибки (`range_chk` / `unknown` / `cell_und`), версии записи `size_limits_config` v1–v3 точно по слайсу; подсчёт ячеек сообщения в глубину по порядку ссылок | `exec_send_message` (`tonops.cpp`), `Config::do_get_msg_prices`, `do_get_size_limits_config`, `VmStorageStat::add_storage` (`boc.cpp`) |
| `Exec/Msg/SendMsg.lean`, `Model/Cell/Primitives.lean` (`Slice.skip*Tlb`) | **ошибки:** сообщение проверяется как сгенерированный код TL-B (`anycast`, `addr_var`, адреса нужного вида, пустой остаток после тела); рабочие цепочки `MYADDR` и получателя читаются без проверки, как `parse_addr_workchain` | `tlb::type_unpack_cell(t_MessageRelaxed_Any)` (`block-auto.cpp`), `parse_addr_workchain` |
| `Exec/TonEnv/{GetGasFee,GetStorageFee,GetForwardFee,GetOriginalFwdFee,GetGasFeeSimple,GetForwardFeeSimple}.lean`, `Exec/Exception/{ThrowArgIf,ThrowArgIfNot,ThrowAny}.lean`, `Exec/Cell/Stb.lean` | **ошибка исходной модели:** 17 инструкций проверяют глубину стека до снятия операндов (`stk_und`, а не `type_chk`) | `check_underflow` в `exec_get_*_fee`, `exec_throw_arg_fixed`, `exec_throw_any`, `exec_store_builder` |
| `Model/Cell/Primitives.lean` (`libraryResolver`, `parseDictLabel`), `Exec/Common.lean` (`VM.loadCellSlice`, `VM.cellResolver`), инструкции со ссылками, словари, `Step/Step.lean` (неявный `JMPREF`) | **ошибка исходной модели:** ячейка-библиотека загружается как корень своей библиотеки (CTOS, LDREFRTOS, PUSHREF*, CALLREF, JMPREF*, IF*REF*, узлы словарей); прочие экзотические ячейки — `cell_und` (IF*REF и неявный JMPREF исполняли биты обрезанной ветви как код) | `load_cell_slice_impl` (`cells/CellSlice.cpp`), `VmState::load_library` (`vm.cpp`) |
| `Exec/Msg/SendMsg.lean` | **ошибка:** сообщение-библиотека разбирается и считается по корню своей библиотеки, в действие идёт сама ячейка; экзотическое сообщение — `cell_und` | `exec_send_message`: `type_unpack_cell`, `load_cell_slice(msg_cell)` |
| `Model/Cell/{Cell,Builder,Primitives}.lean` (`Cell.depthAt`, `Cell.refsDepthOk`, `Builder.finalizeChecked`, `dictKeyPath`), `Exec/Common.lean` (`VM.checkNewCellDepth`, `VM.chargeDictSetCreates`), `ENDC`, `ENDXC`, `STBREF*`, `ENDCST`, `BTOS`, `HASHBU`, `HASHSU`, действия, установка в словарях | **ошибка исходной модели:** ячейка глубже 1024 (на любом уровне) не создаётся: `cell_ov` после списания за создание; в словарях — после списания за узлы, созданные до первого слишком глубокого | `DataCell::create` (`cells/DataCell.cpp:78`), `CellBuilder::finalize*`, `dict_set`, `dict_lookup_set`, `pfx_dict_set` (`dict.cpp`) |
| `Exec/TonEnv/ConfigParam.lean` | **ошибка исходной модели:** индекс `CONFIGPARAM`/`CONFIGOPTPARAM` — ключ со знаком (−2³¹..2³¹−1, иначе поиска нет); узлы, загруженные до ошибки словаря, списываются | `exec_get_config_param` (`tonops.cpp:189`), `Dictionary::lookup_ref` |
| `Exec/Misc.lean` | **ошибка исходной модели:** `CDATASIZE`/`SDATASIZE` снимают границу через `pop_int` (NaN допустим), затем ячейку или слайс, и только потом — `range_chk` для NaN или отрицательной | `exec_compute_data_size` (`tonops.cpp:1529`) |
| `Step/Core.lean` (новый: `VmState.stepWith`, `runWith`), `Step/{Step,Run,Trace}.lean`, `Exec/Flow/Runvm.lean` | один шаг для VM, дочерних VM `RUNVM` и трассировки вместо трёх копий (копия трассировки уже расходилась); поведение не меняется | `VmState::run`, `run_inner`, `step` (`vm.cpp:438-513`) |
| `Step/Core.lean`, `Exec/Flow/LoopExt.lean` | **ошибка исходной модели:** в конце `WHILE`/`UNTIL`/`REPEAT` модель ставила `c0 := quit0`, если в `after` нет сохранённого `c0` (`*END` берут текущий `c0`); переход в `after` применяет только его собственный список сохранения. `REPEAT` строит `after` через `extract_cc(1)` | `WhileCont`/`UntilCont`/`RepeatCont::jump_w`, `OrdCont::jump` (`continuation.cpp:405-408, 509-512, 574-578, 637-647`) |
| `Step/Core.lean` (`OrdCdata.needsMoreArgs`) | **ошибка исходной модели:** проверка `nargs` при каждом прыжке: тело и условие, которые возвращают продолжения циклов, продолжения `WHILE`, `UNTIL`, `TRY`, `TRYARGS`, `IFNOTJMP` (`cc` задавался без `VM.jump`) — `stk_und`, у `TRY` — в новый обработчик | `adjust_jump_cont` (`vm.cpp:259-260`), `jump_to` (`vm.h:394-399`) |
| `Model/State/VmState.lean` (`chainJumps`), `Model/Gas/Constants.lean`, `Step/Core.lean` | **ошибка исходной модели:** девятый и следующие прыжки одной цепочки `jump_to` стоят по 1 газу | `jump_to`, `free_nested_cont_jump` (`vm.h:126, 386-401`) |
| `Model/Cont/Cregs.lean` (`Continuation.pushInt`), `Exec/Cont/AtExit.lean`, `Step/Core.lean` | **ошибка исходной модели:** продолжения `BOOLEVAL` — `PushIntCont`: кладут −1 или 0 и переходят в `cc`, не исполняя инструкции (модель исполняла `PUSHINT` и неявный `RET`: 23 газа; тип `vmc_pushint`) | `exec_booleval` (`contops.cpp:1051`), `PushIntCont::jump` (`continuation.cpp:321-330`) |
| `Exec/Flow/Runvm.lean` (`childRun`), `Step/Core.lean` (`GasLimits.stepBound`) | **ошибка исходной модели:** дочерняя VM работала не больше 50 000 шагов; теперь до остановки, число шагов ограничено её газом | `VmState::run`, `run_child_vm` (`vm.cpp:513, 729`) |
| `Exec/Flow/Runvm.lean` (`execInstrNested`) | **ошибка исходной модели:** `RUNVM` внутри дочерней VM был `inv_opcode`; глубина вложенности ограничена газом, рекурсия структурная | `run_child_vm`, `restore_parent_vm` (`vm.cpp:729, 770`), `exec_runvm_common` (`contops.cpp:230, 260-261`) |
| `Exec/Dict/Ext.lean` (`PFXDICTSET`, `PFXDICTDEL`) | **ошибка исходной модели:** узлы, загруженные до ошибки ниже корня (значение или слитое ребро не помещается, испорченный узел), не списывались | `pfx_dict_set`, `pfx_dict_lookup_delete` (`dict.cpp:988, 993`) |
| `Model/Cell/Primitives.lean` (`dictDeleteWithLoads`), `Exec/Dict/{Ext,DictGetMinMax}.lean` | **ошибка исходной модели:** при ошибке удаления (слитое ребро не помещается) списывались не те узлы: лишние соседи на пути (`DICT*DEL*`, `DICT*REMMIN/MAX*`) или без сливаемого ребёнка (`DICT*SETGETOPTREF`) | `DictionaryFixed::dict_lookup_delete` (`dict.cpp:1116-1188`) |

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
6. Покрытие ветвей C++ при сверке (`gcov`): замер есть (`docs/coverage/README.md`), идёт закрытие непокрытых ветвей.
7. Поле `savedC0` обычного продолжения (`Continuation.ordinary`) больше не читается семантикой и
   всегда `quit 0`: удалить (механическая правка ~400 мест).
