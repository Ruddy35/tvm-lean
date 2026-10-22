# Изменения модели относительно исходного tvm-lean

Каждое изменение — отдельный коммит ветки `formal-tvm`; подробности в сообщениях коммитов (`git log e1f334f..`).

База: `Gusarich/tvm-lean`, коммит `e1f334f`.
Эталон C++: `ton-blockchain/ton`, коммит `3d478cb` (сборка `fift`, на которой работает оракул).

## Сверка (на этой ветке)

| Проверка | Результат |
|---|---|
| Сборка всех библиотек и тестов | без ошибок |
| Unit-тесты, все 919 наборов | 5990 / 5990 |
| Оракул против C++, полный набор, каждая глобальная версия 0..16 | 48 618 / 48 618 на каждой |
| Fuzz против C++, каждая версия 0..16 | 417 516 / 417 516 на каждой |
| Дифференциальные прогоны реального байткода | 35 889 / 35 889 |
| Транзакции против эмулятора C++, версии 0..16 | 40 125 / 40 125 и 3000 / 3000 случайных |

Проверено на `a303aee` (сервер): разделы 1.1–1.6, 2 и 4 целиком, включая фазу исполнения транзакции из
определений `Contract.lean` и исправления, найденные по покрытию `transaction.cpp`.

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
| `Exec/Stack/{BlkSwapX,ReverseX}.lean` | **ошибка исходной модели:** нет `check_underflow(2)` до снятия счётчиков (найдено проходом коротких стеков по собственному опкоду набора) | `exec_blkswap_x`, `exec_reverse_x` (`stackops.cpp:439, 455`) |

### 1.3. Глобальные версии ниже 13 (фаза 3, 2026-10-20)

Источник — ветви C++ по `global_version` (`docs/audit/cpp-global-version.csv`): модель повторяла
версию 13 на всех версиях. Каждая ветвь сверена полным оракулом на версиях по обе стороны порога;
случаи, которых не было в наборах, — в `Tests/Harness/Gen/Versions.lean` (идут для каждого набора и
каждой версии).

| Файл | Что изменено | Основание в C++ |
|---|---|---|
| `Model/Instr/Codepage/Versions.lean`, `Step/Core.lean` | опкоды более поздней версии — `inv_opcode` после списания `gas_per_instr` | `OpcodeInstrWithVersion::dispatch` (`opctable.cpp:457-461`) |
| `Exec/Arith/{DivMod,MulDivMod,Ext}.lean` | формы `ADD` деления и сдвигов (режим 0) — с версии 4, до неё `inv_opcode` | `exec_divmod`, `exec_shrmod`, `exec_muldivmod`, `exec_mulshrmod`, `exec_shldivmod` (`arithops.cpp:271, 350, 461, 530, 643`) |
| `Step/Core.lean` (`VmState.enteredCdata`) | до версии 9 продолжение, в которое переходит цепочка `jump_to`, входит без своего стека и `nargs` | `jump_to` (`vm.h:394-399`) |
| `Exec/Common.lean` (`VM.popStackCount`), `Exec/Stack/*X.lean`, `Exec/Stack/BlkSwapX.lean` | до версии 4 счётчик со стека — не больше 255; `BLKSWX` не списывает газ за элементы сверх 255 | `stackops.cpp:404-530`, `443-445` |
| `Exec/Msg/{RawReserve,RawReserveX,SetLibCode,ChangeLib}.lean` | до версии 4 режим `RAWRESERVE` до 15, `SETLIBCODE`/`CHANGELIB` — до 2 | `tonops.cpp:2370, 2403-2414, 2427-2438` |
| `Exec/Cell/Ext.lean` (`XLOAD`) | до версии 5 ячейка возвращается как есть, без загрузки | `exec_load_special_cell` (`cellops.cpp:906`) |
| `Exec/Crypto/HashExt.lean` | до версии 9 нет `check_underflow(2)` для номера хэша со стека, счётчик `HASHEXTA` может включать построитель | `exec_hash_ext` (`tonops.cpp:687-691`) |
| `Exec/Dict/Ext.lean` (`PFXDICTSET`, `PFXDICTDEL`) | до версии 9 проверка глубины на один элемент меньше | `dictops.cpp:570, 584` |
| `Model/Value/IntVal.lean` (`nanLshiftCpp`, `nanRshiftCpp`, `nanAndCpp`, `nanOrCpp`), `Exec/Arith/{Lshift,Rshift,And,Or,ContExt,Ext,MulShrModConst,LshiftConst,RshiftConst}.lean` | до версии 13 NaN в сдвигах, `AND`, `OR`, `MULRSHIFT`, `LSHIFTDIV` проходит через `BigInt` C++ (NaN, сдвинутый на целые слова, — 0; `AND` с 0 — 0, `OR` с −1 — −1; …), тихие формы бросают `range_chk` на плохой сдвиг; **ошибка и на версии 13:** `LSHIFT#` NaN на 52..63 бита — 0 | `arithops.cpp:542-562, 655-673, 775-889`; `lshift_any`, `rshift_any`, `log_op_any` (`bigint.hpp`) |
| `VM/Ops/Gas.lean` (`VmState.gasExhaustedNow`), `Step/Core.lean` | до версии 4 `consume_gas` не останавливает инструкцию: её находит `gas.check()` в конце шага; исключение списывается до остановки; прыжок в обработчик исключения не проверяется, и первая инструкция обработчика исполняется; `CHKSIGN*` не считаются | `VmState::consume_gas` (`vm.h:203-209`), `run_inner` (`vm.cpp:483-497`), `register_chksgn_call` (`vm.h:434-443`) |
| `Model/Cell/Primitives.lean` (`skipMaybeAnycast`, `skipMessageAddr`, `parseMaybeAnycast`, `parseMessageAddr`), `Exec/TonEnv/{LdMsgAddr,ParseMsgAddr,RewriteStdAddr,RewriteVarAddr}.lean` | до версии 10 адрес может быть `addr_var` и иметь anycast; `REWRITEVARADDR` строит новую ячейку (создание и загрузка) | `tonops.cpp:1608-1853` |
| `Exec/TonEnv/GlobalId.lean` | до версии 6 — запись 19 словаря конфигурации из параметра 19 `c7` | `exec_get_global_id` (`tonops.cpp:277-304`) |
| `Exec/Msg/SendMsg.lean` | до версии 6 цены из словаря конфигурации (параметр 9, ключи 24/25) и предел 2¹³ ячеек; до 10 — учёт словаря валют сообщения и валют баланса (режимы 128/64); до 11 — плата IHR, если сообщение её не отключает; до 12 — `extra_flags` читается как `ihr_fee`; **ошибка:** длина корня считалась с платой до переноса `init` в ссылку | `exec_send_message` (`tonops.cpp:2121-2357`) |
| `Model/Cell/Primitives.lean` (`libraryResolveLoads`), `VM/Ops/Gas.lean` (`VM.registerCellLoad`, `registerCellLoadSpecial`), `Exec/Common.lean`, `Step/Core.lean` | до версии 5 корень библиотеки загружается и списывается, библиотека в библиотеке разрешается дальше; до версии 4 поиск в коллекции списывает её узлы | `load_cell_slice_impl` (`CellSlice.cpp:1074-1136`), `VmState::load_library` (`vm.cpp:643-670`) |
| `Exec/Flow/Runvm.lean` | **ошибка:** родитель, не способный оплатить газ дочерней VM (или стек её результатов), сообщал газ без этой оплаты | `restore_parent_vm` (`vm.cpp:788, 805`) |
| `Model/Cont/Cregs.lean` (`Value.nullCell`), `Exec/Flow/Runvm.lean` | `RUNVM`: до версии 10 пределы газа дочерней VM — по остатку до оплаты бесплатного газа; до 11 незафиксированные `c4`/`c5` — запись-ячейка без ячейки (не `null` для `ISNULL`) | `run_child_vm`, `restore_parent_vm` (`vm.cpp:729-826`) |

### 1.4. Криптография на Lean (фаза 4, 2026-10-20)

Внешние функции `Host` заменены реализациями на Lean (`TvmLean/Model/Crypto/`). Каждая сверена с
самой библиотекой, которую вызывает C++, на тысячах случаев (0 расхождений), наборы — оракулом и
fuzz на нескольких версиях; новые случаи оракула и fuzz — на найденные правила библиотек.

| Файл | Что | Основание в C++ |
|---|---|---|
| `Crypto/Keccak.lean`, `Crypto/Blake2b.lean`, `Basics/Bytes.lean` (SHA-256/512) | `HASHEXT{A}{R}`, `SHA256U` (сверка с hashlib и `crypto/keccak` на 710 длинах до 12 000 байт) | `Hasher.cpp` (OpenSSL EVP, `keccak_digest(…, padding = 1)`) |
| `Crypto/Weierstrass.lean`, `Crypto/Secp256k1.lean` | `ECRECOVER`, `SECP256K1_XONLY_PUBKEY_TWEAK_ADD` (4333 случая против libsecp256k1) | `secp256k1.cpp`, libsecp256k1 `acf5c55`: `parse_compact`, `ecdsa_sig_recover`, `xonly_pubkey_parse`, `tweak_add_helper` |
| `Crypto/P256.lean` | `P256_CHKSIGNU/S` (2983 случая против OpenSSL) | `p256.cpp`, OpenSSL 3.5.5: `oct2point`, `ecdsa_simple_verify_sig` |
| `Crypto/Ristretto255.lean` | `RIST255_*` (1900 случаев против libsodium) | libsodium `d24faf5`: `ristretto255_frombytes`, `_p3_tobytes`, `_from_hash`, `crypto_scalarmult_ristretto255{_base}` |
| `Crypto/Bls12381*.lean` | `BLS_*` (20 296 случаев против blst): разбор и подгруппы как blst, GLV/GLS и окна умножения, таблицы и корзины `MULTIEXP`, правила бесконечности в `PAIRING` и проверках | `bls.cpp`, blst `6d960cd` (`e1.c`, `e2.c`, `multi_scalar.c`, `pairing.c`, `aggregate.c`) |

### 1.5. Найдено по ходу фазы 5 (2026-10-20)

| Файл | Что изменено | Основание в C++ |
|---|---|---|
| `Model/Cell/Primitives.lean` (`dictDeleteAuxWithLoads`), `Exec/Dict/Ext.lean` (`pfxLookupDeleteWithCells`) | **ошибка исходной модели:** удаление, после которого у развилки остаются оба ребёнка, пишет метку развилки заново (`dictLabelEncode`, как `append_dict_label`), а не копирует биты старой ячейки: метка могла быть записана другим своим кодом (`parse_label` читает любой), узел словаря — ячейкой-библиотекой. `DICT*DEL*`, `DICT*REMMIN/MAX*`, `DICT*SETGETOPTREF` с `null`, `PFXDICTDEL`; в транзакции — `clamp` валют резерва и удаление `CHANGELIB` | `dict_lookup_delete`, `pfx_dict_lookup_delete` (`dict.cpp:1165, 975`), `append_dict_label` (`dict.cpp:565`) |
| `Exec/Dict/Ext.lean` (`PFXDICTSET`/`ADD`/`REPLACE`, `PFXDICTDEL`, `PFXDICTGET*`, `PFXDICTSWITCH`, ошибка `SUBDICT*GET`) | **ошибка исходной модели:** ячейка-библиотека в префиксном словаре (корень или узел) загружается как корень своей библиотеки (`VM.cellResolver`), а не `cell_und`; при ошибке `SUBDICT*GET` списываются узлы и за ячейкой-библиотекой | `LabelParser` (`dict.cpp:264`) → `load_cell_slice_ref`; `load_cell_slice_impl` (`cells/CellSlice.cpp:1107-1120`) |

### 1.6. Найдено по покрытию `transaction.cpp` (фаза 5, 2026-10-21)

Случаи `Tests/Tx/Coverage.lean` на непокрытые ветви первого замера (`docs/coverage/README.md`); каждое
исправление — коммит со случаями и мутацией (без него случаи расходятся с эмулятором).

| Файл | Что изменено | Основание в C++ |
|---|---|---|
| `Transaction/Action.lean` (`parseRelaxedMsg`, `actionSendMsg`) | библиотека `StateInit` исходящего сообщения проверяется при самом действии, а не при проверке списка (там `library:(Maybe ^Cell)`): действия до него исполняются, с версии 13 режим 2 его пропускает | `validate_message_relaxed_libs` (transaction.cpp:2704-2707), 2169 |
| `Transaction/Action.lean` (`actionSendMsg`) | `fwd_fee` и `extra_flags` исходящего сообщения с ведущим нулевым байтом (`block::tlb::t_Grams`): до версии 8 действие неверно, с версии 12 — код 45 | transaction.cpp:2766-2783 |
| `Transaction/Action.lean` (`actionSendMsg`) | заголовок исходящего сообщения больше 1023 бит (после переписывания сумм и адресов) — фаза действий не удаётся, эмулятор отказывает (раньше модель давала 39) | `csr_pack` под `ERRCODE_FAIL_ACTION_PHASE` (3026), 2229-2230 |
| `Transaction/Run.lean` (`Tx.msgBalanceValid`), `Action.lean`, `Emulate.lean` | у tick-tock `msg_balance_remaining` не задан: режим 64 до версии 10 — 37 со штрафом; с версии 10 и с режимом 65 C++ разыменовывает пустое число (модель: «не поддержано»); режимы 128 и 64 его обнуляют, с версии 14 он восстанавливается при неудаче фазы | transaction.h:388; transaction.cpp:2839-2841, 2948-2974, 3049-3055, 2247, 2276 |
| `Transaction/Account.lean` (`mkAddr`, `withMyAddr`, `unpackAddress`), `Emulate.lean` (`accountAddrValid`) | `compute_my_addr` строит `addr_std` только для воркчейнов -128..126: anycast-счёт воркчейна 127 получает `addr_var`, и новый счёт не проходит `block::tlb::t_Account` — эмулятор отказывает; счёт без anycast сохраняет свой адрес | transaction.cpp:341-372, 3713, 3733; block-parse.cpp:83-99 |
| `Transaction/Config.lean` (`mcGasPricesValid`, `createFeesValid`), `Emulate.lean` | параметр 20 нужен счёту любого воркчейна (`get_gas_limits_prices(true)`: не до конца ячейки, `gas_prices#dd` после `gas_flat_pfx` не принимается); параметр 14, если есть, читается точно с суммами `block::tlb` | transaction.cpp:4297-4299, 4358-4368; mc-config.cpp:776-807 |
| `Transaction/Run.lean` (`computePhaseRun`, `payGas`) | счёт без кода (активный или `StateInit` без кода): VM не исполняется, код выхода -13 (`~fatal`), ни шагов, ни газа, `exit_arg` — верх начального стека; принятое сообщение активирует счёт и платит за газ (раньше — «не поддержано») | transaction.cpp:1934, 1995-2072; vm.cpp:84-88, 513-516 |
| `Transaction/Action.lean` (`parseRelaxedMsg`) | тело-ссылка и `^StateInit` предложенного сообщения — экзотические ячейки: проверка списка действий их не принимает (34, с версии 8 режим 2 пропускает), раньше модель отправляла сообщение | `TLB::validate_ref_internal` (tlblib.cpp:128-148), `RefT` (tlblib.hpp:1071-1083), block-auto.cpp:4490-4494 |
| `Transaction/Run.lean` (`Tx.computeState`, `Tx.storageStat`), `Emulate.lean` | новый счёт, поле которого не помещается в свою запись: `compute_state` возвращает `false`, эмулятор отказывает (раньше модель записывала неверную длину): баланс или долг от 2^120 (`Grams`), статистика хранения от 2^48 (`VarUInteger 7`). Биты статистики при неизменных ссылках обновляются 64-битно (`-= old; += new`): ниже нуля — переполнение и отказ, иначе разность (раньше модель вычитала с обрезкой до нуля) | transaction.cpp:3572-3573, 3704-3705, 3714-3715, 3720; transaction-emulator.cpp:70-73 |
| `Transaction/Emulate.lean` (`inputsAtLevel0`, `emulate`, `emulateTickTock`) | входы эмулятора — мешки ячеек, а `std_boc_deserialize` не принимает корень ненулевого уровня: сообщение, тело которого ссылается на обрезанную ветвь (или на обычную ячейку над ней), счёт с такими данными, библиотеки эмулятора, конфигурация — эмулятор отказывает (раньше модель исполняла транзакцию, а с экзотическим телом отвечала «не поддержано»). Найдено доказательствами хранения контракта TON Storage (`Tests/Tx/StorageContract.lean`) | boc.cpp:975-977; emulator-extern.cpp:15-18, 69, 383-387, 112-115, 120-123, 232-235 |
| `Transaction/Run.lean` (`Tx.serialize`) | транзакция, поле которой не помещается в свою запись: `serialize` возвращает `false`, эмулятор отказывает (раньше модель записывала неверную длину): `total_fees`, собранные и недоплаченные сборы фазы хранения (`Grams`, от 2^120; недоплата — до версии 4 или у удалённого счёта), `gas_limit` и `gas_used` (`VarUInteger 7`, от 2^48: параметр 21 с большим лимитом газа), `gas_credit` (`VarUInteger 3`, от 2^16: параметр 21), сборы фазы возврата от 2^63 (`long long` от `uint64`: параметр 25 с платой от 2^63; C++ отказывает уже в самой фазе возврата, при записи возвращаемого сообщения, модель — в `serialize`), а также проверки, недостижимые без чрезмерных параметров или 2^31 шагов VM (`vm_steps`, `gas_fees`, сборы и размеры фазы действий, размер сообщения фазы возврата) | transaction.cpp:3767, 3773, 3871, 3876, 3899, 3935-3944, 3968-3978, 3999-4005, 3459-3460, 3481, 3484; transaction-emulator.cpp:70-73 |
| `Transaction/Run.lean` (`Tx.runVm`, `Tx.computePhaseRun`, `GasPrices.maxGasThreshold`, `GasPrices.gasPriceOf`, `int64OfUInt64`) | лимиты газа VM — `long long` из `td::uint64` (раньше модель передавала их без приведения): от 2^63 отрицательны. Порог `compute_max_gas_threshold` умножает на разность `gas_limit - flat_gas_limit` как `long long`: от 2^63 порог отрицателен и любая сумма покупает весь лимит (раньше модель считала частное), VM сразу без газа, `serialize` отказывает. Максимум газа от 2^63 при лимите меньше 2^48 — `ACCEPT` ставит отрицательный лимит, газ кончается, `gas_used` (`td::uint64` от `std::min<long long>`) — максимум, `serialize` отказывает (раньше модель исполняла код до конца); предкомпилированный код с лимитом конфигурации от 2^63 — нехватка газа и отказ. Плата за газ от `gas_used - flat_gas_limit` ≥ 2^63 в C++ отрицательна — транзакция всё равно отказывает в `serialize`, модель её не берёт | transaction.cpp:1268-1275, 1298, 1315-1318, 1938, 1955-1956, 2016, 2027-2030; refint.h:42; vm.cpp:414-419 |
| `Transaction/Run.lean` (`Tx.runVm`) | адрес счёта на стеке тик-тока — `import_bits` его 256 бит со знаком (по умолчанию): адрес от 2^255 отрицателен (раньше модель клала его без знака, и `STU 256` адреса проходил там, где C++ даёт ошибку диапазона) | transaction.cpp:1463; bigint.hpp:644 |

### 1.7. Найдено доказательствами (фаза 7, 2026-10-22)

| Файл | Что изменено | Основание в C++ |
|---|---|---|
| `Exec/TonEnv/{Now,GetParam,GetParamAliases,Balance,GetPrecompiledGas,InMsgParam,PrevBlocksInfo,GetExtraBalance}.lean`, `Exec/Common.lean` (`getUnpackedConfigTuple`), `VM/Ops/State.lean` (`generateRandu256`), `Exec/Msg/SendMsg.lean` | кортеж параметров `c7[0]` длиннее 255 элементов — `type_chk` у каждого его читателя (`GETPARAM`, `GETPARAMLONG`, `NOW` и остальные псевдонимы, `INMSGPARAMS`, `INMSG_*`, `CONFIGDICT`, `CONFIGPARAM`, `CONFIGOPTPARAM`, `GLOBALID`, `GETPRECOMPILEDGAS`, `GETGASFEE` и прочие цены, `PREVMCBLOCKS` и др., `GETEXTRABALANCE`, `RANDU256`, `RAND`, `SENDMSG`); так же для распакованной конфигурации `c7[0][14]`, кортежа прошлых блоков `c7[0][13]` и баланса `c7[0][7]` в `GETEXTRABALANCE` (раньше модель читала кортеж любой длины; `SETRAND` и `ADDRAND` уже проверяли). Сам `c7` и параметры входящего сообщения `c7[0][17]` длиной не ограничены | `get_param`, `get_unpacked_config_tuple` (tonops.cpp:121-142), 264-273, 393-401, 537-542, 2138; `as_tuple_range` (stack.cpp:312-319) |

## 2. Тотальность (поведение не меняется)

Цель — чтобы все определения модели были тотальными и вычислимыми ядром Lean, без `partial` и без
недоказуемых циклов.

| Где | Что | Статус доказательства |
|---|---|---|
| `Basics/Bytes.lean` | циклы SHA-256/512 и упаковки битов через `List.range'` | **доказано** равенство исходному определению (`ModelEquiv`) |
| `Basics/Bytes.lean` | `countWhile` вместо циклов `while` (`SDCNT*`) | **доказано** `countWhile_eq` |
| `Cell/Primitives.lean` | поиск в словаре — структурная рекурсия | **доказаны** исходные уравнения (`*_eq`, `*_fuel`) |
| `Cell/Primitives.lean` | `dictLabelMatches` через `allBelow` | **доказано** равенство исходному |
| `Cell/Cell.lean` | `Cell.beq`, `computeLevelInfo?` — структурная взаимная рекурсия | **доказано**: `Cell.beq` удовлетворяет уравнению исходного определения (`Cell.beq_orig`), `computeLevelInfo?` — неподвижная точка исходного тела `Orig.levelBody` (`Cell.computeLevelInfo?_fix`; хвост тела перенесён в `levelInfoFromChildren`, `levelBody_split`) |
| `Instr/Codepage/Cp0.lean` | `takeRefsInv` вместо четырёх циклов декодера (`PUSHCONT`, `PUSHSLICE` r2, `PUSHSLICE_REFS`, `STSLICECONST`) | **доказано** равенство исходному циклу (`takeRefsInv_eq_orig`) |
| `Value/Value.lean` | `Value.beq`: `partial` → вполне обоснованная рекурсия (цикл `arrayBeqBy` по кортежу встроен, чтобы у элемента была граница индекса) | **доказано**: случай кортежа равен исходному `arrayBeqBy x y Value.beq` (`Value.beq_tuple`); остальные уравнения — исходные (плюс новый конструктор `nullCell`) |
| `Cont/Continuation.lean` | `Continuation.beq`: `partial` → структурная рекурсия | текст исходного определения (плюс случай нового конструктора `pushInt`): уравнения, которые порождает Lean, и есть исходные |
| `Exec/Dict/Ext.lean` (`pfx*WithCells`), `Exec/Misc.lean` (`CDATASIZE`) | `partial` → тотальные с доказанным завершением | не рефакторинг: переписаны по C++ (разделы 1.2, 1.5), с исходными не сравниваются |
| `Exec/Crypto/HashExt.lean` | цикл `while off < size` по 32-байтным кускам дайджеста → `hashExtChunks` (структурная рекурсия по числу кусков) | **доказано**: удовлетворяет уравнению исходного цикла (`hashExtChunks_loop`) |
| `Exec/Arith/Ext.lean` | `while q != 0` в `intToBigInt52Digits` → `intToBigInt52DigitsAux` с топливом `|q| + 1` | **доказано**: шаг уменьшает `|q|` (`bigint52_step_lt`), топлива больше `|q|` хватает и результат от него не зависит (`intToBigInt52DigitsAux_fuel`), исходное уравнение (`intToBigInt52DigitsAux_loop`) |
| `Exec/Crypto/Ext.lean` | `while 2^(l+1) ≤ n` в `blsMultiexpL` → `countWhile n` | **доказано**: граница `l < n` следует из условия, исходное уравнение без неё (`blsMultiexpL_loop`) |
| `Exec/Msg/SendMsg.lean` | обход ячеек сообщения | не рефакторинг: переписан по C++ (`VmStorageStat::add_storage`, раздел 1.2), вполне обоснованная рекурсия `VM.countMsgCells` с доказанным завершением (`termination_by`) |

## 3. Инфраструктура

- `Semantics/Contract.lean` — фаза исполнения (`computePhase`): начальное состояние, фиксация `c4/c5`, откат. Используется дифференциальным тестированием.
- `VmState.steps` — шаги VM, как их считает C++ (`vm_steps` транзакции): шаг с инструкцией, неявным
  `RET` или `JMPREF`, обработанное исключение, нехватка газа, шаги дочерней VM (`vm.cpp:458, 496,
  527, 778`); сверяется эмулятором транзакций.
- `Proofs/ModelEquiv.lean` — доказательства из раздела 2.
- `Proofs/DecEq.lean` — разрешимое равенство для ячеек и инструкций.
- `Apps/TestsSubset.lean` — прогон тестов изменённых инструкций.
- `Validation/{Diff,Oracle}/Runner.lean`, `oracle/fif/ton_oracle_runvm_lib.fif` — выбор глобальной версии в сверке.

## 4. Транзакции (фаза 5, начата 2026-10-20)

`TvmLean/Transaction/` — обычная транзакция по `crypto/block/transaction.cpp` в порядке эмулятора
транзакций (`emulator/transaction-emulator.cpp`): конфигурация (параметры 0, 5, 8, 12, 14, 18, 20/21,
24/25, 31, 43, 44, 45), счёт (`Account::unpack`, `init_new`), входящее сообщение, фазы хранения,
кредита, исполнения (газ, причины пропуска, развёртывание и разморозка по `StateInit`, `c7` всех
версий, предкомпилированный код), действий (`SENDRAWMSG`, `RAWRESERVE`, `SETCODE`, `CHANGELIB`,
штрафы, пределы состояния) и bounce (оба формата тела), новое состояние счёта (статистика хранения,
хэш словаря ячеек) и ячейка транзакции. Эталон — `libemulator.so` эталонной сборки
(`tools/txoracle/txoracle.py`); `tvm-lean-tx-test` сравнивает хэши транзакции и нового счёта:
случаи на всех версиях 0..16 и случайные транзакции (`--fuzz`), без расхождений. Tick-tock
(`emulateTickTock`, `transaction_emulator_emulate_tick_tock_transaction`): без сообщения и кредита, стек
`balance address is_tock -2`, весь газ, который покупает баланс, `in_msg_params` — нули и `addr_none`,
описание `trans_tick_tock$001`. Код — по `VmState::convert_code_cell`: с версии 9 ячейка-библиотека
разрешается библиотеками VM без газа, иначе (и для особой ячейки до версии 9) код — ячейка со ссылкой
на неё, и неявный `JMPREF` загружает её с газом (раньше модель исполняла биты самой ячейки); библиотеки
эмулятора (`set_libs`) — последняя коллекция VM на всех версиях. Адрес «чёрной дыры» (параметр 5)
сжигает граммы входящего сообщения; предкомпилированный контракт, которому не хватило газа в VM, —
отказ C++. Не смоделированы: split/merge (эмулятор их не запускает).

Предел загрузок библиотек транзакции (`max_transaction_library_loads`, параметр 43;
`VmState::load_library`, vm.cpp:643-670): VM помнит хэши библиотек, которые она загружала
(`VmState.loadedLibraries`; потомок `RUNVM` получает их и возвращает), и, когда их столько, сколько
разрешено (`VmState.maxLibraryLoads`), отвергает другую библиотеку как отсутствующую; пока их меньше,
библиотека записывается, даже если её потом не найдут. Словарные функции разрешают ячейки-библиотеки
чистой функцией, заданной на весь шаг, а множество в C++ растёт по ходу инструкции. Поэтому шаг
(`VmState.stepWith`) исполняется без отвергнутых библиотек, загрузки регистрируются в порядке C++
(`VmState.registerCellLoads`), и если C++ отверг бы библиотеку, которую шаг принял, шаг исполняется
заново с ней отвергнутой (C++ кончает инструкцию на первой отвергнутой библиотеке, поэтому второй
прогон — последний). Без предела ничего не меняется. Найдено по ходу: `CDATASIZE` загружал ячейки как
`load_cell_slice` (до версии 5 списывал газ за загрузку библиотеки ячейки-библиотеки), C++ — как
`load_cell_slice_special` (boc.cpp:1257): без библиотеки.

VM фазы исполнения строится функциями `computePhaseInit` и `computePhaseStack`, результат читается
`ComputeOutcome.ofHalt` (`TvmLean/Semantics/Contract.lean`, `Tx.runVm`, `Tx.computePhaseRun`): те же
определения, в которых формулируются теоремы о контрактах; `ComputeOutcome.gasUsed` — потраченный газ
не больше предела, как `cp.gas_used` (transaction.cpp:2016).

Дополнительные валюты (`ExtraCurrencyCollection`, `Transaction/Extra.lean`): сложение и вычитание
словарей повторяют `dict_combine_with` узел за узлом (поддеревья, которых операция не касается,
остаются прежними ячейками, перестроенные узлы получают метки `append_dict_label`), удаление нулей —
`dict_filter`, ограничение резерва — `CurrencyCollection::clamp`; суммы читаются `VarUInteger` из
`block-parse.cpp`, который отвергает ведущий нулевой байт (сгенерированный код TL-B списка действий —
нет). Значение исходящего сообщения и резерва проверяется как `block::tlb::t_CurrencyCollection`:
граммы без ведущего нулевого байта, суммы валют больше нуля (`VarUIntegerPos 32`), иначе действие
недопустимо (-1, код 34) — раньше модель этого не проверяла.

Чтения по `block-parse.cpp` (`block::tlb`, рукописный TL-B): `Account::unpack` проверяет `ShardAccount`
им (`t_ShardAccount.validate_csr`): `VarUInteger` без ведущего нулевого байта в балансе, статистике
хранения и долге, валюты баланса больше нуля; входящее сообщение — граммы значения
(`msg_balance_remaining.unpack`) и `extra_flags` (`t_Grams.as_integer`) так же; новая транзакция
проходит `block::tlb::t_Transaction.validate_ref`, и входящее сообщение в ней — единственная часть,
которую строит не транзакция (`messageValid`: `fwd_fee`, `import_fee`, валюты значения, адреса
`addr_var`). Сгенерированный код TL-B (`block-auto.cpp`) ведущий нулевой байт принимает: такие входы
модель раньше принимала, C++ — нет. Пути по версиям: до 10 валюты идут вместе с граммами (режим 128 — все валюты баланса, режим 64 —
валюты входящего сообщения, резерв их берёт, `original_balance` с валютами, удаление счёта — только без
валют); с 10 (`extra_currency_v2`) сообщение несёт только названные валюты без нулей, не больше
`max_msg_extra_currencies` (код 44), резерв валют — ошибка, счёт без граммов с валютами при удалении
становится `uninit`, статистика хранения не считает словарь баланса; с 9 — `clamp` резерва; до 13
словарь входящего сообщения входит в размер bounce. Хранение не удаляет счёт с валютами. Найдено по
ходу: до версии 9 `original_balance` ниже нуля (сборы больше прежнего баланса) недействителен, и резерв
от него (режим 4) — ошибка (раньше модель брала 0).

## Вынесено из модели (отдельный архив)

60 файлов доказательств путей контракта TON Storage, библиотека лемм об исполнении инструкций
(12 файлов) и генератор фикстур этого контракта. К модели TVM они не относятся.

## Открытые пункты на пути к полной модели

1. Доказать равенства, помеченные «не доказано» в разделе 2.
2. Аудит по исходникам C++ `3d478cb`: полный список опкодов и ветвей против модели; инструкции `EXTCALL`, `XCHG_IJ`, `SETCP_SHORT`.
3. Глобальные версии ниже 13: ветви закрыты (раздел 1.3); граница цепочки библиотек
   (`libraryChainBound`, 1024) и библиотека внутри коллекции библиотек до версии 4 (C++ следовал
   бы ей) не воспроизводятся.
4. Криптография — на Lean (раздел 1.4); внешних функций нет.
5. Фазы транзакции (раздел 4): split/merge (нет оракула).
6. Покрытие ветвей C++ при сверке (`gcov`): замер кода исполнения и `transaction.cpp` есть
   (`docs/coverage/README.md`), непокрытое разобрано; повторить замер `transaction.cpp` со случаями
   `Tests/Tx/Coverage.lean`.
7. Поле `savedC0` обычного продолжения (`Continuation.ordinary`) больше не читается семантикой и
   всегда `quit 0`: удалить (механическая правка ~400 мест).
