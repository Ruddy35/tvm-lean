# Аудит списаний газа без немедленной проверки лимита

Эталон: `ton-blockchain/ton` @ `3d478cb`. Дата: 2026-10-19.

## Правило

В C++ каждое списание газа — `VmState::consume_gas` → `GasLimits::consume_chk` (глобальная версия
≥ 4): при превышении лимита сразу бросается `VmNoGas`, исполнение прекращается, исключения TVM и
его газа нет, а израсходованным считается всё списанное до этого места включительно.

В модели часть списаний делалась без проверки (`st.consumeGas`, `consumeStackGas`,
`consumeTupleGas`, `registerChkSgnCall`); проверка выполнялась после инструкции. Это неотличимо от
C++, если **после такого списания в той же инструкции ничего не списывается и ничего не бросается**:
тогда модель останавливается после инструкции с тем же израсходованным газом и тем же наблюдаемым
результатом (стек заменяется на израсходованный газ, `c4`/`c5` — последние зафиксированные).
Расхождение возможно, только если после списания идут ещё списания (отчёт о газе больше) или
исключение (к нему добавляется газ исключения, 50).

Каждое место разобрано по C++; наблюдаемые закрыты случаями оракула с лимитом, пониженным
`SETGASLIMIT`, и исправлены (списание через проверяющие `VM.consumeGas` / проверку сразу после).

## Исправлено (расхождение воспроизведено оракулом)

| Место модели | C++ | Что было | Случаи оракула |
|---|---|---|---|
| `Exec/Crypto/HashExt.lean` | `exec_hash_ext`: `consume_gas` после каждого элемента | все элементы списывались до проверки; при не-срезе — ещё газ исключения | `HASHEXT{A}{R}`: `oracle/gas/*` |
| `Exec/TonEnv/GetExtraBalance.lean` | загрузки ячеек словаря через `register_cell_load` / `LocalVmState` | загрузки списывались без проверки и не списывались перед ошибкой | `GETEXTRABALANCE` |
| `Step/Step.lean`, `Step/Trace.lean`, `Exec/Flow/Runvm.lean` (ветка ошибки декодера) | `opctable.cpp`: `consume_gas(gas_per_instr + bits)`, затем `inv_opcode` | после переполнения ещё бросалось `inv_opcode` и списывалось 50 | `NOP`: `oracle/raw/gas/*` |
| `Step/Step.lean`, `Step/Trace.lean` (вход в продолжение с замыканием) | `adjust_jump_cont` → `consume_stack_gas` при прыжке (в т. ч. в `c2` из `throw_exception`) | газ стека замыкания проверялся только после списания следующей инструкции | `THROW`: `oracle/closure-handler/*` |
| `Exec/CellOp/Ext.lean` (`ENDXC`) | `finalize_copy` → `register_cell_create` до проверки особой ячейки | после переполнения бросалось `cell_ov` | `ENDXC`: `gas/invalid-special/*` |
| `Exec/TonEnv/SetRand.lean` | `consume_tuple_gas(tpay)`, затем `consume_tuple_gas(c7)` | оба списания до проверки | `SETRAND`: `oracle/gas/short-params/*` |
| `Exec/Crypto/Ext.lean` (34 цены) | фиксированная цена `consume_gas(price)`; у `RIST255_*` и `BLS_*` — до разбора операндов | после переполнения бросалась ошибка разбора, +50 | 23 набора: `oracle/gas-at-price/*` |

## Проверено, расхождения нет

| Место модели | Почему ненаблюдаемо |
|---|---|
| `Step/Step.lean`, `Step/Trace.lean`, `Exec/Flow/Runvm.lean`: газ инструкции, неявные `RET`/`JMPREF`, газ исключения, `RUNVM` (база, стек, оплата дочерней VM, возвращаемые значения) | за каждым списанием сразу следует проверка `gasRemaining < 0` |
| `Exec/Msg/*` (`SENDRAWMSG`, `SENDMSG`, `RAWRESERVE{X}`, `SETCODE`, `SETLIBCODE`, `CHANGELIB`) | создание ячейки действия — последнее, после него только запись `c5` |
| `Exec/Stack/{Roll,RollRev,ReverseX,BlkSwapX,OnlyTopX}` | доплата за глубину > 255 — последнее; дальше только перестановка |
| `Exec/Cell/Endc.lean`, `Exec/Cell/StbRef.lean`, `Exec/Crypto/HashSU.lean`, `Exec/Dict/DictGetNear.lean` | создание ячейки — последнее, дальше только запись в стек |
| `Exec/Crypto/{ChkSignU,ChkSignS}.lean` (`registerChkSgnCall`) | после него только проверка подписи и результат |
| `Exec/Tuple/*` (14), `Exec/TonEnv/{SetGlob,SetGlobVar}` | газ кортежа — единственное и последнее списание (`exec_untuple`, `exec_set_global_common` и др.) |
| `Exec/Exception/{Throw*,ThrowAny}` | газ исключения — последнее списание; `throw_exception` в C++ тоже списывает его последним перед прыжком в `c2` (газ стека замыкания — см. выше; отказ прыжка в замыкание, ждущее больше аргументов, — `docs/model-changes.md`, раздел 1.1) |
| `Exec/Exception/Try.lean`, `Exec/Common.lean` (`extract_cc`), `Exec/Cont/{SetContArgs,SetContVarArgs,ReturnArgs,Bless}` | газ стека — последнее списание; при разбиении стека не более 15 значений газ равен 0 (бесплатная глубина 32) |
| `VM/Ops/Cont.lean` (переходы и вызовы) | газ стека при прыжке — последнее списание инструкции |
| `VM/Ops/State.lean` (`RAND`, `RANDU256`) | первая доплата (`tpay`) всегда 0: семя читается из `c7[0][6]`, кортеж уже длиной ≥ 7 |

Вывод: после этих исправлений каждое списание, за которым в той же инструкции может последовать
другое списание или исключение, проверяет лимит сразу, как C++.
