# Покрытие инструкций символьным исполнением

Сгенерировано `tools/spec-coverage/spec_coverage.py` на коммите `cf7faf3`; руками не править. Пересоздать (на сервере сборки: нужна собранная библиотека доказательств, Fift эталона — только для `--regen`):

```sh
export LEAN_NUM_THREADS=1   # процессов × потоков не больше ядер: под перегрузкой пробы упираются в тайм-аут
python3 tools/spec-coverage/spec_coverage.py patterns --jobs 12 --timeout 2700 --save   # шаблоны: пробы (--regen: probes.txt из probes.fif)
python3 tools/spec-coverage/spec_coverage.py inventory --deep --jobs 14 --save --raw inv.tsv
python3 tools/spec-coverage/spec_coverage.py precheck --save   # контракты contracts.txt; после inventory (forms.json)
python3 tools/spec-coverage/spec_coverage.py inventory --from-raw inv.tsv --md docs/audit/spec-coverage.md
```

## Как считается

- **Формы инструкций** — 919 форм таблицы декодирования C++ (по одному набору тестов на форму): диапазоны 24-битных опкодов из `third_party/tvm-specification/tvm-specification.json` без `EXTCALL` (в эталоне его нет) и с `GETEXTRABALANCE` (в снимке его нет). Семейства — по категориям снимка (`continuation_cond_loop` — циклы; `codepage` — в cont/flow; `address` — в msg/actions; `config`, `globals`, `prng`, `basic_gas` — в tonenv/c7).
- Каждая форма перебирается по аргументам (все значения, если их не больше 256, иначе 64 по диапазону); опкод с хвостом из 999 нулей (иначе единиц) и четырьмя пустыми ссылками декодируется декодером модели, как его декодирует `vm_step`.
- **Лемма**: лемма `vm_spec`, чья инструкция унифицируется с декодированной (`withReducible isDefEq`, как `applySpec` в `TvmLean/Proofs/Exec/Tactic.lean`), из модулей, которые импортирует `TvmLean.Proofs.Check.Tactic` (их видит модуль `tools/contract-check`). Условия леммы на состояние (форма стека, факт кода) — то, что должен дать прогон.
- **Обработчик**: если ни одна лемма не подходит, `runInstr` исполняет обработчик модели (диспетчеры `execInstr` пройдены, программы VM считаются леммами `vm_run` или разворачиваются, `unfoldModelRun`). Статически: каждая программа VM обработчика либо считается леммой `vm_run`, либо разворачивается (нерекурсивное определение модели), либо **блокирует** (рекурсивная программа, комбинатор вне модели: `forIn`, ...).
- **Прогон** (`--deep`): первая выборка формы исполняется на символьном состоянии — стек из значений сигнатуры формы (целые, срезы, ячейки, построители, простые продолжения, кортежи; по снимку спецификации) поверх неизвестного стека, `c0` — простое продолжение возврата, `c7` — кортеж фазы исполнения из одного неизвестного значения, остальное неизвестно: (1) срабатывает ли лемма (`simp` только с `applySpec`, с разрядчиком `vm_disch`); (2) считается ли обработчик (`vm_simp`): в цели не остаётся ни `execInstr`, ни прогона программы (`ExceptT.run`), только `if` и `match` по неизвестным значениям (на них `vm_split` делит путь). Это приближение одного шага на самом общем состоянии: в настоящем прогоне состояние конкретнее (например, `CALLCC` и `AGAINBRK` здесь не посчитаны — `simp` упирается в глубину рекурсии, — а их пробы ниже проходят), и наоборот, посчитанный шаг не значит, что путь дойдёт до конца (`CONFIGOPTPARAM`); целые пути проверяют пробы шаблонов.

Статусы формы:

| Статус | Значение |
|---|---|
| лемма | лемма `vm_spec` подходит к каждой выборке и срабатывает на символьном стеке сигнатуры |
| лемма с условием | лемма подходит не ко всем аргументам, требует факта кода (словарь-константа) или условия, которого нет на общем символьном стеке (`c.special = false`, форма `c7`); остальное — обработчиком |
| лемма вне contract-check | лемма есть только в модулях, которые `TvmLean.Proofs.Check.Tactic` не импортирует (подключить импорт) |
| развёртка обработчика | леммы нет; обработчик считается развёрткой (прогон: посчитан) |
| не исполняется | леммы нет; обработчик блокирует или его прогон не считается |

## Итог по семействам

Сейчас, в окружении contract-check: **покрыто** — лемма (и лемма с условием); **развёртка** — обработчик считается (в том числе у форм с леммой вне contract-check: в скобках — сколько из них); **не исполняется** — остальное.

| Семейство | Форм | Лемма | Лемма с условием | Лемма вне contract-check (из них развёртка) | Развёртка обработчика | Не исполняется | Покрыто / развёртка / не исполняется сейчас |
|---|---:|---:|---:|---:|---:|---:|---|
| stack | 50 | 49 | 0 | 0 (0) | 0 | 1 | 49 / 0 / 1 |
| arith | 246 | 221 | 15 | 0 (0) | 10 | 0 | 236 / 10 / 0 |
| cell | 199 | 105 | 2 | 0 (0) | 92 | 0 | 107 / 92 / 0 |
| cont/flow | 85 | 23 | 3 | 0 (0) | 44 | 15 | 26 / 44 / 15 |
| loops | 16 | 8 | 0 | 0 (0) | 8 | 0 | 8 / 8 / 0 |
| exceptions | 17 | 7 | 0 | 0 (0) | 10 | 0 | 7 / 10 / 0 |
| dict | 143 | 4 | 74 | 0 (0) | 45 | 20 | 78 / 45 / 20 |
| tuple | 34 | 30 | 2 | 0 (0) | 2 | 0 | 32 / 2 / 0 |
| msg/actions | 13 | 2 | 3 | 0 (0) | 6 | 2 | 5 / 6 / 2 |
| tonenv/c7 | 55 | 2 | 11 | 0 (0) | 37 | 5 | 13 / 37 / 5 |
| crypto | 50 | 3 | 0 | 0 (0) | 33 | 14 | 3 / 33 / 14 |
| debug | 7 | 0 | 0 | 0 (0) | 7 | 0 | 0 / 7 / 0 |
| misc | 4 | 4 | 0 | 0 (0) | 0 | 0 | 4 / 0 / 0 |
| **всего** | **919** | **458** | **110** | **0** **(0)** | **294** | **57** | **568 / 294 / 57** |

Лемм `vm_spec`: 398, из них в импортах contract-check 398; вне их: нет.

## Шаблоны управления

Каждый шаблон проверяется пробами (`tools/spec-coverage/probes.fif`): маленький код запускается `ran_case` от начала внешнего сообщения (глобальная версия от 4) с инвариантом `True`; шаблон **исполняется**, если все пути прогона доходят до конца. Результаты — `tools/spec-coverage/probe-results.json`.

| Шаблон | Статус | Чем | Пробы | Где остановились пробы, которые не прошли | Чего не хватает |
|---|---|---|---|---|---|
| переход/вызов обычного продолжения без замыкания (`EXECUTE`/`CALLX`, `JMPX`, `IF`, `IFNOT`, `IFJMP`, `IFNOTJMP`, `IFELSE`, `RET`, `IFRET`) | исполняется | `Spec.execute`, `Spec.jmpx`, `Spec.if_`, `Spec.ifnot`, `Spec.ifjmp`, `Spec.ifnotjmp`, `Spec.ifelse`, `Spec.ret`, `Spec.ifret` (`Exec/Spec/Flow.lean`); `VM.run_jump_ordinary`, `VM.run_call_plain` | `callx`, `jmpx`, `ifelse-unknown` | — | — |
| переход/вызов продолжения с замыканием или `nargs` (`SETCONTARGS`, `BLESSARGS`, затем `EXECUTE`/`JMPX`) | исполняется | `Spec.setContArgs_ord`, `VM.run_jump_ordinary_cdata`, `VM.run_call_ordinary_cdata` (`Exec/Closure.lean`) | `closure-call`, `closure-jump` | — | — |
| `CALLXARGS` / `JMPXARGS` / `RETARGS` (число аргументов и результатов) | исполняется | обработчик; `VM.call`/`VM.jump` с `passArgs` | `callxargs`, `jmpxargs`, `retargs` | — | — |
| `CALLCC` и варианты (текущее продолжение как значение) | исполняется | обработчик (`VM.extractCc`) | `callcc`, `callccargs` | — | — |
| `RETALT` / `c1` (альтернативный возврат) | исполняется | обработчик | `retalt` | — | — |
| `REPEAT` / `UNTIL` с известным числом итераций | исполняется | `Spec.repeat_`, `Spec.until_` (`Exec/Spec/Loop.lean`); правило цикла (`vm_loop_c5`) | `repeat-const`, `until-const` | — | — |
| `REPEAT` / `UNTIL` / `WHILE` с неизвестным числом итераций, значение на стеке | исполняется | правило цикла `VmState.runWith_inv` в голове цикла (`vm_loop_c5`, `Contracts/Wallet3Run/Tactic.lean`): полезная нагрузка вершины стека обобщена, `c5` — `SafeActs` | `repeat-unknown`, `repeat-data`, `until-data`, `while-data` | — | — |
| `REPEATEND` / `UNTILEND` / `WHILEEND` / `AGAINEND` (тело — остаток кода) | исполняется | `Spec.untilEnd`, `Spec.whileEnd`, `Spec.againEnd`; `REPEATEND` — обработчиком | `repeatend`, `untilend`, `whileend`, `againend` | — | — |
| циклы `BRK` (`c1` — выход; `RETALT` выходит из цикла) | исполняется | обработчики | `againbrk`, `repeatbrk`, `untilbrk`, `whilebrk` | — | — |
| `AGAIN` без выхода (кончается нехваткой газа) | исполняется | `Spec.again` и правило цикла | `again` | — | — |
| цикл в цикле | исполняется | вложенные правила цикла (`check_loop_close` берёт последний `ih`) | `loop-in-loop` | — | — |
| `TRY` / `TRYARGS`: исключение ловит обработчик (`c2`) | исполняется | обработчик; `VM.run_throwToHandler` | `try-throw`, `try-nothrow`, `tryargs` | — | — |
| `THROW*` в обработчик по умолчанию (прогон останавливается с кодом выхода) | исполняется | `Spec.throw`, `Spec.throwIf`, `Spec.throwIfNot`, `Spec.throwArg`, `Spec.throwAny`; `VM.run_throwToHandler`, продолжение `excQuit` разворачивается | `throw`, `throwarg`, `throwif-unknown`, `throwifnot-unknown` | — | — |
| неявный `RET` в конце ячейки, неявный `JMPREF` на следующую ссылку | исполняется | `stepCode`: `VmState.stepOnceWith_implicitRet'`, `VmState.stepOnceWith_implicitJmpRef'` | `implicit-jmpref`, `nop` | — | — |
| `CALLREF` / `JMPREF` / `IF*REF` (продолжения в ссылках) | исполняется | обработчики (ссылка загружается как ячейка) | `callref`, `jmpref`, `ifjmpref` | — | — |
| диспетчер методов: `SETCP0`, `DICTPUSHCONST`, `DICTIGETJMPZ` по словарю кода | исполняется | `Spec.setcp0`, `Spec.dictPushConst`, `Spec.dictGetExec_*` (`Exec/Spec/Dispatch.lean`): поиск — замкнутый факт кода (`dictLookupLoads`, решает ядро) | `calldict` | — | — |
| `CALLDICT` / `JMPDICT` / `PREPAREDICT` (процедуры через `c3`) | исполняется | `Spec.callDict`, `Spec.jmpDict`, `Spec.prepareDict` | `calldict`, `jmpdict`, `preparedict` | — | — |
| `RUNVM` / `RUNVMX` (дочерняя VM) | нет | обработчик; прогон дочерней VM (`VmState.runWith`) рекурсивен | `runvm` | runvm: failed at cell code, bit 32: RUNVM 0 (the run is there) | прогон дочерней VM (`VmState.runWith`) — рекурсивная функция: обработчик не считается |
| `SETCP` с кодовой страницей не 0, `SETCPX` | исполняется | обработчик; `stepCode` требует `cp = 0` | `setcp1`, `setcpx` | — | — |
| действия `SENDRAWMSG` / `RAWRESERVE` (`c5`) | исполняется | `Spec.sendRawMsg`, `Spec.rawReserve`; `SafeActs` закрывает `c5` (`Check/Tactic.lean`) | `sendrawmsg`, `rawreserve` | — | — |
| действия `SETCODE` / `SETLIBCODE` / `CHANGELIB` / `SENDMSG` / `RAWRESERVEX` | нет | `Spec.setCode` исполняется; `ran_case` доказывает только инварианты неизменного кода, `SafeActs` допускает лишь `SENDRAWMSG` и `RAWRESERVE` | `setcode`, `setlibcode`, `changelib`, `sendmsg` | setcode: failed at cell code, bit 24: the implicit RET at the end of the cell; setlibcode: failed at cell code, bit 32: the implicit RET at the end of the cell; changelib: failed at cell code, bit 32: the implicit RET at the end of the cell; sendmsg: failed at cell code, bit 16: SENDMSG (the run is there) | по замыслу: `ran_case` доказывает инварианты неизменного кода, `SafeActs` допускает лишь `SENDRAWMSG` и `RAWRESERVE`; `SENDMSG` к тому же версии 4 |
| изменение `c4` / `c5` / `c7` (`POP c4`, `POP c5`, `POP c7`, `SETGLOB`) | исполняется | `Spec.popRoot` (`c4`); остальное — обработчиком | `c4-update`, `c5-update`, `c7-update`, `setglob` | — | — |
| `COMMIT` | исполняется | `Spec.commit`; `keeps_haltResult` проверяет зафиксированное состояние | `commit` | — | — |
| `ACCEPT` / `SETGASLIMIT` | исполняется | `Spec.accept`, `GasLimits.changeLimit_infty_min`; `SETGASLIMIT` — обработчиком | `accept`, `setgaslimit` | — | — |
| `DICTGET` / `DICTSET` по словарю, которого прогон не знает | частично | `Spec.dictGetInt_*` требуют фактов `dictLookupLoads`: замкнутых или гипотезы; `Exec/FramedDict.lean` — для обрамлённых ячеек | `dictget-unknown`, `dictset-unknown` | dictset-unknown: failed at cell code, bit 104: the implicit RET at the end of the cell (the run is there) | `DICTUGET`/`DICTUSET` по словарю из сообщения: леммам нужны факты `dictLookupLoads`, обработчик останавливается на загрузках ячеек поиска (`registerCellLoad` неизвестных ячеек) |
| перебор неизвестного словаря (`GETNEXT`/`PREV`/`MIN`/`MAX`) | нет | обработчик | `dictgetnext-unknown`, `dictmin-unknown` | dictgetnext-unknown: failed at cell code, bit 24: POP 0 (the run is there); dictmin-unknown: failed at cell code, bit 24: POP 0 (the run is there) | `GETNEXT`/`MIN` по неизвестному словарю: леммы нет, обработчик останавливается на инструкции |
| чтение конфигурации (`CONFIGPARAM`, `CONFIGOPTPARAM`) | исполняется | обработчик | `configparam`, `configoptparam` | — | — |
| параметры `c7` (`NOW`, `BALANCE`, `MYADDR`, `GETPARAM`) при неизвестном `c7` | исполняется | `Spec.getParam` и синонимы требуют гипотезы `c7[0]! = .tuple params`; иначе обработчик | `now` | — | — |
| опкод глобальной версии > 0 (например `GASCONSUMED`, v4) при символьной версии | исполняется | `stepCode`: `k ≤ globalVersion` — `decide` при известной версии, иначе `omega` из гипотез о версии (`hgv`); не решено — `if` на `k ≤ gv` (`VmState.stepOnceWith_instrVer'`) | `gasconsumed-v4` | — | — |

## Предпроверка контрактов

`contract-check <код> --precheck` (`spec_coverage.py precheck ... --save`): весь код, достижимый из корня (неявные `JMPREF`, `PUSHCONT`, `CALLREF`, `IF*REF`, процедуры `DICTPUSHCONST`), дизассемблирован декодером модели; каждая инструкция — по её точным аргументам (лемма), иначе по результату формы выше. Вхождения инструкций:

| Код | Инструкций | Форм | Лемма | Лемма для словаря-константы | Лемма вне contract-check | Развёртка обработчика | Не исполняется | Формы без леммы contract-check |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `wallet3` | 59 | 36 | 59 | 0 | 0 | 0 | 0 | — |
| `highload2` | 125 | 61 | 118 | 0 | 0 | 7 | 0 | `LDDICT`, `DICTIGETNEXT`, `DICTUREMMIN`, `PUSHREFCONT`, `STDICT` |
| `elector` | 2158 | 138 | 1967 | 0 | 0 | 188 | 3 | `CALLREF`, `STDICT`, `LDDICT`, `CONFIGOPTPARAM`, `POPCTR`, `DICTUGETPREV`, `REWRITESTDADDR`, `DICTUGETNEXT`, `PLDDICT`, `PUSHREFCONT`, `CHKSIGNS` (нет), `MULRSHIFT#` и ещё 5 |
| `config` | 1294 | 130 | 1205 | 0 | 0 | 87 | 2 | `CALLREF`, `STDICT`, `POPCTR`, `PUSHCTR`, `CONFIGOPTPARAM`, `LDDICT`, `DICTIGETOPTREF`, `MULRSHIFT#`, `BLESS`, `CHKSIGNS` (нет), `DICTISETGETOPTREF`, `DICTUGETPREV` и ещё 6 |
| `dns` | 436 | 100 | 408 | 0 | 0 | 28 | 0 | `CALLREF`, `LDDICT`, `PUSHCTR`, `STDICT`, `POPCTR`, `SDCUTLAST`, `BLESS`, `DICTUGETOPTREF`, `DICTUREMMIN`, `DICTUSETGETOPTREF`, `IFJMPREF`, `IFREF` и ещё 3 |
| `simple-wallet` | 38 | 30 | 38 | 0 | 0 | 0 | 0 | — |
| `wallet2` | 53 | 36 | 53 | 0 | 0 | 0 | 0 | — |
| `pow` | 311 | 85 | 300 | 0 | 0 | 8 | 3 | `ADDRAND` (нет), `CALLREF`, `MULRSHIFTR#`, `RANDU256`, `IFREFELSE` |
| `multisig` | 538 | 108 | 499 | 0 | 0 | 39 | 0 | `CALLREF`, `LDDICT`, `PUSHCTR`, `STDICT`, `DICTUGETNEXT`, `DICTUREMMIN`, `SDSKIPLAST`, `SETGASLIMIT` |
| `restricted3` | 163 | 63 | 150 | 0 | 0 | 13 | 0 | `CALLREF`, `LDDICT`, `DICTIGETPREVEQ`, `STDICT`, `CONFIGOPTPARAM`, `PUSHREFCONT` |
| `pchan` | 572 | 85 | 551 | 0 | 0 | 21 | 0 | `THROWANYIFNOT`, `CALLREF`, `IFREFELSE`, `IFREFELSEREF`, `THROWANYIF` |
| `highload1` | 72 | 46 | 70 | 0 | 0 | 2 | 0 | `DICTIGETNEXT`, `LDDICT` |
| `simple-wallet-ext` | 67 | 39 | 65 | 0 | 0 | 2 | 0 | `PUSHCTR` |
| `restricted1` | 129 | 57 | 124 | 0 | 0 | 5 | 0 | `CONFIGOPTPARAM`, `CALLREF`, `REWRITESTDADDR` |
| `restricted2` | 143 | 62 | 132 | 0 | 0 | 11 | 0 | `CALLREF`, `DICTIGETPREVEQ`, `LDDICT`, `STDICT`, `CONFIGOPTPARAM` |
| `dnsauto` | 875 | 120 | 828 | 0 | 0 | 47 | 0 | `CALLREF`, `LDDICT`, `DICTUMIN`, `GETGLOB`, `SDSKIPLAST`, `IFJMPREF`, `PUSHREFCONT`, `SDCUTLAST`, `SHA256U`, `STDICT`, `DICTUGETOPTREF`, `DICTUMAX` и ещё 2 |
| `storage` | 388 | 85 | 378 | 0 | 0 | 10 | 0 | `PUSHCTR`, `CALLREF`, `IFREFELSE`, `IFJMPREF`, `RAND`, `XCTOS` |
| `wallet4` | 376 | 92 | 359 | 0 | 0 | 16 | 1 | `LDDICT`, `STDICT`, `IFREFELSE`, `IFREF`, `DICTREMMIN` (нет), `REWRITESTDADDR`, `SDCUTFIRST` |
| `wallet5` | 320 | 97 | 293 | 0 | 0 | 27 | 0 | `POPCTR`, `REWRITESTDADDR`, `PLDDICT`, `SDBEGINSQ`, `CALLREF`, `RETALT`, `SAMEALTSAVE`, `SAVECTR`, `XCTOS`, `IFREFELSEREF`, `LDDICT`, `SDBEGINS` и ещё 3 |
| `jetton.minter` | 390 | 71 | 375 | 0 | 0 | 15 | 0 | `STDICT`, `IFJMPREF`, `IFREFELSE`, `MULRSHIFT#`, `REWRITESTDADDR`, `THROWANY` |
| `jetton.wallet` | 443 | 75 | 434 | 0 | 0 | 9 | 0 | `STDICT`, `IFREFELSEREF`, `LDDICT`, `MULRSHIFT#`, `REWRITESTDADDR`, `THROWANY` |
| `jetton1.minter` | 388 | 70 | 374 | 0 | 0 | 14 | 0 | `STDICT`, `IFJMPREF`, `IFREFELSE`, `REWRITESTDADDR`, `THROWANY` |
| `jetton1.wallet` | 439 | 75 | 430 | 0 | 0 | 9 | 0 | `STDICT`, `IFREFELSE`, `LDDICT`, `MULRSHIFT#`, `REWRITESTDADDR`, `THROWANY` |
| `nft.collection` | 291 | 73 | 283 | 0 | 0 | 8 | 0 | `IFJMPREF`, `STDICT`, `DICTUREMMIN`, `THROWANY`, `THROWANYIFNOT` |
| `nft.item` | 254 | 71 | 251 | 0 | 0 | 3 | 0 | `IFJMPREF`, `REWRITESTDADDR`, `THROWANY` |
| `nft2.item` | 257 | 73 | 250 | 0 | 0 | 7 | 0 | `IFJMPREF`, `IFREFELSE`, `MULRSHIFT#`, `REWRITESTDADDR`, `THROWANY` |

## Что не покрыто

**stack** (1): `REVX` (прогон обработчика: предел heartbeats).

**cont/flow** (15): `CALLXVARARGS` (прогон обработчика остановился на VM.call); `RETVARARGS` (прогон обработчика остановился на VM.jump); `CALLCCVARARGS` (прогон обработчика: предел heartbeats); `RUNVMX` (прогон обработчика: предел глубины рекурсии simp); `RETURNVARARGS` (прогон обработчика: предел heartbeats); `SETCONTVARARGS` (прогон обработчика: предел heartbeats); `BLESSVARARGS` (прогон обработчика: предел heartbeats); `SETCONTCTRMANYX` (прогон обработчика остановился на ForIn.forIn); `SETCONTCTRMANY` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика остановился на ForIn.forIn); `JMPXARGS` (прогон обработчика остановился на VM.jump); `RETARGS` (прогон обработчика остановился на VM.jump); `RETURNARGS` (прогон обработчика: предел heartbeats); `RUNVM` (прогон обработчика: предел глубины рекурсии simp); `CALLXARGS` (прогон обработчика остановился на VM.call); `CALLXARGS_1` (прогон обработчика остановился на VM.call).

**dict** (20): `DICTMINREF` (прогон обработчика: предел heartbeats); `DICTIMINREF` (прогон обработчика: предел heartbeats); `DICTUMINREF` (прогон обработчика: предел heartbeats); `DICTMAXREF` (прогон обработчика: предел heartbeats); `DICTIMAXREF` (прогон обработчика: предел heartbeats); `DICTUMAXREF` (прогон обработчика: предел heartbeats); `DICTREMMIN` (прогон обработчика: предел heartbeats); `DICTREMMINREF` (прогон обработчика: предел heartbeats); `DICTIREMMINREF` (прогон обработчика: предел heartbeats); `DICTUREMMINREF` (прогон обработчика: предел heartbeats); `DICTREMMAX` (прогон обработчика: предел heartbeats); `DICTREMMAXREF` (прогон обработчика: предел heartbeats); `DICTIREMMAXREF` (прогон обработчика: предел heartbeats); `DICTUREMMAX` (прогон обработчика: предел heartbeats); `DICTUREMMAXREF` (прогон обработчика: предел heartbeats); `DICTREPLACEB` (прогон обработчика: предел heartbeats); `DICTIREPLACEB` (прогон обработчика: предел heartbeats); `DICTUREPLACEB` (прогон обработчика: предел heartbeats); `SUBDICTGET` (прогон обработчика: предел heartbeats); `SUBDICTRPGET` (прогон обработчика: предел heartbeats).

**msg/actions** (2): `RAWRESERVEX` (прогон обработчика: предел heartbeats); `SENDMSG` (прогон обработчика: предел heartbeats).

**tonenv/c7** (5): `GETSTORAGEFEE` (прогон обработчика: предел heartbeats); `GETFORWARDFEE` (прогон обработчика: предел heartbeats); `GETFORWARDFEESIMPLE` (прогон обработчика: предел heartbeats); `ADDRAND` (прогон обработчика: предел heartbeats); `GETEXTRABALANCE` (прогон обработчика: предел heartbeats).

**crypto** (14): `CHKSIGNS` (прогон обработчика: предел heartbeats); `P256_CHKSIGNS` (прогон обработчика: предел heartbeats); `RIST255_MULBASE` (прогон обработчика: предел heartbeats); `RIST255_QMULBASE` (прогон обработчика: предел heartbeats); `BLS_AGGREGATE` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика остановился на ForIn.forIn); `BLS_FASTAGGREGATEVERIFY` (прогон обработчика остановился на ForIn.forIn); `BLS_AGGREGATEVERIFY` (прогон обработчика остановился на ForIn.forIn); `BLS_G1_MULTIEXP` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика остановился на ForIn.forIn); `BLS_G2_MULTIEXP` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика остановился на ForIn.forIn); `BLS_PAIRING` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика остановился на ForIn.forIn); `HASHEXT` (прогон обработчика: предел heartbeats); `HASHEXTR` (прогон обработчика: предел heartbeats); `HASHEXTA` (прогон обработчика: предел heartbeats); `HASHEXTAR` (прогон обработчика: предел heartbeats).

## Все формы

### stack

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `NOP` | лемма | nop | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `SWAP` | лемма | swap, xchg0 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `DUP` | лемма | push | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `OVER` | лемма | push | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `DROP` | лемма | drop, pop | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `NIP` | лемма | nip, pop | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `ROT` | лемма | rot | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `ROTREV` | лемма | rotRev, rotRev_any | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PICK` | лемма | pick | развёртка | лемма срабатывает; посчитан, ветвлений 20 |
| `ROLL` | лемма | roll | развёртка | лемма срабатывает; стоит на ForIn.forIn |
| `ROLLREV` | лемма | rollRev | развёртка | лемма срабатывает; стоит на ForIn.forIn |
| `BLKSWX` | лемма | blkSwapX | развёртка | лемма срабатывает; предел heartbeats |
| `REVX` | не исполняется | — | развёртка | предел heartbeats |
| `DROPX` | лемма | dropX | развёртка | лемма срабатывает; посчитан, ветвлений 20 |
| `TUCK` | лемма | tuck, tuck_any | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCHGX` | лемма | xchgX | развёртка | лемма срабатывает; посчитан, ветвлений 20 |
| `DEPTH` | лемма | depth | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `CHKDEPTH` | лемма | chkDepth | развёртка | лемма срабатывает; посчитан, ветвлений 20 |
| `ONLYTOPX` | лемма | onlyTopX | развёртка | лемма срабатывает; посчитан, ветвлений 28 |
| `ONLYX` | лемма | onlyX | развёртка | лемма срабатывает; посчитан, ветвлений 20 |
| `BLKDROP` | лемма | blkdrop | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `XC2PU` | лемма | xc2pu | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCPU2` | лемма | xcpu2 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUSH3` | лемма | push3 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCHG2` | лемма | xchg2 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCPU` | лемма | xcpu | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUSH2` | лемма | push2, push2_shape | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUXC` | лемма | puxc | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCPUXC` | лемма | xcpuxc | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUXC2` | лемма | puxc2 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUXCPU` | лемма | puxcpu | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PU2XC` | лемма | pu2xc | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `BLKSWAP` | лемма | blkSwap | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `REVERSE` | лемма | reverse | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `BLKPUSH` | лемма | blkPush | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; стоит на ForIn.forIn |
| `BLKDROP2` | лемма | blkdrop2 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `2SWAP` | лемма | twoSwap, twoSwap_shape | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `2DROP` | лемма | drop2, drop2_any | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `2DUP` | лемма | twoDup, twoDup_shape | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `2OVER` | лемма | twoOver, twoOver_shape | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCHG3` | лемма | xchg3 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCHG3_ALT` | лемма | xchg3 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCHG_0I_LONG` | лемма | swap, xchg0, xchg0_2 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCHG_0I` | лемма | xchg0, xchg0_2 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCHG_IJ` | лемма | xchg, xchg_any | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCHG_1I` | лемма | xchg1 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUSH` | лемма | push | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `PUSH_LONG` | лемма | push | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `POP` | лемма | pop | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `POP_LONG` | лемма | drop, nip, pop | развёртка | лемма срабатывает; посчитан, ветвлений 0 |

### arith

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `PUSHNAN` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `ADD` | лемма | add | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `SUB` | лемма | sub | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `SUBR` | лемма | subr | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `NEGATE` | лемма | negate | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `INC` | лемма | inc | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `DEC` | лемма | dec | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `MUL` | лемма | mul | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `POW2` | лемма | pow2 | развёртка | лемма срабатывает; посчитан, ветвлений 14 |
| `AND` | лемма | and_ | развёртка | лемма срабатывает; посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `OR` | лемма | or | развёртка | лемма срабатывает; посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `XOR` | лемма | xor | развёртка | лемма срабатывает; посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `NOT` | лемма с условием | not_ | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `FITSX` | лемма | fitsx | развёртка | лемма срабатывает; посчитан, ветвлений 15 |
| `UFITSX` | лемма | ufitsx | развёртка | лемма срабатывает; посчитан, ветвлений 15 |
| `BITSIZE` | лемма | bitsize | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `UBITSIZE` | лемма | ubitsize | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `MIN` | лемма | min | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `MAX` | лемма | max | развёртка | лемма срабатывает; посчитан, ветвлений 11 |
| `MINMAX` | лемма с условием | minmax | развёртка | посчитан, ветвлений 19 |
| `ABS` | лемма | abs | развёртка | лемма срабатывает; посчитан, ветвлений 15 |
| `QADD` | лемма | qadd | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QSUB` | лемма | qsub | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QSUBR` | лемма | qsubr | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QNEGATE` | лемма | qnegate | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QINC` | лемма | qinc | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QDEC` | лемма | qdec | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QMUL` | лемма | qmul | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QPOW2` | лемма | qpow2 | развёртка | лемма срабатывает; посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `QAND` | лемма | qand | развёртка | лемма срабатывает; посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `QOR` | лемма | qor | развёртка | лемма срабатывает; посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `QXOR` | лемма | qxor | развёртка | лемма срабатывает; посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `QNOT` | лемма | qnot | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QFITSX` | лемма | qfitsx | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `QUFITSX` | лемма | qufitsx | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `QBITSIZE` | лемма | qbitsize | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `QUBITSIZE` | лемма | ubitsize | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QMIN` | лемма | qmin | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QMAX` | лемма | qmax | развёртка | лемма срабатывает; посчитан, ветвлений 11 |
| `QMINMAX` | лемма с условием | qminmax | развёртка | посчитан, ветвлений 23 |
| `QABS` | лемма | abs | развёртка | лемма срабатывает; посчитан, ветвлений 15 |
| `SGN` | лемма | sgn | развёртка | лемма срабатывает; посчитан, ветвлений 10 |
| `LESS` | лемма | less | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `EQUAL` | лемма | equal | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `LEQ` | лемма | leq | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `GREATER` | лемма | greater | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `NEQ` | лемма | neq | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `GEQ` | лемма | geq | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `CMP` | лемма | cmp | развёртка | лемма срабатывает; посчитан, ветвлений 10 |
| `ISNAN` | лемма | isnan_nan, isnan_num | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `CHKNAN` | лемма | chknan_nan, chknan_num | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QSGN` | лемма | qsgn | развёртка | лемма срабатывает; посчитан, ветвлений 10 |
| `QLESS` | лемма | qless | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QEQUAL` | лемма | qequal | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QLEQ` | лемма | qleq | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QGREATER` | лемма | qgreater | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QNEQ` | лемма | qneq | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QGEQ` | лемма | qgeq | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QCMP` | лемма | qcmp | развёртка | лемма срабатывает; посчитан, ветвлений 10 |
| `ADDDIVMOD` | лемма | adddivmod | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `ADDDIVMODR` | лемма | adddivmod | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `ADDDIVMODC` | лемма | adddivmod | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `DIV` | лемма | div, divMod_nan_dividend, divMod_nan_divisor | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `DIVR` | лемма | div, divMod_nan_dividend, divMod_nan_divisor | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `DIVC` | лемма | div, divMod_nan_dividend, divMod_nan_divisor | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MOD` | лемма | divMod_nan_dividend, divMod_nan_divisor, mod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MODR` | лемма | divMod_nan_dividend, divMod_nan_divisor, mod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MODC` | лемма | divMod_nan_dividend, divMod_nan_divisor, mod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `DIVMOD` | лемма | divMod_nan_dividend, divMod_nan_divisor, divmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `DIVMODR` | лемма | divMod_nan_dividend, divMod_nan_divisor, divmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `DIVMODC` | лемма | divMod_nan_dividend, divMod_nan_divisor, divmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QADDDIVMOD` | лемма | adddivmod | развёртка | лемма срабатывает; посчитан, ветвлений 21 |
| `QADDDIVMODR` | лемма | adddivmod | развёртка | лемма срабатывает; посчитан, ветвлений 21 |
| `QADDDIVMODC` | лемма | adddivmod | развёртка | лемма срабатывает; посчитан, ветвлений 21 |
| `QDIV` | лемма | div, divMod_nan_dividend, divMod_nan_divisor | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QDIVR` | лемма | div, divMod_nan_dividend, divMod_nan_divisor | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QDIVC` | лемма | div, divMod_nan_dividend, divMod_nan_divisor | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMOD` | лемма | divMod_nan_dividend, divMod_nan_divisor, mod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMODR` | лемма | divMod_nan_dividend, divMod_nan_divisor, mod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMODC` | лемма | divMod_nan_dividend, divMod_nan_divisor, mod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QDIVMOD` | лемма | divMod_nan_dividend, divMod_nan_divisor, divmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QDIVMODR` | лемма | divMod_nan_dividend, divMod_nan_divisor, divmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QDIVMODC` | лемма | divMod_nan_dividend, divMod_nan_divisor, divmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `ADDRSHIFTMOD` | лемма с условием | addShrModVar | развёртка | предел глубины рекурсии simp |
| `ADDRSHIFTMODR` | лемма с условием | addShrModVar | развёртка | предел глубины рекурсии simp |
| `ADDRSHIFTMODC` | лемма с условием | addShrModVar | развёртка | предел глубины рекурсии simp |
| `RSHIFTR` | лемма | shrVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `RSHIFTC` | лемма | shrVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MODPOW2` | лемма | modPow2Var | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MODPOW2R` | лемма | modPow2Var | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MODPOW2C` | лемма | modPow2Var | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `RSHIFTMOD` | лемма | shrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `RSHIFTMODR` | лемма | shrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `RSHIFTMODC` | лемма | shrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QADDRSHIFTMOD` | лемма с условием | addShrModVar | развёртка | предел глубины рекурсии simp |
| `QADDRSHIFTMODR` | лемма с условием | addShrModVar | развёртка | предел глубины рекурсии simp |
| `QADDRSHIFTMODC` | лемма с условием | addShrModVar | развёртка | предел глубины рекурсии simp |
| `QRSHIFTR` | лемма | shrVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QRSHIFTC` | лемма | shrVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMODPOW2` | лемма | modPow2Var | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMODPOW2R` | лемма | modPow2Var | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMODPOW2C` | лемма | modPow2Var | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QRSHIFTMOD` | лемма | shrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QRSHIFTMODR` | лемма | shrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QRSHIFTMODC` | лемма | shrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULADDDIVMOD` | лемма | muladddivmod | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `MULADDDIVMODR` | лемма | muladddivmod | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `MULADDDIVMODC` | лемма | muladddivmod | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `MULDIV` | лемма | muldiv | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULDIVR` | лемма | muldiv | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULDIVC` | лемма | muldiv | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULMOD` | лемма | mulmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULMODR` | лемма | mulmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULMODC` | лемма | mulmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULDIVMOD` | лемма | muldivmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULDIVMODR` | лемма | muldivmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULDIVMODC` | лемма | muldivmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULADDDIVMOD` | лемма | muladddivmod | развёртка | лемма срабатывает; посчитан, ветвлений 21 |
| `QMULADDDIVMODR` | лемма | muladddivmod | развёртка | лемма срабатывает; посчитан, ветвлений 21 |
| `QMULADDDIVMODC` | лемма | muladddivmod | развёртка | лемма срабатывает; посчитан, ветвлений 21 |
| `QMULDIV` | лемма | muldiv | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULDIVR` | лемма | muldiv | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULDIVC` | лемма | muldiv | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULMOD` | лемма | mulmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULMODR` | лемма | mulmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULMODC` | лемма | mulmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULDIVMOD` | лемма | muldivmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULDIVMODR` | лемма | muldivmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULDIVMODC` | лемма | muldivmod | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULADDRSHIFTMOD` | лемма | mulAddShrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULADDRSHIFTRMOD` | лемма | mulAddShrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULADDRSHIFTCMOD` | лемма | mulAddShrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULRSHIFT` | лемма | mulShrVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULRSHIFTR` | лемма | mulShrVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULRSHIFTC` | лемма | mulShrVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULMODPOW2` | лемма | mulModPow2Var | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULMODPOW2R` | лемма | mulModPow2Var | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULMODPOW2C` | лемма | mulModPow2Var | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULRSHIFTMOD` | лемма | mulShrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULRSHIFTRMOD` | лемма | mulShrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULRSHIFTCMOD` | лемма | mulShrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULADDRSHIFTMOD` | лемма | mulAddShrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULADDRSHIFTRMOD` | лемма | mulAddShrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULADDRSHIFTCMOD` | лемма | mulAddShrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULRSHIFT` | лемма | mulShrVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULRSHIFTR` | лемма | mulShrVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULRSHIFTC` | лемма | mulShrVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULMODPOW2` | лемма | mulModPow2Var | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULMODPOW2R` | лемма | mulModPow2Var | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULMODPOW2C` | лемма | mulModPow2Var | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULRSHIFTMOD` | лемма | mulShrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULRSHIFTRMOD` | лемма | mulShrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QMULRSHIFTCMOD` | лемма | mulShrModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFTADDDIVMOD` | лемма с условием | shlAddDivModVar | развёртка | предел глубины рекурсии simp |
| `LSHIFTADDDIVMODR` | лемма с условием | shlAddDivModVar | развёртка | предел глубины рекурсии simp |
| `LSHIFTADDDIVMODC` | лемма с условием | shlAddDivModVar | развёртка | предел глубины рекурсии simp |
| `LSHIFTDIV` | лемма | shlDivVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFTDIVR` | лемма | shlDivVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFTDIVC` | лемма | shlDivVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFTMOD` | лемма | shlModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFTMODR` | лемма | shlModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFTMODC` | лемма | shlModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFTDIVMOD` | лемма | shlDivModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFTDIVMODR` | лемма | shlDivModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFTDIVMODC` | лемма | shlDivModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QLSHIFTADDDIVMOD` | лемма с условием | shlAddDivModVar | развёртка | предел глубины рекурсии simp |
| `QLSHIFTADDDIVMODR` | лемма с условием | shlAddDivModVar | развёртка | предел глубины рекурсии simp |
| `QLSHIFTADDDIVMODC` | лемма с условием | shlAddDivModVar | развёртка | предел глубины рекурсии simp |
| `QLSHIFTDIV` | лемма | shlDivVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QLSHIFTDIVR` | лемма | shlDivVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QLSHIFTDIVC` | лемма | shlDivVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QLSHIFTMOD` | лемма | shlModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QLSHIFTMODR` | лемма | shlModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QLSHIFTMODC` | лемма | shlModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QLSHIFTDIVMOD` | лемма | shlDivModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QLSHIFTDIVMODR` | лемма | shlDivModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QLSHIFTDIVMODC` | лемма | shlDivModVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `ADDINT` | лемма | addInt | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `MULINT` | лемма | mulInt | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `QADDINT` | лемма | qaddInt | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QMULINT` | лемма | qmulInt | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `EQINT` | лемма | eqInt | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `LESSINT` | лемма | lessInt | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `GTINT` | лемма | gtInt | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `NEQINT` | лемма | neqInt | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QEQINT` | лемма | qeqInt | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QLESSINT` | лемма | qlessInt | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QGTINT` | лемма | qgtInt | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QNEQINT` | лемма | qneqInt | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `PUSHPOW2DEC` | лемма | pushPow2Dec | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUSHNEGPOW2` | лемма | pushNegPow2 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `FITS` | лемма | fits | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `UFITS` | лемма | ufits | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QFITS` | лемма | fits | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QUFITS` | лемма | ufits | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `PUSHPOW2` | лемма | pushPow2 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `ADDRSHIFT#MOD` | лемма | addShrModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `ADDRSHIFTR#MOD` | лемма | addShrModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `ADDRSHIFTC#MOD` | лемма | addShrModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `RSHIFT#` | лемма | shrConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `RSHIFTR#` | лемма | shrConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `RSHIFTC#` | лемма | shrConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MODPOW2#` | лемма | modPow2Const | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MODPOW2R#` | лемма | modPow2Const | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MODPOW2C#` | лемма | modPow2Const | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `RSHIFT#MOD` | лемма | shrModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `RSHIFTR#MOD` | лемма | shrModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `RSHIFTC#MOD` | лемма | shrModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULADDRSHIFT#MOD` | лемма | mulAddShrModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULADDRSHIFTR#MOD` | лемма | mulAddShrModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULADDRSHIFTC#MOD` | лемма | mulAddShrModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `MULRSHIFT#` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `MULRSHIFTR#` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `MULRSHIFTC#` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `MULMODPOW2#` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `MULMODPOW2R#` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `MULMODPOW2C#` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `MULRSHIFT#MOD` | развёртка обработчика | — | развёртка | посчитан, ветвлений 10 |
| `MULRSHIFTR#MOD` | развёртка обработчика | — | развёртка | посчитан, ветвлений 10 |
| `MULRSHIFTC#MOD` | развёртка обработчика | — | развёртка | посчитан, ветвлений 10 |
| `LSHIFT#ADDDIVMOD` | лемма | shlAddDivModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFT#ADDDIVMODR` | лемма | shlAddDivModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFT#ADDDIVMODC` | лемма | shlAddDivModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFT#DIV` | лемма | shlDivConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFT#DIVR` | лемма | shlDivConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFT#DIVC` | лемма | shlDivConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFT#MOD` | лемма | shlModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFT#MODR` | лемма | shlModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFT#MODC` | лемма | shlModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFT#DIVMOD` | лемма | shlDivModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFT#DIVMODR` | лемма | shlDivModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFT#DIVMODC` | лемма | shlDivModConst | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LSHIFT_VAR` | лемма | lshift | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `LSHIFT` | лемма | lshiftConst | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QLSHIFT_VAR` | лемма | lshiftVar | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `QLSHIFT` | лемма | lshiftConst | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `RSHIFT_VAR` | лемма | rshift | развёртка | лемма срабатывает; посчитан, ветвлений 14 |
| `RSHIFT` | лемма | rshiftConst | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `RSHIFT_ALT` | лемма | shrVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `QRSHIFT_VAR` | лемма | rshiftVar | развёртка | лемма срабатывает; посчитан, ветвлений 15 |
| `QRSHIFT` | лемма | rshiftConst | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `QRSHIFT_ALT` | лемма | shrVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `PUSHINT_4` | лемма | pushInt | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUSHINT_8` | лемма | pushInt | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUSHINT_16` | лемма | pushInt | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUSHINT_LONG` | лемма | pushInt | развёртка | лемма срабатывает; посчитан, ветвлений 0 |

### cell

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `SEMPTY` | лемма | sempty | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `SDEMPTY` | лемма | sdempty | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `SREMPTY` | лемма | srempty | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `SDFIRST` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `SDLEXCMP` | развёртка обработчика | — | развёртка | посчитан, ветвлений 28 |
| `SDEQ` | лемма | sdEq | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `SDPFX` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SDPFXREV` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SDPPFX` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SDPPFXREV` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SDSFX` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `SDSFXREV` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `SDPSFX` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `SDPSFXREV` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `SDCNTLEAD0` | лемма | sdCntLead0 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `SDCNTLEAD1` | лемма | sdCntLead1 | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 0 |
| `SDCNTTRAIL0` | лемма | sdCntTrail0 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `SDCNTTRAIL1` | лемма | sdCntTrail1 | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 6 |
| `NEWC` | лемма | newc | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `ENDC` | лемма | endc | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `ENDCST` | развёртка обработчика | — | развёртка | посчитан, ветвлений 11 |
| `STBREF` | лемма | stbRef | развёртка | лемма срабатывает; посчитан, ветвлений 11 |
| `STB` | лемма | stb | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `STREFR` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `STBREFR` | лемма | stbRef_rev | развёртка | лемма срабатывает; посчитан, ветвлений 11 |
| `STSLICER` | лемма | stSlice_rev | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STBR` | лемма | stb_rev | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `STREFQ` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `STBREFQ` | лемма | stbRef | развёртка | лемма срабатывает; посчитан, ветвлений 11 |
| `STSLICEQ` | лемма | stSlice | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `STBQ` | лемма | stb | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `STREFRQ` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `STBREFRQ` | лемма | stbRef_rev | развёртка | лемма срабатывает; посчитан, ветвлений 11 |
| `STSLICERQ` | лемма | stSlice_rev | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STBRQ` | лемма | stb_rev | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `ENDXC` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `BDEPTH` | лемма | bdepth | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; стоит на ForIn.forIn |
| `BBITS` | лемма | bbits | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `BREFS` | лемма | brefs | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 0 |
| `BBITREFS` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `BREMBITS` | лемма | brembits | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 0 |
| `BREMREFS` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `BREMBITREFS` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `BCHKREFS` | лемма | bchkRefs | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; предел глубины рекурсии simp |
| `BCHKBITREFS` | лемма | bchkBitRefs | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; предел глубины рекурсии simp |
| `BCHKREFSQ` | лемма | bchkRefs | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; предел глубины рекурсии simp |
| `BCHKBITREFSQ` | лемма | bchkBitRefs | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; предел глубины рекурсии simp |
| `STZEROES` | развёртка обработчика | — | развёртка | посчитан, ветвлений 15 |
| `STONES` | развёртка обработчика | — | развёртка | посчитан, ветвлений 15 |
| `STSAME` | развёртка обработчика | — | развёртка | посчитан, ветвлений 23 |
| `CTOS` | лемма с условием | ctos_mkOrdinary, ctos | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `ENDS` | лемма | ends | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `LDREF` | лемма | ldref | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `LDREFRTOS` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `SDCUTFIRST` | развёртка обработчика | — | развёртка | посчитан, ветвлений 15 |
| `SDSKIPFIRST` | лемма | sdskipfirst | развёртка | лемма срабатывает; посчитан, ветвлений 15 |
| `SDCUTLAST` | развёртка обработчика | — | развёртка | посчитан, ветвлений 15 |
| `SDSKIPLAST` | развёртка обработчика | — | развёртка | посчитан, ветвлений 15 |
| `SDSUBSTR` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 23 |
| `SCUTFIRST` | лемма | scutfirst | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 23 |
| `SSKIPFIRST` | лемма | sskipfirst | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 23 |
| `SCUTLAST` | лемма | scutlast | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 23 |
| `SSKIPLAST` | лемма | sskiplast | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 23 |
| `SUBSLICE` | лемма | subslice | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; предел heartbeats |
| `SPLIT` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 23 |
| `SPLITQ` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 23 |
| `XCTOS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 11 |
| `XLOAD` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `XLOADQ` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SCHKBITS` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 15 |
| `SCHKREFS` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 15 |
| `SCHKBITREFS` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 23 |
| `SCHKBITSQ` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 15 |
| `SCHKREFSQ` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 15 |
| `SCHKBITREFSQ` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 23 |
| `PLDREFVAR` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 15 |
| `SBITS` | лемма | sbits | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `SREFS` | лемма | srefs | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `SBITREFS` | лемма | sbitrefs | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `LDZEROES` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `LDONES` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `LDSAME` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 15 |
| `SDEPTH` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `CDEPTH` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `CLEVEL` v6 | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `CLEVELMASK` v6 | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `CHASHIX` v6 | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: Cell.computeLevelInfo? |
| `CDEPTHIX` v6 | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: Cell.computeLevelInfo? |
| `LDGRAMS` | лемма | ldGrams | блок: liftM (вне модели, нет леммы vm_run) | лемма срабатывает; стоит на liftM |
| `LDVARINT16` | лемма | ldVarInt | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STGRAMS` | лемма | stGrams | развёртка | лемма срабатывает; посчитан, ветвлений 14 |
| `STVARINT16` | лемма | stVarInt | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LDVARUINT32` | лемма | ldVarInt | развёртка | лемма срабатывает; стоит на liftM |
| `LDVARINT32` | лемма | ldVarInt | развёртка | лемма срабатывает; стоит на liftM |
| `STVARUINT32` | лемма | stVarUInt | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STVARINT32` | лемма | stVarInt | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LDMSGADDR` | лемма | ldMsgAddr, ldMsgAddr_any, ldMsgAddr_error | развёртка | лемма срабатывает; посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `LDMSGADDRQ` | лемма с условием | ldMsgAddr, ldMsgAddr_error | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `STIX` | лемма | stIntVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STUX` | лемма | stIntVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STIXR` | лемма | stIntVar_rev | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STUXR` | лемма | stIntVar_rev | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STIXQ` | лемма | stIntVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STUXQ` | лемма | stIntVar | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STIXRQ` | лемма | stIntVar_rev | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STUXRQ` | лемма | stIntVar_rev | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STILE4` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `STULE4` | развёртка обработчика | — | развёртка | посчитан, ветвлений 10 |
| `STILE8` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `STULE8` | развёртка обработчика | — | развёртка | посчитан, ветвлений 10 |
| `LDIX` | лемма | loadIntVar | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `LDUX` | лемма | loadIntVar | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `PLDIX` | лемма | loadIntVar | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `PLDUX` | лемма | loadIntVar | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `LDIXQ` | лемма | loadIntVar | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `LDUXQ` | лемма | loadIntVar | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `PLDIXQ` | лемма | loadIntVar | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `PLDUXQ` | лемма | loadIntVar | развёртка | лемма срабатывает; посчитан, ветвлений 19 |
| `LDSLICEX` | лемма | ldslicex, loadSliceX | развёртка | лемма срабатывает; посчитан, ветвлений 15 |
| `PLDSLICEX` | лемма | loadSliceX | развёртка | лемма срабатывает; посчитан, ветвлений 15 |
| `LDSLICEXQ` | лемма | loadSliceX | развёртка | лемма срабатывает; посчитан, ветвлений 15 |
| `PLDSLICEXQ` | лемма | loadSliceX | развёртка | лемма срабатывает; посчитан, ветвлений 15 |
| `LDILE4` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `LDULE4` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `LDILE8` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `LDULE8` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `PLDILE4` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `PLDULE4` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `PLDILE8` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `PLDULE8` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `LDILE4Q` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `LDULE4Q` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `LDILE8Q` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `LDULE8Q` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `PLDILE4Q` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `PLDULE4Q` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `PLDILE8Q` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `PLDULE8Q` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `PLDREFIDX` | лемма | pldRefIdx | развёртка | лемма срабатывает; посчитан, ветвлений 10 |
| `CHASHI` v6 | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: Cell.computeLevelInfo? |
| `CDEPTHI` v6 | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: Cell.computeLevelInfo? |
| `STIR` | лемма | stIntFixed_rev | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STUR` | лемма | stIntFixed_rev | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STIQ` | лемма | stIntFixed | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STUQ` | лемма | stIntFixed | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STIRQ` | лемма | stIntFixed_rev | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STURQ` | лемма | stIntFixed_rev | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `PLDI` | лемма | loadInt | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `PLDU` | лемма | loadInt | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LDIQ` | лемма | loadIntQ | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LDUQ` | лемма | loadIntQ | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `PLDIQ` | лемма | loadIntQ | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `PLDUQ` | лемма | loadIntQ | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `PLDUZ` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `PLDSLICE` | лемма | loadSliceFixed, loadSliceFixed_any | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `LDSLICEQ` | лемма | loadSliceFixed_any | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `PLDSLICEQ` | лемма | loadSliceFixed_any | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `PUSHREF` | лемма | pushRef | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUSHREFSLICE` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `PUSHREFCONT` | лемма | pushRefCont | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `SDBEGINSX` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SDBEGINSXQ` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SDBEGINS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SDBEGINSQ` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `STREFCONST` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `STREF2CONST` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `STREF` | лемма | stref | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `STREF_ALT` | лемма | stref | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `STSLICE` | лемма | stSlice | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `STSLICE_ALT` | лемма | stSlice | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `STI` | лемма | sti | развёртка | лемма срабатывает; посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `STI_ALT` | лемма | stIntFixed | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `STU` | лемма | stu | развёртка | лемма срабатывает; посчитан, ветвлений 10 |
| `STU_ALT` | лемма | stIntFixed | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LDI` | лемма | loadInt | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LDI_ALT` | лемма | loadInt | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LDU` | лемма | ldu | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `LDU_ALT` | лемма | loadInt | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LDSLICE` | лемма | loadSliceFixed, loadSliceFixed_any | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `LDSLICE_ALT` | лемма | loadSliceFixed, loadSliceFixed_any | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `BCHKBITS_VAR` | лемма | bchkBits | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; предел глубины рекурсии simp |
| `BCHKBITS` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `BCHKBITSQ_VAR` | лемма | bchkBits | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; предел глубины рекурсии simp |
| `BCHKBITSQ` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `PUSHSLICE` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `PUSHSLICE_REFS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `PUSHSLICE_LONG` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `PUSHCONT` | лемма | pushCont | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUSHCONT_SHORT` | лемма | pushCont | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `STSLICECONST` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `BTOS` v12 | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `LDSTDADDR` v12 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `LDSTDADDRQ` v12 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `LDOPTSTDADDR` v12 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `LDOPTSTDADDRQ` v12 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `STSTDADDR` v12 | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `STSTDADDRQ` v12 | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `STOPTSTDADDR` v12 | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `STOPTSTDADDRQ` v12 | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |

### cont/flow

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `EXECUTE` | лемма | execute | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `JMPX` | лемма | jmpx | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `RET` | лемма | ret, ret_quit | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `RETALT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `RETBOOL` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `CALLCC` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `JMPXDATA` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `CALLXVARARGS` | не исполняется | — | развёртка | стоит на VM.call; остаются термами: VM.call |
| `RETVARARGS` | не исполняется | — | развёртка | стоит на VM.jump; остаются термами: VM.jump |
| `JMPXVARARGS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 16 |
| `CALLCCVARARGS` | не исполняется | — | развёртка | предел heartbeats |
| `RETDATA` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `RUNVMX` v4 | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `IFRET` | лемма | ifret | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `IFNOTRET` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `IF` | лемма | if_ | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `IFNOT` | лемма | ifnot | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `IFJMP` | лемма | ifjmp | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `IFNOTJMP` | лемма | ifnotjmp | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `IFELSE` | лемма | ifelse | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `CONDSEL` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `CONDSELCHK` | развёртка обработчика | — | развёртка | посчитан, ветвлений 10 |
| `IFRETALT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `IFNOTRETALT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `RETURNVARARGS` | не исполняется | — | развёртка | предел heartbeats |
| `SETCONTVARARGS` | не исполняется | — | развёртка | предел heartbeats |
| `SETNUMVARARGS` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `BLESS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `BLESSVARARGS` | не исполняется | — | развёртка | предел heartbeats |
| `PUSHCTRX` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `POPCTRX` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SETCONTCTRX` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SETCONTCTRMANYX` v9 | не исполняется | — | развёртка | стоит на ForIn.forIn |
| `BOOLAND` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `BOOLOR` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `COMPOSBOTH` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `ATEXIT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `ATEXITALT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `SETEXITALT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `THENRET` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `THENRETALT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `INVERT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `BOOLEVAL` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `SAMEALT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `SAMEALTSAVE` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `SETCONTCTRMANY` v9 | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `CALLCCARGS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `JMPDICT` | лемма | jmpDict | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PREPAREDICT` | лемма | prepareDict | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `JMPXARGS` | не исполняется | — | развёртка | стоит на VM.jump; остаются термами: VM.jump |
| `RETARGS` | не исполняется | — | развёртка | стоит на VM.jump; остаются термами: VM.jump |
| `RETURNARGS` | не исполняется | — | развёртка | предел heartbeats |
| `SETCONTARGS` | лемма с условием | setContArgs_ord | развёртка | предел глубины рекурсии simp |
| `BLESSARGS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `IFBITJMP` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `IFNBITJMP` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `CALLREF` | лемма | callRef | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `JMPREF` | лемма | jmpRef | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `JMPREFDATA` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `IFREF` | лемма | ifref | развёртка | лемма срабатывает; посчитан, ветвлений 11 |
| `IFNOTREF` | лемма | ifnotref | развёртка | лемма срабатывает; посчитан, ветвлений 11 |
| `IFJMPREF` | лемма | ifjmpref | развёртка | лемма срабатывает; посчитан, ветвлений 11 |
| `IFNOTJMPREF` | лемма | ifnotjmpref | развёртка | лемма срабатывает; посчитан, ветвлений 11 |
| `IFREFELSE` | лемма | ifrefElse | развёртка | лемма срабатывает; посчитан, ветвлений 11 |
| `IFELSEREF` | лемма | ifelseRef | развёртка | лемма срабатывает; посчитан, ветвлений 11 |
| `IFREFELSEREF` | лемма | ifrefElseRef | развёртка | лемма срабатывает; посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads, VM.call |
| `IFBITJMPREF` | развёртка обработчика | — | развёртка | посчитан, ветвлений 11 |
| `IFNBITJMPREF` | развёртка обработчика | — | развёртка | посчитан, ветвлений 11 |
| `SETCONTCTR` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SETRETCTR` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SETALTCTR` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `POPSAVE` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SAVECTR` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SAVEALTCTR` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SAVEBOTHCTR` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `RUNVM` v4 | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `CALLDICT` | лемма | callDict | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `CALLDICT_LONG` | лемма | callDict | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUSHCTR` | лемма | pushCtr0, pushCtr1, pushCtr2, pushCtr3, pushCtr5, pushCtr7, pushRoot | развёртка | лемма срабатывает; посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `POPCTR` | лемма с условием | popCtr0, popCtr1, popCtr2, popCtr3, popCtr5, popCtr7, popRoot | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `CALLXARGS` | не исполняется | — | развёртка | стоит на VM.call; остаются термами: VM.call |
| `CALLXARGS_1` | не исполняется | — | развёртка | стоит на VM.call; остаются термами: VM.call |
| `SETCP` | лемма с условием | setcp0 (1/240 аргументов) | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `SETCPX` | развёртка обработчика | — | развёртка | посчитан, ветвлений 10 |
| `SETCP_SHORT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |

### loops

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `REPEAT` | лемма | repeat_ | развёртка | лемма срабатывает; посчитан, ветвлений 11 |
| `REPEATEND` | развёртка обработчика | — | развёртка | посчитан, ветвлений 11 |
| `UNTIL` | лемма | until_ | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `UNTILEND` | лемма | untilEnd | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `WHILE` | лемма | while_ | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `WHILEEND` | лемма | whileEnd | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `AGAIN` | лемма | again | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `AGAINEND` | лемма | againEnd | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `REPEATBRK` | развёртка обработчика | — | развёртка | посчитан, ветвлений 11 |
| `REPEATENDBRK` | развёртка обработчика | — | развёртка | посчитан, ветвлений 11 |
| `UNTILBRK` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `UNTILENDBRK` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `WHILEBRK` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `WHILEENDBRK` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `AGAINBRK` | лемма | againBrk | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `AGAINENDBRK` | развёртка обработчика | — | развёртка | посчитан, ветвлений 5 |

### exceptions

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `TRY` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `THROWANY` | развёртка обработчика | — | развёртка | посчитан, ветвлений 18 |
| `THROWARGANY` | развёртка обработчика | — | развёртка | посчитан, ветвлений 18 |
| `THROWANYIFNOT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 23 |
| `THROWARGANYIFNOT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 23 |
| `TRYARGS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `THROWARG` | лемма | throwArg | развёртка | лемма срабатывает; посчитан, ветвлений 10 |
| `THROWARGIF` | развёртка обработчика | — | развёртка | посчитан, ветвлений 15 |
| `THROWARGIFNOT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 15 |
| `THROWANYIF` | развёртка обработчика | — | развёртка | посчитан, ветвлений 23 |
| `THROWARGANYIF` | развёртка обработчика | — | развёртка | посчитан, ветвлений 23 |
| `THROW_SHORT` | лемма | throw | развёртка | лемма срабатывает; посчитан, ветвлений 10 |
| `THROW` | лемма | throw | развёртка | лемма срабатывает; посчитан, ветвлений 10 |
| `THROWIF_SHORT` | лемма | throwIf | развёртка | лемма срабатывает; посчитан, ветвлений 15 |
| `THROWIF` | лемма | throwIf | развёртка | лемма срабатывает; посчитан, ветвлений 15 |
| `THROWIFNOT_SHORT` | лемма | throwIfNot | развёртка | лемма срабатывает; посчитан, ветвлений 15 |
| `THROWIFNOT` | лемма | throwIfNot | развёртка | лемма срабатывает; посчитан, ветвлений 15 |

### dict

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `STDICT` | лемма | stdict_cell, stdict_null | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `SKIPDICT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 15 |
| `LDDICTS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 15 |
| `PLDDICTS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 15 |
| `LDDICT` | лемма | lddict | развёртка | лемма срабатывает; посчитан, ветвлений 20 |
| `PLDDICT` | лемма | plddict | развёртка | лемма срабатывает; посчитан, ветвлений 20 |
| `LDDICTQ` | развёртка обработчика | — | развёртка | посчитан, ветвлений 20 |
| `PLDDICTQ` | развёртка обработчика | — | развёртка | посчитан, ветвлений 20 |
| `PFXDICTSET` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `PFXDICTREPLACE` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `PFXDICTADD` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `PFXDICTDEL` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `PFXDICTGETQ` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `PFXDICTGET` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `PFXDICTGETJMP` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `PFXDICTGETEXEC` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTIGETJMP` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETJMP` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTIGETEXEC` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETEXEC` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTIGETJMPZ` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETJMPZ` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTIGETEXECZ` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETEXECZ` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTGET` | лемма с условием | dictGetSlice_found, dictGetSlice_notFound, dictGetSlice_short, dictGetSlice_wf | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTGETREF` | лемма с условием | dictGetSlice_wf | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTIGET` | лемма с условием | dictGetInt_empty, dictGetInt_found, dictGetInt_noKey, dictGetInt_notFound, dictGetInt_wf | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTIGETREF` | лемма с условием | dictGetIntRef_found, dictGetIntRef_notFound, dictGetInt_wf | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGET` | лемма с условием | dictGetInt_empty, dictGetInt_found, dictGetInt_noKey, dictGetInt_notFound, dictGetInt_wf | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETREF` | лемма с условием | dictGetIntRef_found, dictGetIntRef_notFound, dictGetInt_wf | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTSET` | лемма с условием | dictSetSliceEmpty_flag, dictSetSliceEmpty_set, dictSetSlice_flag, dictSetSlice_set | развёртка | предел глубины рекурсии simp |
| `DICTSETREF` | лемма с условием | dictSetSliceRefEmpty_flag, dictSetSliceRefEmpty_set, dictSetSliceRef_flag, dictSetSliceRef_set | развёртка | предел глубины рекурсии simp |
| `DICTISET` | лемма с условием | dictSetIntEmpty_flag, dictSetIntEmpty_set, dictSetInt_flag, dictSetInt_set | развёртка | предел heartbeats |
| `DICTISETREF` | лемма с условием | dictSetIntRefEmpty_flag, dictSetIntRefEmpty_set, dictSetIntRef_flag, dictSetIntRef_set | развёртка | предел heartbeats |
| `DICTUSET` | лемма с условием | dictSetIntEmpty_flag, dictSetIntEmpty_set, dictSetInt_flag, dictSetInt_set | развёртка | предел heartbeats |
| `DICTUSETREF` | лемма с условием | dictSetIntRefEmpty_flag, dictSetIntRefEmpty_set, dictSetIntRef_flag, dictSetIntRef_set | развёртка | предел heartbeats |
| `DICTSETGET` | лемма с условием | dictSetGetSlice, dictSetGetSliceEmpty | развёртка | предел глубины рекурсии simp |
| `DICTSETGETREF` | лемма с условием | dictSetGetSliceRef, dictSetGetSliceRefEmpty | развёртка | предел глубины рекурсии simp |
| `DICTISETGET` | лемма с условием | dictSetGetInt, dictSetGetIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTISETGETREF` | лемма с условием | dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUSETGET` | лемма с условием | dictSetGetInt, dictSetGetIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUSETGETREF` | лемма с условием | dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTREPLACE` | лемма с условием | dictSetSliceEmpty_flag, dictSetSlice_flag | развёртка | предел heartbeats |
| `DICTREPLACEREF` | лемма с условием | dictSetSliceRefEmpty_flag, dictSetSliceRef_flag | развёртка | предел heartbeats |
| `DICTIREPLACE` | лемма с условием | dictSetIntEmpty_flag, dictSetInt_flag | развёртка | предел heartbeats |
| `DICTIREPLACEREF` | лемма с условием | dictSetIntRefEmpty_flag, dictSetIntRef_flag | развёртка | предел heartbeats |
| `DICTUREPLACE` | лемма с условием | dictSetIntEmpty_flag, dictSetInt_flag | развёртка | предел heartbeats |
| `DICTUREPLACEREF` | лемма с условием | dictSetIntRefEmpty_flag, dictSetIntRef_flag | развёртка | предел heartbeats |
| `DICTREPLACEGET` | лемма с условием | dictSetGetSlice, dictSetGetSliceEmpty | развёртка | предел глубины рекурсии simp |
| `DICTREPLACEGETREF` | лемма с условием | dictSetGetSliceRef, dictSetGetSliceRefEmpty | развёртка | предел глубины рекурсии simp |
| `DICTIREPLACEGET` | лемма с условием | dictSetGetInt, dictSetGetIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTIREPLACEGETREF` | лемма с условием | dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUREPLACEGET` | лемма с условием | dictSetGetInt, dictSetGetIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUREPLACEGETREF` | лемма с условием | dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTADD` | лемма с условием | dictSetSliceEmpty_flag, dictSetSlice_flag | развёртка | предел heartbeats |
| `DICTADDREF` | лемма с условием | dictSetSliceRefEmpty_flag, dictSetSliceRef_flag | развёртка | предел heartbeats |
| `DICTIADD` | лемма с условием | dictSetIntEmpty_flag, dictSetInt_flag | развёртка | предел heartbeats |
| `DICTIADDREF` | лемма с условием | dictSetIntRefEmpty_flag, dictSetIntRef_flag | развёртка | предел heartbeats |
| `DICTUADD` | лемма с условием | dictSetIntEmpty_flag, dictSetInt_flag | развёртка | предел heartbeats |
| `DICTUADDREF` | лемма с условием | dictSetIntRefEmpty_flag, dictSetIntRef_flag | развёртка | предел heartbeats |
| `DICTADDGET` | лемма с условием | dictSetGetSlice, dictSetGetSliceEmpty | развёртка | предел глубины рекурсии simp |
| `DICTADDGETREF` | лемма с условием | dictSetGetSliceRef, dictSetGetSliceRefEmpty | развёртка | предел глубины рекурсии simp |
| `DICTIADDGET` | лемма с условием | dictSetGetInt, dictSetGetIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTIADDGETREF` | лемма с условием | dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUADDGET` | лемма с условием | dictSetGetInt, dictSetGetIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUADDGETREF` | лемма с условием | dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTDELGET` | лемма с условием | dictSetGetSlice, dictSetGetSliceEmpty | развёртка | предел глубины рекурсии simp |
| `DICTDELGETREF` | лемма с условием | dictSetGetSliceRef, dictSetGetSliceRefEmpty | развёртка | предел глубины рекурсии simp |
| `DICTIDELGET` | лемма с условием | dictSetGetInt, dictSetGetIntEmpty | развёртка | предел глубины рекурсии simp |
| `DICTIDELGETREF` | лемма с условием | dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | предел глубины рекурсии simp |
| `DICTUDELGET` | лемма с условием | dictSetGetInt, dictSetGetIntEmpty | развёртка | предел глубины рекурсии simp |
| `DICTUDELGETREF` | лемма с условием | dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | предел глубины рекурсии simp |
| `DICTMIN` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTMINREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTIMIN` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTIMINREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTUMIN` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTUMINREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTMAX` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTMAXREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTIMAX` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTIMAXREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTUMAX` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTUMAXREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTREMMIN` | не исполняется | — | развёртка | предел heartbeats |
| `DICTREMMINREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTIREMMIN` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTIREMMINREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTUREMMIN` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTUREMMINREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTREMMAX` | не исполняется | — | развёртка | предел heartbeats |
| `DICTREMMAXREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTIREMMAX` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTIREMMAXREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTUREMMAX` | не исполняется | — | развёртка | предел heartbeats |
| `DICTUREMMAXREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTSETB` | лемма с условием | dictSetSliceBEmpty_flag, dictSetSliceBEmpty_set, dictSetSliceB_flag, dictSetSliceB_set | развёртка | предел heartbeats |
| `DICTISETB` | лемма с условием | dictSetIntBEmpty_flag, dictSetIntBEmpty_set, dictSetIntB_flag, dictSetIntB_set | развёртка | предел heartbeats |
| `DICTUSETB` | лемма с условием | dictSetIntBEmpty_flag, dictSetIntBEmpty_set, dictSetIntB_flag, dictSetIntB_set | развёртка | предел heartbeats |
| `DICTSETGETB` | лемма с условием | dictSetGetSliceB, dictSetGetSliceBEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTISETGETB` | лемма с условием | dictSetGetIntB, dictSetGetIntBEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUSETGETB` | лемма с условием | dictSetGetIntB, dictSetGetIntBEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTREPLACEB` | не исполняется | — | развёртка | предел heartbeats |
| `DICTIREPLACEB` | не исполняется | — | развёртка | предел heartbeats |
| `DICTUREPLACEB` | не исполняется | — | развёртка | предел heartbeats |
| `DICTREPLACEGETB` | лемма с условием | dictSetGetSliceB, dictSetGetSliceBEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTIREPLACEGETB` | лемма с условием | dictSetGetIntB, dictSetGetIntBEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUREPLACEGETB` | лемма с условием | dictSetGetIntB, dictSetGetIntBEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTADDB` | лемма с условием | dictSetSliceBEmpty_flag, dictSetSliceB_flag | развёртка | предел heartbeats |
| `DICTIADDB` | лемма с условием | dictSetIntBEmpty_flag, dictSetIntB_flag | развёртка | предел heartbeats |
| `DICTUADDB` | лемма с условием | dictSetIntBEmpty_flag, dictSetIntB_flag | развёртка | предел heartbeats |
| `DICTADDGETB` | лемма с условием | dictSetGetSliceB, dictSetGetSliceBEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTIADDGETB` | лемма с условием | dictSetGetIntB, dictSetGetIntBEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUADDGETB` | лемма с условием | dictSetGetIntB, dictSetGetIntBEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTDEL` | лемма с условием | dictDelSlice, dictDelSliceEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTIDEL` | лемма с условием | dictDelInt, dictDelIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUDEL` | лемма с условием | dictDelInt, dictDelIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTGETOPTREF` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTIGETOPTREF` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETOPTREF` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTSETGETOPTREF` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTISETGETOPTREF` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUSETGETOPTREF` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SUBDICTGET` | не исполняется | — | развёртка | предел heartbeats |
| `SUBDICTIGET` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SUBDICTUGET` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SUBDICTRPGET` | не исполняется | — | развёртка | предел heartbeats |
| `SUBDICTIRPGET` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SUBDICTURPGET` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTGETNEXT` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTGETNEXTEQ` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTGETPREV` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTGETPREVEQ` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTIGETNEXT` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTIGETNEXTEQ` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTIGETPREV` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTIGETPREVEQ` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETNEXT` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETNEXTEQ` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETPREV` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETPREVEQ` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTPUSHCONST` | лемма | dictPushConst | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PFXDICTSWITCH` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |

### tuple

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `PUSHNULL` | лемма | pushNull | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `ISNULL` | лемма | isNull | развёртка | лемма срабатывает; посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `TUPLEVAR` | лемма | mktupleVar | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; стоит на ForIn.forIn |
| `INDEXVAR` | лемма | indexVar | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 19 |
| `UNTUPLEVAR` | лемма | untupleVar | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; стоит на ForIn.forIn |
| `UNPACKFIRSTVAR` | лемма | unpackFirstVar | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; стоит на ForIn.forIn |
| `EXPLODEVAR` | лемма | explodeVar | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; стоит на ForIn.forIn |
| `SETINDEXVAR` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 19 |
| `INDEXVARQ` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 19 |
| `SETINDEXVARQ` | лемма | setIndexVarQ, setIndexVarQ_null | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; предел heartbeats |
| `TLEN` | лемма | tlen | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 6 |
| `QTLEN` | лемма | qtlen, qtlen_other | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 6 |
| `ISTUPLE` | лемма | isTuple | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 0 |
| `LAST` | лемма | last | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 6 |
| `TPUSH` | лемма | tpush | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 6 |
| `TPOP` | лемма | tpop | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 6 |
| `NULLSWAPIF` | лемма | nullSwapIf | развёртка | лемма срабатывает; стоит на ForIn.forIn |
| `NULLSWAPIFNOT` | лемма | nullSwapIfNot | развёртка | лемма срабатывает; стоит на ForIn.forIn |
| `NULLROTRIF` | лемма | nullRotrIf | развёртка | лемма срабатывает; стоит на ForIn.forIn |
| `NULLROTRIFNOT` | лемма | nullRotrIfNot | развёртка | лемма срабатывает; стоит на ForIn.forIn |
| `NULLSWAPIF2` | лемма | nullSwapIf2 | развёртка | лемма срабатывает; стоит на ForIn.forIn |
| `NULLSWAPIFNOT2` | лемма | nullSwapIfNot2 | развёртка | лемма срабатывает; стоит на ForIn.forIn |
| `NULLROTRIF2` | лемма | nullRotrIf2 | развёртка | лемма срабатывает; стоит на ForIn.forIn |
| `NULLROTRIFNOT2` | лемма | nullRotrIfNot2 | развёртка | лемма срабатывает; стоит на ForIn.forIn |
| `TUPLE` | лемма | mktuple | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; стоит на ForIn.forIn |
| `INDEX` | лемма | index | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 6 |
| `UNTUPLE` | лемма | untuple | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; стоит на ForIn.forIn |
| `UNPACKFIRST` | лемма | unpackFirst | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; стоит на ForIn.forIn |
| `EXPLODE` | лемма | explode | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; стоит на ForIn.forIn |
| `SETINDEX` | лемма | setIndex | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 10 |
| `INDEXQ` | лемма | indexQ, indexQ_null | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; посчитан, ветвлений 10 |
| `SETINDEXQ` | лемма | setIndexQ, setIndexQ_null | блок: ForIn.forIn (вне модели, нет леммы vm_run) | лемма срабатывает; предел heartbeats |
| `INDEX2` | лемма с условием | index2 | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `INDEX3` | лемма с условием | index3 | блок: ForIn.forIn (вне модели, нет леммы vm_run) | предел heartbeats |

### msg/actions

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `PARSEMSGADDR` | лемма с условием | parseMsgAddr, parseMsgAddr_error | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `PARSEMSGADDRQ` | лемма с условием | parseMsgAddr, parseMsgAddr_error | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `REWRITESTDADDR` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `REWRITESTDADDRQ` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `REWRITEVARADDR` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `REWRITEVARADDRQ` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SENDRAWMSG` | лемма | sendRawMsg | развёртка | лемма срабатывает; посчитан, ветвлений 14 |
| `RAWRESERVE` | лемма с условием | rawReserve, rawReserve_le15 | развёртка | посчитан, ветвлений 32 |
| `RAWRESERVEX` | не исполняется | — | развёртка | предел heartbeats |
| `SETCODE` | лемма | setCode | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `SETLIBCODE` | развёртка обработчика | — | развёртка | посчитан, ветвлений 28 |
| `CHANGELIB` | развёртка обработчика | — | развёртка | посчитан, ветвлений 32 |
| `SENDMSG` v4 | не исполняется | — | развёртка | предел heartbeats |

### tonenv/c7

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `ACCEPT` | лемма | accept | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `SETGASLIMIT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 15 |
| `GASCONSUMED` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `COMMIT` | лемма | commit | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `NOW` | лемма с условием | now, now' | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `BLOCKLT` | лемма с условием | blockLt | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `LTIME` | лемма с условием | lTime | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `RANDSEED` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `BALANCE` | лемма с условием | balance | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `MYADDR` | лемма с условием | myAddr | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `CONFIGROOT` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `MYCODE` | лемма с условием | myCode | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `INCOMINGVALUE` | лемма с условием | incomingValue | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `STORAGEFEES` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `PREVBLOCKSINFOTUPLE` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `UNPACKEDCONFIGTUPLE` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DUEPAYMENT` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `CONFIGDICT` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `CONFIGPARAM` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `CONFIGOPTPARAM` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `PREVMCBLOCKS` v4 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `PREVKEYBLOCK` v4 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `PREVMCBLOCKS_100` v9 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `GLOBALID` v4 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `GETGASFEE` v6 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `GETSTORAGEFEE` v6 | не исполняется | — | развёртка | предел heartbeats |
| `GETFORWARDFEE` v6 | не исполняется | — | развёртка | предел heartbeats |
| `GETPRECOMPILEDGAS` v6 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `GETORIGINALFWDFEE` v6 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `GETGASFEESIMPLE` v6 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `GETFORWARDFEESIMPLE` v6 | не исполняется | — | развёртка | предел heartbeats |
| `GETGLOBVAR` | развёртка обработчика | — | развёртка | посчитан, ветвлений 20 |
| `SETGLOBVAR` | развёртка обработчика | — | развёртка | посчитан, ветвлений 15 |
| `RANDU256` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `RAND` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SETRAND` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `ADDRAND` | не исполняется | — | развёртка | предел heartbeats |
| `GETGLOB` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `SETGLOB` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `GETPARAM` | лемма с условием | getParam | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `GETPARAMLONG` v11 | лемма с условием | getParam | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `INMSGPARAMS` v11 | лемма с условием | getParam | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `GETPARAMLONG2` v11 | лемма с условием | getParam | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `INMSG_BOUNCE` v11 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `INMSG_BOUNCED` v11 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `INMSG_SRC` v11 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `INMSG_FWDFEE` v11 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `INMSG_LT` v11 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `INMSG_UTIME` v11 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `INMSG_ORIGVALUE` v11 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `INMSG_VALUE` v11 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `INMSG_VALUEEXTRA` v11 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `INMSG_STATEINIT` v11 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `INMSGPARAM` v11 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `GETEXTRABALANCE` v10 | не исполняется | — | развёртка | предел heartbeats |

### crypto

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `HASHCU` | лемма | hashCU | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `HASHSU` | лемма | hashSU | развёртка | лемма срабатывает; посчитан, ветвлений 10 |
| `SHA256U` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `CHKSIGNU` | лемма | chkSignU | развёртка | лемма срабатывает; посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `CHKSIGNS` | не исполняется | — | развёртка | предел heartbeats |
| `ECRECOVER` v4 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SECP256K1_XONLY_PUBKEY_TWEAK_ADD` v9 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `P256_CHKSIGNU` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `P256_CHKSIGNS` v4 | не исполняется | — | развёртка | предел heartbeats |
| `RIST255_FROMHASH` v4 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `RIST255_VALIDATE` v4 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `RIST255_ADD` v4 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `RIST255_SUB` v4 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `RIST255_MUL` v4 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `RIST255_MULBASE` v4 | не исполняется | — | развёртка | предел heartbeats |
| `RIST255_PUSHL` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `RIST255_QVALIDATE` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 16 |
| `RIST255_QADD` v4 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `RIST255_QSUB` v4 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `RIST255_QMUL` v4 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `RIST255_QMULBASE` v4 | не исполняется | — | развёртка | предел heartbeats |
| `BLS_VERIFY` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 33 |
| `BLS_AGGREGATE` v4 | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `BLS_FASTAGGREGATEVERIFY` v4 | не исполняется | — | развёртка | стоит на ForIn.forIn |
| `BLS_AGGREGATEVERIFY` v4 | не исполняется | — | развёртка | стоит на ForIn.forIn |
| `BLS_G1_ADD` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 29 |
| `BLS_G1_SUB` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 29 |
| `BLS_G1_NEG` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 27 |
| `BLS_G1_MUL` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 32 |
| `BLS_G1_MULTIEXP` v4 | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `BLS_G1_ZERO` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `BLS_MAP_TO_G1` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 22 |
| `BLS_G1_INGROUP` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 27 |
| `BLS_G1_ISZERO` v4 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `BLS_G2_ADD` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 29 |
| `BLS_G2_SUB` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 29 |
| `BLS_G2_NEG` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 27 |
| `BLS_G2_MUL` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 32 |
| `BLS_G2_MULTIEXP` v4 | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `BLS_G2_ZERO` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `BLS_MAP_TO_G2` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 22 |
| `BLS_G2_INGROUP` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 27 |
| `BLS_G2_ISZERO` v4 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `BLS_PAIRING` v4 | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `BLS_PUSHR` v4 | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `HASHEXT` v4 | не исполняется | — | развёртка | предел heartbeats |
| `HASHEXTR` v4 | не исполняется | — | развёртка | предел heartbeats |
| `HASHEXTA` v4 | не исполняется | — | развёртка | предел heartbeats |
| `HASHEXTAR` v4 | не исполняется | — | развёртка | предел heartbeats |
| `HASHBU` v12 | развёртка обработчика | — | развёртка | посчитан, ветвлений 10 |

### debug

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `DEBUGSTR` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `DUMPSTK` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `DEBUG` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `STRDUMP` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `DEBUG_1` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `DUMP` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `DEBUG_2` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |

### misc

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `CDATASIZEQ` | лемма | cdataSize, cdataSize_null | развёртка | лемма срабатывает; стоит на VM.visitDataSizeCell._unary; остаются термами: VM.visitDataSizeCell._unary |
| `CDATASIZE` | лемма | cdataSize, cdataSize_null | развёртка | лемма срабатывает; стоит на VM.visitDataSizeCell._unary; остаются термами: VM.visitDataSizeCell._unary |
| `SDATASIZEQ` | лемма | sdataSize | развёртка | лемма срабатывает; стоит на ForIn.forIn |
| `SDATASIZE` | лемма | sdataSize | развёртка | лемма срабатывает; стоит на ForIn.forIn |

