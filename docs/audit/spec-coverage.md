# Покрытие инструкций символьным исполнением

Сгенерировано `tools/spec-coverage/spec_coverage.py` на коммите `165811a`; руками не править. Пересоздать (на сервере сборки: нужна собранная библиотека доказательств, Fift эталона — только для `--regen`):

```sh
python3 tools/spec-coverage/spec_coverage.py patterns --jobs 5 --save            # шаблоны: пробы (--regen: probes.txt из probes.fif)
python3 tools/spec-coverage/spec_coverage.py inventory --deep --jobs 12 --save --raw inv.tsv
python3 tools/spec-coverage/spec_coverage.py precheck --save                    # контракты contracts.txt
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
| stack | 50 | 22 | 1 | 25 (22) | 1 | 1 | 23 / 23 / 4 |
| arith | 246 | 13 | 1 | 123 (83) | 10 | 99 | 14 / 93 / 139 |
| cell | 199 | 23 | 2 | 59 (44) | 93 | 22 | 25 / 137 / 37 |
| cont/flow | 85 | 13 | 3 | 1 (0) | 47 | 21 | 16 / 47 / 22 |
| loops | 16 | 7 | 0 | 0 (0) | 8 | 1 | 7 / 8 / 1 |
| exceptions | 17 | 7 | 0 | 0 (0) | 10 | 0 | 7 / 10 / 0 |
| dict | 143 | 1 | 13 | 61 (21) | 38 | 30 | 14 / 59 / 70 |
| tuple | 34 | 0 | 0 | 29 (13) | 2 | 3 | 0 / 15 / 19 |
| msg/actions | 13 | 2 | 1 | 2 (2) | 6 | 2 | 3 / 8 / 2 |
| tonenv/c7 | 55 | 2 | 11 | 0 (0) | 39 | 3 | 13 / 39 / 3 |
| crypto | 50 | 3 | 0 | 0 (0) | 33 | 14 | 3 / 33 / 14 |
| debug | 7 | 0 | 0 | 0 (0) | 7 | 0 | 0 / 7 / 0 |
| misc | 4 | 0 | 0 | 0 (0) | 0 | 4 | 0 / 0 / 4 |
| **всего** | **919** | **93** | **32** | **300** **(185)** | **294** | **200** | **125 / 479 / 315** |

Лемм `vm_spec`: 333, из них в импортах contract-check 106; вне их: `TvmLean.Proofs.Exec.Closure` (1), `TvmLean.Proofs.Exec.Spec.ArithExt` (79), `TvmLean.Proofs.Exec.Spec.CellExt` (36), `TvmLean.Proofs.Exec.Spec.DictDel` (6), `TvmLean.Proofs.Exec.Spec.DictSet` (24), `TvmLean.Proofs.Exec.Spec.DictSetGet` (12), `TvmLean.Proofs.Exec.Spec.MsgAddr` (1), `TvmLean.Proofs.Exec.Spec.MsgExt` (1), `TvmLean.Proofs.Exec.Spec.StackExt` (35), `TvmLean.Proofs.Exec.Spec.Tuple` (32).

## Шаблоны управления

Каждый шаблон проверяется пробами (`tools/spec-coverage/probes.fif`): маленький код запускается `ran_case` от начала внешнего сообщения (глобальная версия от 4) с инвариантом `True`; шаблон **исполняется**, если все пути прогона доходят до конца. Результаты — `tools/spec-coverage/probe-results.json`.

| Шаблон | Статус | Чем | Пробы | Где остановились пробы, которые не прошли | Чего не хватает |
|---|---|---|---|---|---|
| переход/вызов обычного продолжения без замыкания (`EXECUTE`/`CALLX`, `JMPX`, `IF`, `IFNOT`, `IFJMP`, `IFNOTJMP`, `IFELSE`, `RET`, `IFRET`) | частично | `Spec.execute`, `Spec.jmpx`, `Spec.if_`, `Spec.ifnot`, `Spec.ifjmp`, `Spec.ifnotjmp`, `Spec.ifelse`, `Spec.ret`, `Spec.ifret` (`Exec/Spec/Flow.lean`); `VM.run_jump_ordinary`, `VM.run_call_plain` | `callx`, `jmpx`, `ifelse-unknown` | ifelse-unknown: failed at cell code, bit 72: IFELSE | `IFELSE` (и вызов `DICT*GETEXEC`) оставляет `VmState.callTo` ветви, его не разворачивает ни одна лемма `vm_run`: следующий шаг не видит продолжения |
| переход/вызов продолжения с замыканием или `nargs` (`SETCONTARGS`, `BLESSARGS`, затем `EXECUTE`/`JMPX`) | нет | `Spec.setContArgs_ord`, `VM.run_jump_ordinary_cdata`, `VM.run_call_ordinary_cdata` (`Exec/Closure.lean`, contract-check его не импортирует) | `closure-call`, `closure-jump` | closure-call: failed (the run stops); closure-jump: failed (the run stops) | `SETCONTARGS` и переходы в продолжения с замыканием: `Spec.setContArgs_ord` и `VM.run_*_cdata` — в `Exec/Closure.lean`, его contract-check не импортирует; обработчик делит путь по `forceCdata` и останавливается |
| `CALLXARGS` / `JMPXARGS` / `RETARGS` (число аргументов и результатов) | нет | обработчик; `VM.call`/`VM.jump` с `passArgs` | `callxargs`, `jmpxargs`, `retargs` | callxargs: failed at cell code, bit 32: CALLXARGS 2,1; jmpxargs: failed at cell code, bit 40: JMPXARGS 2; retargs: failed at cell code, bit 40: CALLXARGS 0,1 | у `VM.call`/`VM.jump` с числом аргументов или результатов (`passArgs`, `retArgs`) нет леммы `vm_run` |
| `CALLCC` и варианты (текущее продолжение как значение) | исполняется | обработчик (`VM.extractCc`) | `callcc`, `callccargs` | — | — |
| `RETALT` / `c1` (альтернативный возврат) | нет | обработчик | `retalt` | retalt: failed (the run stops) | после `RETALT` (переход в `c1`) следующий шаг остаётся `VmState.stepFinish` состояния |
| `REPEAT` / `UNTIL` с известным числом итераций | исполняется | `Spec.repeat_`, `Spec.until_` (`Exec/Spec/Loop.lean`); правило цикла (`vm_loop_c5`) | `repeat-const`, `until-const` | — | — |
| `REPEAT` / `UNTIL` / `WHILE` с неизвестным числом итераций, значение на стеке | частично | правило цикла `VmState.runWith_inv` в голове цикла (`vm_loop_c5`, `Contracts/Wallet3Run/Tactic.lean`): полезная нагрузка вершины стека обобщена, `c5` — `SafeActs` | `repeat-unknown`, `repeat-data`, `until-data`, `while-data` | repeat-unknown: timeout; repeat-data: timeout | `REPEAT` с неизвестным числом итераций: правило цикла обобщает значения на стеке, но не счётчик в продолжении цикла (`repeatBody … n`), и цикл разворачивается до предела шагов (тайм-аут); `UNTIL`/`WHILE` со значением на стеке исполняются |
| `REPEATEND` / `UNTILEND` / `WHILEEND` / `AGAINEND` (тело — остаток кода) | частично | `Spec.untilEnd`, `Spec.whileEnd`, `Spec.againEnd`; `REPEATEND` — обработчиком | `repeatend`, `untilend`, `whileend`, `againend` | repeatend: timeout | у `REPEATEND` тот же счётчик, что у `REPEAT` (тайм-аут); `UNTILEND`, `WHILEEND`, `AGAINEND` исполняются |
| циклы `BRK` (`c1` — выход; `RETALT` выходит из цикла) | частично | обработчики | `againbrk`, `repeatbrk`, `untilbrk`, `whilebrk` | repeatbrk: failed at cell code, bit 128: REPEATBRK; untilbrk: failed at cell code, bit 96: UNTILBRK; whilebrk: failed at cell code, bit 104: WHILEBRK | `REPEATBRK`, `UNTILBRK`, `WHILEBRK` останавливаются на инструкции (леммы нет, прогон обработчика не считается); `AGAINBRK` исполняется |
| `AGAIN` без выхода (кончается нехваткой газа) | исполняется | `Spec.again` и правило цикла | `again` | — | — |
| цикл в цикле | нет | вложенные правила цикла (`check_loop_close` берёт последний `ih`) | `loop-in-loop` | loop-in-loop: timeout | `REPEAT` в `REPEAT`: внутренний счётчик, как выше (тайм-аут) |
| `TRY` / `TRYARGS`: исключение ловит обработчик (`c2`) | частично | обработчик; `VM.run_throwToHandler` | `try-throw`, `try-nothrow`, `tryargs` | try-throw: timeout; tryargs: failed at cell code, bit 64: TRYARGS 1,0 | `TRY` без исключения исполняется; исключение, пойманное обработчиком, не доходит до конца (тайм-аут); `TRYARGS` останавливается на инструкции |
| `THROW*` в обработчик по умолчанию (прогон останавливается с кодом выхода) | исполняется | `Spec.throw`, `Spec.throwIf`, `Spec.throwIfNot`, `Spec.throwArg`, `Spec.throwAny`; `VM.run_throwToHandler`, продолжение `excQuit` разворачивается | `throw`, `throwarg`, `throwif-unknown`, `throwifnot-unknown` | — | — |
| неявный `RET` в конце ячейки, неявный `JMPREF` на следующую ссылку | исполняется | `stepCode`: `VmState.stepOnceWith_implicitRet'`, `VmState.stepOnceWith_implicitJmpRef'` | `implicit-jmpref`, `nop` | — | — |
| `CALLREF` / `JMPREF` / `IF*REF` (продолжения в ссылках) | исполняется | обработчики (ссылка загружается как ячейка) | `callref`, `jmpref`, `ifjmpref` | — | — |
| диспетчер методов: `SETCP0`, `DICTPUSHCONST`, `DICTIGETJMPZ` по словарю кода | исполняется | `Spec.setcp0`, `Spec.dictPushConst`, `Spec.dictGetExec_*` (`Exec/Spec/Dispatch.lean`): поиск — замкнутый факт кода (`dictLookupLoads`, решает ядро) | `calldict` | — | — |
| `CALLDICT` / `JMPDICT` / `PREPAREDICT` (процедуры через `c3`) | исполняется | `Spec.callDict`, `Spec.jmpDict`, `Spec.prepareDict` | `calldict`, `jmpdict`, `preparedict` | — | — |
| `RUNVM` / `RUNVMX` (дочерняя VM) | нет | обработчик; прогон дочерней VM (`VmState.runWith`) рекурсивен | `runvm` | runvm: failed at cell code, bit 32: RUNVM 0 (the run is there) | опкод версии 4: `vm_step` декодирует его только при известной глобальной версии (см. ниже); прогон дочерней VM — рекурсивная функция |
| `SETCP` с кодовой страницей не 0, `SETCPX` | исполняется | обработчик; `stepCode` требует `cp = 0` | `setcp1`, `setcpx` | — | — |
| действия `SENDRAWMSG` / `RAWRESERVE` (`c5`) | частично | `Spec.sendRawMsg`, `Spec.rawReserve`; `SafeActs` закрывает `c5` (`Check/Tactic.lean`) | `sendrawmsg`, `rawreserve` | rawreserve: failed at cell code, bit 32: the implicit RET at the end of the cell | `SENDRAWMSG` исполняется; действие `RAWRESERVE 0 0` не закрывает `safe_acts_close` |
| действия `SETCODE` / `SETLIBCODE` / `CHANGELIB` / `SENDMSG` / `RAWRESERVEX` | нет | `Spec.setCode` исполняется; `ran_case` доказывает только инварианты неизменного кода, `SafeActs` допускает лишь `SENDRAWMSG` и `RAWRESERVE` | `setcode`, `setlibcode`, `changelib`, `sendmsg` | setcode: failed at cell code, bit 24: the implicit RET at the end of the cell; setlibcode: failed at cell code, bit 32: the implicit RET at the end of the cell; changelib: failed at cell code, bit 32: the implicit RET at the end of the cell; sendmsg: failed at cell code, bit 16: SENDMSG (the run is there) | по замыслу: `ran_case` доказывает инварианты неизменного кода, `SafeActs` допускает лишь `SENDRAWMSG` и `RAWRESERVE`; `SENDMSG` к тому же версии 4 |
| изменение `c4` / `c5` / `c7` (`POP c4`, `POP c5`, `POP c7`, `SETGLOB`) | частично | `Spec.popRoot` (`c4`); остальное — обработчиком | `c4-update`, `c5-update`, `c7-update`, `setglob` | c5-update: failed (the run stops); c7-update: failed (the run stops); setglob: failed at cell code, bit 8: SETGLOB 1 | `POP c4` исполняется; после `POP c5` и `POP c7` следующий шаг остаётся `VmState.stepFinish` состояния; `SETGLOB` останавливается на инструкции |
| `COMMIT` | нет | `Spec.commit`; `keeps_haltResult` проверяет зафиксированное состояние | `commit` | commit: failed (the run stops) | после `COMMIT` (`Spec.commit`: проверки `tryCommit` над `c4` и `c5`) следующий шаг остаётся `VmState.stepFinish` состояния |
| `ACCEPT` / `SETGASLIMIT` | исполняется | `Spec.accept`, `GasLimits.changeLimit_infty_min`; `SETGASLIMIT` — обработчиком | `accept`, `setgaslimit` | — | — |
| `DICTGET` / `DICTSET` по словарю, которого прогон не знает | нет | `Spec.dictGetInt_*` требуют фактов `dictLookupLoads`: замкнутых или гипотезы; `Exec/FramedDict.lean` — для обрамлённых ячеек | `dictget-unknown`, `dictset-unknown` | dictget-unknown: failed at cell code, bit 64: DICTUGET; dictset-unknown: failed at cell code, bit 80: DICTUSET | `DICTUGET`/`DICTUSET` по словарю из сообщения: леммам нужны факты `dictLookupLoads`, обработчик останавливается на загрузках ячеек поиска (`registerCellLoad` неизвестных ячеек) |
| перебор неизвестного словаря (`GETNEXT`/`PREV`/`MIN`/`MAX`) | нет | обработчик | `dictgetnext-unknown`, `dictmin-unknown` | dictgetnext-unknown: failed at cell code, bit 64: DICTUGETNEXT; dictmin-unknown: failed at cell code, bit 48: DICTUMIN | `GETNEXT`/`MIN` по неизвестному словарю: леммы нет, обработчик останавливается на инструкции |
| чтение конфигурации (`CONFIGPARAM`, `CONFIGOPTPARAM`) | нет | обработчик | `configparam`, `configoptparam` | configparam: failed (the run stops); configoptparam: failed (the run stops) | поиск в словаре конфигурации (`dictLookupWithCells` по неизвестному корню из `c7`) остаётся термом, и прогон останавливается на форме значения |
| параметры `c7` (`NOW`, `BALANCE`, `MYADDR`, `GETPARAM`) при неизвестном `c7` | исполняется | `Spec.getParam` и синонимы требуют гипотезы `c7[0]! = .tuple params`; иначе обработчик | `now` | — | — |
| опкод глобальной версии > 0 (например `GASCONSUMED`, v4) при символьной версии | нет | `stepCode` решает `k ≤ globalVersion` через `decide` по версии состояния | `gasconsumed-v4` | gasconsumed-v4: failed at cell code, bit 0: GASCONSUMED (the run is there) | `stepCode` доказывает `k ≤ globalVersion` через `decide`, а у contract-check версия символьная (`hgv : 4 ≤ gv` не используется): любой опкод версии > 0 останавливает прогон |

## Предпроверка контрактов

`contract-check <код> --precheck` (`spec_coverage.py precheck ... --save`): весь код, достижимый из корня (неявные `JMPREF`, `PUSHCONT`, `CALLREF`, `IF*REF`, процедуры `DICTPUSHCONST`), дизассемблирован декодером модели; каждая инструкция — по её точным аргументам (лемма), иначе по результату формы выше. Вхождения инструкций:

| Код | Инструкций | Форм | Лемма | Лемма для словаря-константы | Лемма вне contract-check | Развёртка обработчика | Не исполняется | Формы без леммы contract-check |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `wallet3` | 59 | 36 | 59 | 0 | 0 | 0 | 0 | — |
| `highload2` | 125 | 61 | 107 | 0 | 11 | 6 | 1 | `LDDICT`, `BLKDROP2`, `NULLSWAPIFNOT`, `NULLSWAPIFNOT2`, `DICTIGETNEXT`, `DICTUREMMIN` (нет), `DICTUSETB`, `LSHIFT`, `NEGATE`, `PUSHREFCONT`, `PUXC`, `STDICT` и ещё 1 |
| `elector` | 2158 | 138 | 1564 | 0 | 401 | 188 | 5 | `CALLREF`, `XCHG_1I`, `LDGRAMS`, `PUXC`, `PUSHNULL`, `STDICT`, `LDDICT`, `NULLSWAPIFNOT`, `CONFIGOPTPARAM`, `ISNULL`, `STGRAMS`, `TUPLE` и ещё 55 |
| `config` | 1294 | 130 | 984 | 0 | 218 | 87 | 5 | `XCHG_1I`, `CALLREF`, `PUSHNULL`, `STI`, `STDICT`, `PUXC`, `POPCTR`, `ISNULL`, `PUSHCTR`, `BLKDROP2`, `CONFIGOPTPARAM`, `EQINT` и ещё 44 |
| `dns` | 436 | 100 | 339 | 0 | 68 | 24 | 5 | `EQINT`, `PUSHNULL`, `XCHG_1I`, `CALLREF`, `LDDICT`, `PUSHPOW2DEC`, `LESSINT`, `BLKDROP2`, `PUSHCTR`, `ADDINT`, `STDICT`, `STSLICER` и ещё 26 |
| `simple-wallet` | 38 | 30 | 38 | 0 | 0 | 0 | 0 | — |
| `wallet2` | 53 | 36 | 53 | 0 | 0 | 0 | 0 | — |
| `pow` | 311 | 85 | 246 | 0 | 51 | 8 | 6 | `XCHG_1I`, `LSHIFT`, `POW2`, `ADDRAND` (нет), `CALLREF`, `LDGRAMS`, `PUXC`, `RSHIFT`, `STSLICER`, `AND`, `LSHIFT#DIVR` (нет), `MAX` и ещё 14 |
| `multisig` | 538 | 108 | 412 | 0 | 86 | 38 | 2 | `CALLREF`, `XCHG_1I`, `BLKDROP2`, `LDDICT`, `NULLSWAPIFNOT`, `DICTUSETB`, `ISNULL`, `PUSHCTR`, `STSLICER`, `AND`, `OR`, `POW2` и ещё 25 |
| `restricted3` | 163 | 63 | 139 | 0 | 11 | 13 | 0 | `CALLREF`, `XCHG_1I`, `LDDICT`, `DICTIGETPREVEQ`, `LDGRAMS`, `NULLSWAPIFNOT2`, `STDICT`, `CONFIGOPTPARAM`, `INDEX`, `ISNULL`, `MAX`, `PUSHREFCONT` |
| `pchan` | 572 | 85 | 444 | 0 | 107 | 21 | 0 | `XCHG_1I`, `THROWANYIFNOT`, `LDGRAMS`, `STGRAMS`, `PUXC`, `OR`, `STI`, `AND`, `BLKDROP2`, `PUXC2`, `CALLREF`, `EQINT` и ещё 16 |
| `highload1` | 72 | 46 | 69 | 0 | 1 | 2 | 0 | `DICTIGETNEXT`, `LDDICT`, `NULLSWAPIFNOT2` |
| `simple-wallet-ext` | 67 | 39 | 63 | 0 | 2 | 2 | 0 | `PUSHCTR`, `XCHG_1I`, `XCPU2` |
| `restricted1` | 129 | 57 | 114 | 0 | 10 | 5 | 0 | `CONFIGOPTPARAM`, `AND`, `BLKDROP2`, `ISNULL`, `LDMSGADDR`, `CALLREF`, `EQINT`, `INDEX`, `REWRITESTDADDR` |
| `restricted2` | 143 | 62 | 122 | 0 | 10 | 11 | 0 | `CALLREF`, `XCHG_1I`, `DICTIGETPREVEQ`, `LDDICT`, `LDGRAMS`, `NULLSWAPIFNOT2`, `STDICT`, `CONFIGOPTPARAM`, `INDEX`, `ISNULL`, `MAX` |
| `dnsauto` | 875 | 120 | 656 | 2 | 167 | 47 | 3 | `CALLREF`, `XCHG_1I`, `BLKDROP2`, `EQINT`, `LDGRAMS`, `AND`, `ISNULL`, `LSHIFT`, `PUSHNULL`, `PUXC`, `LDDICT`, `RSHIFT` и ещё 40 |
| `storage` | 388 | 85 | 299 | 0 | 79 | 10 | 0 | `XCHG_1I`, `PUSHCTR`, `STSLICER`, `STGRAMS`, `LDGRAMS`, `LDMSGADDR`, `SDEQ`, `CALLREF`, `PUXC`, `STI`, `BLKDROP2`, `IFREFELSE` и ещё 19 |

## Что не покрыто

**stack** (1): `BLKSWX` (прогон обработчика: предел heartbeats).

**arith** (99): `ADDRSHIFTMOD` (прогон обработчика: предел глубины рекурсии simp); `ADDRSHIFTMODR` (прогон обработчика: предел глубины рекурсии simp); `ADDRSHIFTMODC` (прогон обработчика: предел глубины рекурсии simp); `RSHIFTR` (прогон обработчика: предел глубины рекурсии simp); `RSHIFTC` (прогон обработчика: предел глубины рекурсии simp); `MODPOW2` (прогон обработчика: предел глубины рекурсии simp); `MODPOW2R` (прогон обработчика: предел глубины рекурсии simp); `MODPOW2C` (прогон обработчика: предел глубины рекурсии simp); `RSHIFTMOD` (прогон обработчика: предел глубины рекурсии simp); `RSHIFTMODR` (прогон обработчика: предел глубины рекурсии simp); `RSHIFTMODC` (прогон обработчика: предел глубины рекурсии simp); `QADDRSHIFTMOD` (прогон обработчика: предел глубины рекурсии simp); `QADDRSHIFTMODR` (прогон обработчика: предел глубины рекурсии simp); `QADDRSHIFTMODC` (прогон обработчика: предел глубины рекурсии simp); `QRSHIFTR` (прогон обработчика: предел глубины рекурсии simp); `QRSHIFTC` (прогон обработчика: предел глубины рекурсии simp); `QMODPOW2` (прогон обработчика: предел глубины рекурсии simp); `QMODPOW2R` (прогон обработчика: предел глубины рекурсии simp); `QMODPOW2C` (прогон обработчика: предел глубины рекурсии simp); `QRSHIFTMOD` (прогон обработчика: предел глубины рекурсии simp); `QRSHIFTMODR` (прогон обработчика: предел глубины рекурсии simp); `QRSHIFTMODC` (прогон обработчика: предел глубины рекурсии simp); `MULADDRSHIFTMOD` (прогон обработчика: предел глубины рекурсии simp); `MULADDRSHIFTRMOD` (прогон обработчика: предел глубины рекурсии simp); `MULADDRSHIFTCMOD` (прогон обработчика: предел глубины рекурсии simp); `MULRSHIFT` (прогон обработчика: предел глубины рекурсии simp); `MULRSHIFTR` (прогон обработчика: предел глубины рекурсии simp); `MULRSHIFTC` (прогон обработчика: предел глубины рекурсии simp); `MULMODPOW2` (прогон обработчика: предел глубины рекурсии simp); `MULMODPOW2R` (прогон обработчика: предел глубины рекурсии simp); `MULMODPOW2C` (прогон обработчика: предел глубины рекурсии simp); `MULRSHIFTMOD` (прогон обработчика: предел глубины рекурсии simp); `MULRSHIFTRMOD` (прогон обработчика: предел глубины рекурсии simp); `MULRSHIFTCMOD` (прогон обработчика: предел глубины рекурсии simp); `QMULADDRSHIFTMOD` (прогон обработчика: предел глубины рекурсии simp); `QMULADDRSHIFTRMOD` (прогон обработчика: предел глубины рекурсии simp); `QMULADDRSHIFTCMOD` (прогон обработчика: предел глубины рекурсии simp); `QMULRSHIFT` (прогон обработчика: предел глубины рекурсии simp); `QMULRSHIFTR` (прогон обработчика: предел глубины рекурсии simp); `QMULRSHIFTC` (прогон обработчика: предел глубины рекурсии simp); `QMULMODPOW2` (прогон обработчика: предел глубины рекурсии simp); `QMULMODPOW2R` (прогон обработчика: предел глубины рекурсии simp); `QMULMODPOW2C` (прогон обработчика: предел глубины рекурсии simp); `QMULRSHIFTMOD` (прогон обработчика: предел глубины рекурсии simp); `QMULRSHIFTRMOD` (прогон обработчика: предел глубины рекурсии simp); `QMULRSHIFTCMOD` (прогон обработчика: предел глубины рекурсии simp); `LSHIFTADDDIVMOD` (прогон обработчика: предел глубины рекурсии simp); `LSHIFTADDDIVMODR` (прогон обработчика: предел глубины рекурсии simp); `LSHIFTADDDIVMODC` (прогон обработчика: предел глубины рекурсии simp); `LSHIFTDIV` (прогон обработчика: предел глубины рекурсии simp); `LSHIFTDIVR` (прогон обработчика: предел глубины рекурсии simp); `LSHIFTDIVC` (прогон обработчика: предел глубины рекурсии simp); `LSHIFTMOD` (прогон обработчика: предел глубины рекурсии simp); `LSHIFTMODR` (прогон обработчика: предел глубины рекурсии simp); `LSHIFTMODC` (прогон обработчика: предел глубины рекурсии simp); `LSHIFTDIVMOD` (прогон обработчика: предел глубины рекурсии simp); `LSHIFTDIVMODR` (прогон обработчика: предел глубины рекурсии simp); `LSHIFTDIVMODC` (прогон обработчика: предел глубины рекурсии simp); `QLSHIFTADDDIVMOD` (прогон обработчика: предел глубины рекурсии simp); `QLSHIFTADDDIVMODR` (прогон обработчика: предел глубины рекурсии simp); `QLSHIFTADDDIVMODC` (прогон обработчика: предел глубины рекурсии simp); `QLSHIFTDIV` (прогон обработчика: предел глубины рекурсии simp); `QLSHIFTDIVR` (прогон обработчика: предел глубины рекурсии simp); `QLSHIFTDIVC` (прогон обработчика: предел глубины рекурсии simp); `QLSHIFTMOD` (прогон обработчика: предел глубины рекурсии simp); `QLSHIFTMODR` (прогон обработчика: предел глубины рекурсии simp); `QLSHIFTMODC` (прогон обработчика: предел глубины рекурсии simp); `QLSHIFTDIVMOD` (прогон обработчика: предел глубины рекурсии simp); `QLSHIFTDIVMODR` (прогон обработчика: предел глубины рекурсии simp); `QLSHIFTDIVMODC` (прогон обработчика: предел глубины рекурсии simp); `ADDRSHIFT#MOD` (прогон обработчика: предел глубины рекурсии simp); `ADDRSHIFTR#MOD` (прогон обработчика: предел глубины рекурсии simp); `ADDRSHIFTC#MOD` (прогон обработчика: предел глубины рекурсии simp); `RSHIFT#` (прогон обработчика: предел глубины рекурсии simp); `RSHIFTR#` (прогон обработчика: предел глубины рекурсии simp); `RSHIFTC#` (прогон обработчика: предел глубины рекурсии simp); `MODPOW2#` (прогон обработчика: предел глубины рекурсии simp); `MODPOW2R#` (прогон обработчика: предел глубины рекурсии simp); `MODPOW2C#` (прогон обработчика: предел глубины рекурсии simp); `RSHIFT#MOD` (прогон обработчика: предел глубины рекурсии simp); `RSHIFTR#MOD` (прогон обработчика: предел глубины рекурсии simp); `RSHIFTC#MOD` (прогон обработчика: предел глубины рекурсии simp); `MULADDRSHIFT#MOD` (прогон обработчика: предел глубины рекурсии simp); `MULADDRSHIFTR#MOD` (прогон обработчика: предел глубины рекурсии simp); `MULADDRSHIFTC#MOD` (прогон обработчика: предел глубины рекурсии simp); `LSHIFT#ADDDIVMOD` (прогон обработчика: предел глубины рекурсии simp); `LSHIFT#ADDDIVMODR` (прогон обработчика: предел глубины рекурсии simp); `LSHIFT#ADDDIVMODC` (прогон обработчика: предел глубины рекурсии simp); `LSHIFT#DIV` (прогон обработчика: предел глубины рекурсии simp); `LSHIFT#DIVR` (прогон обработчика: предел глубины рекурсии simp); `LSHIFT#DIVC` (прогон обработчика: предел глубины рекурсии simp); `LSHIFT#MOD` (прогон обработчика: предел глубины рекурсии simp); `LSHIFT#MODR` (прогон обработчика: предел глубины рекурсии simp); `LSHIFT#MODC` (прогон обработчика: предел глубины рекурсии simp); `LSHIFT#DIVMOD` (прогон обработчика: предел глубины рекурсии simp); `LSHIFT#DIVMODR` (прогон обработчика: предел глубины рекурсии simp); `LSHIFT#DIVMODC` (прогон обработчика: предел глубины рекурсии simp); `RSHIFT_ALT` (прогон обработчика: предел глубины рекурсии simp); `QRSHIFT_ALT` (прогон обработчика: предел глубины рекурсии simp).

**cell** (22): `BDEPTH` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика остановился на ForIn.forIn); `BCHKREFS` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика: предел глубины рекурсии simp); `BCHKBITREFS` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика: предел глубины рекурсии simp); `BCHKREFSQ` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика: предел глубины рекурсии simp); `BCHKBITREFSQ` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика: предел глубины рекурсии simp); `SUBSLICE` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика: предел heartbeats); `STVARINT16` (прогон обработчика: предел глубины рекурсии simp); `STVARINT32` (прогон обработчика: предел глубины рекурсии simp); `STIX` (прогон обработчика: предел глубины рекурсии simp); `STUX` (прогон обработчика: предел глубины рекурсии simp); `STIXR` (прогон обработчика: предел глубины рекурсии simp); `STUXR` (прогон обработчика: предел глубины рекурсии simp); `STIXQ` (прогон обработчика: предел глубины рекурсии simp); `STUXQ` (прогон обработчика: предел глубины рекурсии simp); `STIXRQ` (прогон обработчика: предел глубины рекурсии simp); `STUXRQ` (прогон обработчика: предел глубины рекурсии simp); `LDIQ` (прогон обработчика: предел глубины рекурсии simp); `LDUQ` (прогон обработчика: предел глубины рекурсии simp); `PLDIQ` (прогон обработчика: предел глубины рекурсии simp); `PLDUQ` (прогон обработчика: предел глубины рекурсии simp); `BCHKBITS_VAR` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика: предел глубины рекурсии simp); `BCHKBITSQ_VAR` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика: предел глубины рекурсии simp).

**cont/flow** (21): `CALLCC` (прогон обработчика: предел глубины рекурсии simp); `CALLXVARARGS` (обработчик: popCallxVarArgBounded (private-определение: unfoldModelRun его не разворачивает); прогон обработчика остановился на popCallxVarArgBounded); `RETVARARGS` (прогон обработчика остановился на VM.jump); `CALLCCVARARGS` (обработчик: popCallccVarArgBounded (private-определение: unfoldModelRun его не разворачивает); прогон обработчика остановился на popCallccVarArgBounded); `RUNVMX` (прогон обработчика: предел глубины рекурсии simp); `RETURNVARARGS` (прогон обработчика: предел heartbeats); `SETCONTVARARGS` (обработчик: popSetContVarArgBounded (private-определение: unfoldModelRun его не разворачивает); прогон обработчика: предел heartbeats); `BLESSVARARGS` (обработчик: popBlessVarArgMore (private-определение: unfoldModelRun его не разворачивает); прогон обработчика остановился на popBlessVarArgMore); `SETCONTCTRMANYX` (прогон обработчика остановился на ForIn.forIn); `BOOLEVAL` (прогон обработчика: предел глубины рекурсии simp); `SETCONTCTRMANY` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика остановился на ForIn.forIn); `JMPXARGS` (прогон обработчика остановился на VM.jump); `RETARGS` (прогон обработчика остановился на VM.jump); `RETURNARGS` (прогон обработчика: предел heartbeats); `IFBITJMP` (обработчик: popIntFiniteKeepAndBit (private-определение: unfoldModelRun его не разворачивает); прогон обработчика остановился на popIntFiniteKeepAndBit); `IFNBITJMP` (обработчик: popIntFiniteKeepAndBit (private-определение: unfoldModelRun его не разворачивает); прогон обработчика остановился на popIntFiniteKeepAndBit); `IFBITJMPREF` (обработчик: popIntFiniteKeepAndBit (private-определение: unfoldModelRun его не разворачивает); прогон обработчика остановился на popIntFiniteKeepAndBit); `IFNBITJMPREF` (обработчик: popIntFiniteKeepAndBit (private-определение: unfoldModelRun его не разворачивает); прогон обработчика остановился на popIntFiniteKeepAndBit); `RUNVM` (прогон обработчика: предел глубины рекурсии simp); `CALLXARGS` (прогон обработчика остановился на VM.call); `CALLXARGS_1` (прогон обработчика остановился на VM.call).

**loops** (1): `AGAINBRK` (прогон обработчика: предел глубины рекурсии simp).

**dict** (30): `PFXDICTSET` (обработчик: DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.pushDictRoot (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает); прогон обработчика остановился на DictExt.pushDictRoot, DictExt.prechargeRootLoad); `PFXDICTREPLACE` (обработчик: DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.pushDictRoot (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает); прогон обработчика остановился на DictExt.pushDictRoot, DictExt.prechargeRootLoad); `PFXDICTADD` (обработчик: DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.pushDictRoot (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает); прогон обработчика остановился на DictExt.pushDictRoot, DictExt.prechargeRootLoad); `PFXDICTDEL` (обработчик: DictExt.consumeCreatedGas (private-определение: unfoldModelRun его не разворачивает), DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.pushDictRoot (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает); прогон обработчика остановился на DictExt.pushDictRoot, DictExt.prechargeRootLoad); `PFXDICTGETQ` (обработчик: DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает); прогон обработчика остановился на DictExt.prechargeRootLoad); `PFXDICTGET` (обработчик: DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает); прогон обработчика остановился на DictExt.prechargeRootLoad); `PFXDICTGETJMP` (обработчик: DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает); прогон обработчика остановился на DictExt.prechargeRootLoad); `PFXDICTGETEXEC` (обработчик: DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает); прогон обработчика остановился на DictExt.prechargeRootLoad); `DICTMINREF` (прогон обработчика: предел heartbeats); `DICTIMINREF` (прогон обработчика: предел heartbeats); `DICTUMINREF` (прогон обработчика: предел heartbeats); `DICTMAXREF` (прогон обработчика: предел heartbeats); `DICTIMAXREF` (прогон обработчика: предел heartbeats); `DICTUMAXREF` (прогон обработчика: предел heartbeats); `DICTREMMIN` (прогон обработчика: предел heartbeats); `DICTREMMINREF` (прогон обработчика: предел heartbeats); `DICTIREMMINREF` (прогон обработчика: предел heartbeats); `DICTUREMMIN` (прогон обработчика: предел heartbeats); `DICTUREMMINREF` (прогон обработчика: предел heartbeats); `DICTREMMAX` (прогон обработчика: предел heartbeats); `DICTREMMAXREF` (прогон обработчика: предел heartbeats); `DICTIREMMAXREF` (прогон обработчика: предел heartbeats); `DICTUREMMAXREF` (прогон обработчика: предел heartbeats); `DICTREPLACEB` (прогон обработчика: предел heartbeats); `DICTIREPLACEB` (прогон обработчика: предел heartbeats); `DICTUREPLACEB` (прогон обработчика: предел heartbeats); `DICTGETOPTREF` (прогон обработчика остановился на DictExt.prechargeRootLoad); `DICTSETGETOPTREF` (прогон обработчика остановился на DictExt.prechargeRootLoad); `SUBDICTGET` (прогон обработчика: предел heartbeats); `SUBDICTRPGET` (прогон обработчика: предел heartbeats).

**tuple** (3): `UNPACKFIRSTVAR` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика остановился на ForIn.forIn); `EXPLODEVAR` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика остановился на ForIn.forIn); `SETINDEXVARQ` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика: предел heartbeats).

**msg/actions** (2): `RAWRESERVEX` (прогон обработчика: предел heartbeats); `SENDMSG` (прогон обработчика: предел heartbeats).

**tonenv/c7** (3): `GETSTORAGEFEE` (прогон обработчика: предел heartbeats); `ADDRAND` (прогон обработчика: предел heartbeats); `GETEXTRABALANCE` (прогон обработчика: предел heartbeats).

**crypto** (14): `CHKSIGNS` (прогон обработчика: предел heartbeats); `P256_CHKSIGNS` (прогон обработчика: предел heartbeats); `RIST255_MULBASE` (прогон обработчика: предел heartbeats); `RIST255_QMULBASE` (прогон обработчика: предел heartbeats); `BLS_AGGREGATE` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика остановился на ForIn.forIn); `BLS_FASTAGGREGATEVERIFY` (прогон обработчика остановился на ForIn.forIn); `BLS_AGGREGATEVERIFY` (прогон обработчика остановился на ForIn.forIn); `BLS_G1_MULTIEXP` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика остановился на ForIn.forIn); `BLS_G2_MULTIEXP` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика остановился на ForIn.forIn); `BLS_PAIRING` (обработчик: ForIn.forIn (вне модели, нет леммы vm_run); прогон обработчика остановился на ForIn.forIn); `HASHEXT` (прогон обработчика: предел heartbeats); `HASHEXTR` (прогон обработчика: предел heartbeats); `HASHEXTA` (прогон обработчика: предел heartbeats); `HASHEXTAR` (прогон обработчика: предел heartbeats).

**misc** (4): `CDATASIZEQ` (прогон обработчика остановился на MonadExcept.tryCatch); `CDATASIZE` (прогон обработчика остановился на MonadExcept.tryCatch); `SDATASIZEQ` (прогон обработчика остановился на ForIn.forIn); `SDATASIZE` (прогон обработчика остановился на ForIn.forIn).

Кроме того, 115 форм с леммой вне contract-check в нём сейчас не исполняются (обработчик не считается; их покроет подключение модулей с леммами): `STSLICER`, `STSLICERQ`, `ROLL`, `ROLLREV`, `LDGRAMS`, `LDVARINT16`, `LDVARUINT32`, `LDVARINT32`, `STVARUINT32`, `TUPLEVAR`, `UNTUPLEVAR`, `NULLSWAPIF`, `NULLSWAPIFNOT`, `NULLROTRIF`, `NULLROTRIFNOT`, `NULLSWAPIF2`, `NULLSWAPIFNOT2`, `NULLROTRIF2`, `NULLROTRIFNOT2`, `DIV`, `DIVR`, `DIVC`, `MOD`, `MODR`, `MODC`, `DIVMOD`, `DIVMODR`, `DIVMODC`, `QDIV`, `QDIVR`, `QDIVC`, `QMOD`, `QMODR`, `QMODC`, `QDIVMOD`, `QDIVMODR`, `QDIVMODC`, `MULDIV`, `MULDIVR`, `MULDIVC`, `MULMOD`, `MULMODR`, `MULMODC`, `MULDIVMOD`, `MULDIVMODR`, `MULDIVMODC`, `QMULDIV`, `QMULDIVR`, `QMULDIVC`, `QMULMOD`, `QMULMODR`, `QMULMODC`, `QMULDIVMOD`, `QMULDIVMODR`, `QMULDIVMODC`, `DICTSET`, `DICTSETREF`, `DICTISET`, `DICTISETREF`, `DICTUSET`, `DICTUSETREF`, `DICTSETGET`, `DICTSETGETREF`, `DICTREPLACE`, `DICTREPLACEREF`, `DICTIREPLACE`, `DICTIREPLACEREF`, `DICTUREPLACE`, `DICTUREPLACEREF`, `DICTREPLACEGET`, `DICTREPLACEGETREF`, `DICTADD`, `DICTADDREF`, `DICTIADD`, `DICTIADDREF`, `DICTUADD`, `DICTUADDREF`, `DICTADDGET`, `DICTADDGETREF`, `DICTDELGET`, `DICTDELGETREF`, `DICTIDELGET`, `DICTIDELGETREF`, `DICTUDELGET`, `DICTUDELGETREF`, `DICTSETB`, `DICTISETB`, `DICTUSETB`, `DICTSETGETB`, `DICTREPLACEGETB`, `DICTADDB`, `DICTIADDB`, `DICTUADDB`, `DICTADDGETB`, `DICTDEL`, `LESSINT`, `QLESSINT`, `TUPLE`, `UNTUPLE`, `UNPACKFIRST`, `EXPLODE`, `SETINDEXQ`, `SETCONTARGS`, `STIR`, `STUR`, `STIQ`, `STUQ`, `STIRQ`, `STURQ`, `INDEX3`, `BLKPUSH`, `STI_ALT`, `STU_ALT`, `QLSHIFT_VAR`, `QRSHIFT_VAR`.

## Все формы

### stack

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `NOP` | лемма вне contract-check | вне: nop | развёртка | посчитан, ветвлений 0 |
| `SWAP` | лемма | swap, xchg0 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `DUP` | лемма | push | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `OVER` | лемма | push | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `DROP` | лемма | drop, pop | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `NIP` | лемма | nip, pop | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `ROT` | лемма | rot | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `ROTREV` | лемма | rotRev; вне: rotRev_any | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PICK` | лемма вне contract-check | вне: pick | развёртка | посчитан, ветвлений 20 |
| `ROLL` | лемма вне contract-check | вне: roll | развёртка | стоит на ForIn.forIn |
| `ROLLREV` | лемма вне contract-check | вне: rollRev | развёртка | стоит на ForIn.forIn |
| `BLKSWX` | не исполняется | — | развёртка | предел heartbeats |
| `REVX` | развёртка обработчика | — | развёртка | посчитан, ветвлений 35 |
| `DROPX` | лемма вне contract-check | вне: dropX | развёртка | посчитан, ветвлений 20 |
| `TUCK` | лемма | tuck; вне: tuck_any | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCHGX` | лемма вне contract-check | вне: xchgX | развёртка | посчитан, ветвлений 20 |
| `DEPTH` | лемма вне contract-check | вне: depth | развёртка | посчитан, ветвлений 0 |
| `CHKDEPTH` | лемма вне contract-check | вне: chkDepth | развёртка | посчитан, ветвлений 20 |
| `ONLYTOPX` | лемма вне contract-check | вне: onlyTopX | развёртка | посчитан, ветвлений 28 |
| `ONLYX` | лемма вне contract-check | вне: onlyX | развёртка | посчитан, ветвлений 20 |
| `BLKDROP` | лемма | blkdrop | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XC2PU` | лемма | xc2pu | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCPU2` | лемма вне contract-check | вне: xcpu2 | развёртка | посчитан, ветвлений 0 |
| `PUSH3` | лемма вне contract-check | вне: push3 | развёртка | посчитан, ветвлений 0 |
| `XCHG2` | лемма | xchg2 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCPU` | лемма | xcpu | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUSH2` | лемма | push2; вне: push2_shape | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUXC` | лемма вне contract-check | вне: puxc | развёртка | посчитан, ветвлений 0 |
| `XCPUXC` | лемма вне contract-check | вне: xcpuxc | развёртка | посчитан, ветвлений 0 |
| `PUXC2` | лемма вне contract-check | вне: puxc2 | развёртка | посчитан, ветвлений 0 |
| `PUXCPU` | лемма вне contract-check | вне: puxcpu | развёртка | посчитан, ветвлений 0 |
| `PU2XC` | лемма вне contract-check | вне: pu2xc | развёртка | посчитан, ветвлений 0 |
| `BLKSWAP` | лемма вне contract-check | вне: blkSwap | развёртка | посчитан, ветвлений 0 |
| `REVERSE` | лемма вне contract-check | вне: reverse | развёртка | посчитан, ветвлений 0 |
| `BLKPUSH` | лемма вне contract-check | вне: blkPush | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `BLKDROP2` | лемма вне contract-check | вне: blkdrop2 | развёртка | посчитан, ветвлений 0 |
| `2SWAP` | лемма вне contract-check | вне: twoSwap, twoSwap_shape | развёртка | посчитан, ветвлений 0 |
| `2DROP` | лемма | drop2; вне: drop2_any | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `2DUP` | лемма вне contract-check | вне: twoDup, twoDup_shape | развёртка | посчитан, ветвлений 0 |
| `2OVER` | лемма вне contract-check | вне: twoOver, twoOver_shape | развёртка | посчитан, ветвлений 0 |
| `XCHG3` | лемма | xchg3 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCHG3_ALT` | лемма | xchg3 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCHG_0I_LONG` | лемма | swap, xchg0, xchg0_2 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCHG_0I` | лемма | xchg0, xchg0_2 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `XCHG_IJ` | лемма с условием | xchg; вне: xchg_any | развёртка | посчитан, ветвлений 0 |
| `XCHG_1I` | лемма вне contract-check | вне: xchg1 | развёртка | посчитан, ветвлений 0 |
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
| `SUBR` | лемма вне contract-check | вне: subr | развёртка | посчитан, ветвлений 6 |
| `NEGATE` | лемма вне contract-check | вне: negate | развёртка | посчитан, ветвлений 6 |
| `INC` | лемма | inc | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `DEC` | лемма | dec | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `MUL` | лемма вне contract-check | вне: mul | развёртка | посчитан, ветвлений 6 |
| `POW2` | лемма вне contract-check | вне: pow2 | развёртка | посчитан, ветвлений 14 |
| `AND` | лемма вне contract-check | вне: and_ | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `OR` | лемма вне contract-check | вне: or | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `XOR` | лемма вне contract-check | вне: xor | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `NOT` | лемма с условием | not_ | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `FITSX` | лемма вне contract-check | вне: fitsx | развёртка | посчитан, ветвлений 15 |
| `UFITSX` | лемма вне contract-check | вне: ufitsx | развёртка | посчитан, ветвлений 15 |
| `BITSIZE` | лемма вне contract-check | вне: bitsize | развёртка | посчитан, ветвлений 0 |
| `UBITSIZE` | лемма вне contract-check | вне: ubitsize | развёртка | посчитан, ветвлений 6 |
| `MIN` | лемма вне contract-check | вне: min | развёртка | посчитан, ветвлений 6 |
| `MAX` | лемма вне contract-check | вне: max | развёртка | посчитан, ветвлений 11 |
| `MINMAX` | лемма вне contract-check | вне: minmax | развёртка | посчитан, ветвлений 19 |
| `ABS` | лемма вне contract-check | вне: abs | развёртка | посчитан, ветвлений 15 |
| `QADD` | лемма вне contract-check | вне: qadd | развёртка | посчитан, ветвлений 6 |
| `QSUB` | лемма вне contract-check | вне: qsub | развёртка | посчитан, ветвлений 6 |
| `QSUBR` | лемма вне contract-check | вне: qsubr | развёртка | посчитан, ветвлений 6 |
| `QNEGATE` | лемма вне contract-check | вне: qnegate | развёртка | посчитан, ветвлений 6 |
| `QINC` | лемма вне contract-check | вне: qinc | развёртка | посчитан, ветвлений 6 |
| `QDEC` | лемма вне contract-check | вне: qdec | развёртка | посчитан, ветвлений 6 |
| `QMUL` | лемма вне contract-check | вне: qmul | развёртка | посчитан, ветвлений 6 |
| `QPOW2` | лемма вне contract-check | вне: qpow2 | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `QAND` | лемма вне contract-check | вне: qand | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `QOR` | лемма вне contract-check | вне: qor | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `QXOR` | лемма вне contract-check | вне: qxor | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `QNOT` | лемма вне contract-check | вне: qnot | развёртка | посчитан, ветвлений 6 |
| `QFITSX` | лемма вне contract-check | вне: qfitsx | развёртка | посчитан, ветвлений 19 |
| `QUFITSX` | лемма вне contract-check | вне: qufitsx | развёртка | посчитан, ветвлений 19 |
| `QBITSIZE` | лемма вне contract-check | вне: qbitsize | развёртка | посчитан, ветвлений 0 |
| `QUBITSIZE` | лемма вне contract-check | вне: ubitsize | развёртка | посчитан, ветвлений 6 |
| `QMIN` | лемма вне contract-check | вне: qmin | развёртка | посчитан, ветвлений 6 |
| `QMAX` | лемма вне contract-check | вне: qmax | развёртка | посчитан, ветвлений 11 |
| `QMINMAX` | лемма вне contract-check | вне: qminmax | развёртка | посчитан, ветвлений 23 |
| `QABS` | лемма вне contract-check | вне: abs | развёртка | посчитан, ветвлений 15 |
| `SGN` | лемма вне contract-check | вне: sgn | развёртка | посчитан, ветвлений 10 |
| `LESS` | лемма | less | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `EQUAL` | лемма | equal | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `LEQ` | лемма | leq | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `GREATER` | лемма | greater | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `NEQ` | лемма вне contract-check | вне: neq | развёртка | посчитан, ветвлений 6 |
| `GEQ` | лемма вне contract-check | вне: geq | развёртка | посчитан, ветвлений 6 |
| `CMP` | лемма вне contract-check | вне: cmp | развёртка | посчитан, ветвлений 10 |
| `ISNAN` | лемма вне contract-check | вне: isnan_nan, isnan_num | развёртка | посчитан, ветвлений 6 |
| `CHKNAN` | лемма вне contract-check | вне: chknan_nan, chknan_num | развёртка | посчитан, ветвлений 6 |
| `QSGN` | лемма вне contract-check | вне: qsgn | развёртка | посчитан, ветвлений 10 |
| `QLESS` | лемма вне contract-check | вне: qless | развёртка | посчитан, ветвлений 6 |
| `QEQUAL` | лемма вне contract-check | вне: qequal | развёртка | посчитан, ветвлений 6 |
| `QLEQ` | лемма вне contract-check | вне: qleq | развёртка | посчитан, ветвлений 6 |
| `QGREATER` | лемма вне contract-check | вне: qgreater | развёртка | посчитан, ветвлений 6 |
| `QNEQ` | лемма вне contract-check | вне: qneq | развёртка | посчитан, ветвлений 6 |
| `QGEQ` | лемма вне contract-check | вне: qgeq | развёртка | посчитан, ветвлений 6 |
| `QCMP` | лемма вне contract-check | вне: qcmp | развёртка | посчитан, ветвлений 10 |
| `ADDDIVMOD` | лемма вне contract-check | вне: adddivmod | развёртка | посчитан, ветвлений 19 |
| `ADDDIVMODR` | лемма вне contract-check | вне: adddivmod | развёртка | посчитан, ветвлений 19 |
| `ADDDIVMODC` | лемма вне contract-check | вне: adddivmod | развёртка | посчитан, ветвлений 19 |
| `DIV` | лемма вне contract-check | вне: div, divMod_nan_dividend, divMod_nan_divisor | развёртка | предел глубины рекурсии simp |
| `DIVR` | лемма вне contract-check | вне: div, divMod_nan_dividend, divMod_nan_divisor | развёртка | предел глубины рекурсии simp |
| `DIVC` | лемма вне contract-check | вне: div, divMod_nan_dividend, divMod_nan_divisor | развёртка | предел глубины рекурсии simp |
| `MOD` | лемма вне contract-check | вне: divMod_nan_dividend, divMod_nan_divisor, mod | развёртка | предел глубины рекурсии simp |
| `MODR` | лемма вне contract-check | вне: divMod_nan_dividend, divMod_nan_divisor, mod | развёртка | предел глубины рекурсии simp |
| `MODC` | лемма вне contract-check | вне: divMod_nan_dividend, divMod_nan_divisor, mod | развёртка | предел глубины рекурсии simp |
| `DIVMOD` | лемма вне contract-check | вне: divMod_nan_dividend, divMod_nan_divisor, divmod | развёртка | предел глубины рекурсии simp |
| `DIVMODR` | лемма вне contract-check | вне: divMod_nan_dividend, divMod_nan_divisor, divmod | развёртка | предел глубины рекурсии simp |
| `DIVMODC` | лемма вне contract-check | вне: divMod_nan_dividend, divMod_nan_divisor, divmod | развёртка | предел глубины рекурсии simp |
| `QADDDIVMOD` | лемма вне contract-check | вне: adddivmod | развёртка | посчитан, ветвлений 21 |
| `QADDDIVMODR` | лемма вне contract-check | вне: adddivmod | развёртка | посчитан, ветвлений 21 |
| `QADDDIVMODC` | лемма вне contract-check | вне: adddivmod | развёртка | посчитан, ветвлений 21 |
| `QDIV` | лемма вне contract-check | вне: div, divMod_nan_dividend, divMod_nan_divisor | развёртка | предел глубины рекурсии simp |
| `QDIVR` | лемма вне contract-check | вне: div, divMod_nan_dividend, divMod_nan_divisor | развёртка | предел глубины рекурсии simp |
| `QDIVC` | лемма вне contract-check | вне: div, divMod_nan_dividend, divMod_nan_divisor | развёртка | предел глубины рекурсии simp |
| `QMOD` | лемма вне contract-check | вне: divMod_nan_dividend, divMod_nan_divisor, mod | развёртка | предел глубины рекурсии simp |
| `QMODR` | лемма вне contract-check | вне: divMod_nan_dividend, divMod_nan_divisor, mod | развёртка | предел глубины рекурсии simp |
| `QMODC` | лемма вне contract-check | вне: divMod_nan_dividend, divMod_nan_divisor, mod | развёртка | предел глубины рекурсии simp |
| `QDIVMOD` | лемма вне contract-check | вне: divMod_nan_dividend, divMod_nan_divisor, divmod | развёртка | предел глубины рекурсии simp |
| `QDIVMODR` | лемма вне contract-check | вне: divMod_nan_dividend, divMod_nan_divisor, divmod | развёртка | предел глубины рекурсии simp |
| `QDIVMODC` | лемма вне contract-check | вне: divMod_nan_dividend, divMod_nan_divisor, divmod | развёртка | предел глубины рекурсии simp |
| `ADDRSHIFTMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `ADDRSHIFTMODR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `ADDRSHIFTMODC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `RSHIFTR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `RSHIFTC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MODPOW2` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MODPOW2R` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MODPOW2C` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `RSHIFTMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `RSHIFTMODR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `RSHIFTMODC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QADDRSHIFTMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QADDRSHIFTMODR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QADDRSHIFTMODC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QRSHIFTR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QRSHIFTC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QMODPOW2` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QMODPOW2R` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QMODPOW2C` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QRSHIFTMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QRSHIFTMODR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QRSHIFTMODC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULADDDIVMOD` | лемма вне contract-check | вне: muladddivmod | развёртка | посчитан, ветвлений 19 |
| `MULADDDIVMODR` | лемма вне contract-check | вне: muladddivmod | развёртка | посчитан, ветвлений 19 |
| `MULADDDIVMODC` | лемма вне contract-check | вне: muladddivmod | развёртка | посчитан, ветвлений 19 |
| `MULDIV` | лемма вне contract-check | вне: muldiv | развёртка | предел глубины рекурсии simp |
| `MULDIVR` | лемма вне contract-check | вне: muldiv | развёртка | предел глубины рекурсии simp |
| `MULDIVC` | лемма вне contract-check | вне: muldiv | развёртка | предел глубины рекурсии simp |
| `MULMOD` | лемма вне contract-check | вне: mulmod | развёртка | предел глубины рекурсии simp |
| `MULMODR` | лемма вне contract-check | вне: mulmod | развёртка | предел глубины рекурсии simp |
| `MULMODC` | лемма вне contract-check | вне: mulmod | развёртка | предел глубины рекурсии simp |
| `MULDIVMOD` | лемма вне contract-check | вне: muldivmod | развёртка | предел глубины рекурсии simp |
| `MULDIVMODR` | лемма вне contract-check | вне: muldivmod | развёртка | предел глубины рекурсии simp |
| `MULDIVMODC` | лемма вне contract-check | вне: muldivmod | развёртка | предел глубины рекурсии simp |
| `QMULADDDIVMOD` | лемма вне contract-check | вне: muladddivmod | развёртка | посчитан, ветвлений 21 |
| `QMULADDDIVMODR` | лемма вне contract-check | вне: muladddivmod | развёртка | посчитан, ветвлений 21 |
| `QMULADDDIVMODC` | лемма вне contract-check | вне: muladddivmod | развёртка | посчитан, ветвлений 21 |
| `QMULDIV` | лемма вне contract-check | вне: muldiv | развёртка | предел глубины рекурсии simp |
| `QMULDIVR` | лемма вне contract-check | вне: muldiv | развёртка | предел глубины рекурсии simp |
| `QMULDIVC` | лемма вне contract-check | вне: muldiv | развёртка | предел глубины рекурсии simp |
| `QMULMOD` | лемма вне contract-check | вне: mulmod | развёртка | предел глубины рекурсии simp |
| `QMULMODR` | лемма вне contract-check | вне: mulmod | развёртка | предел глубины рекурсии simp |
| `QMULMODC` | лемма вне contract-check | вне: mulmod | развёртка | предел глубины рекурсии simp |
| `QMULDIVMOD` | лемма вне contract-check | вне: muldivmod | развёртка | предел глубины рекурсии simp |
| `QMULDIVMODR` | лемма вне contract-check | вне: muldivmod | развёртка | предел глубины рекурсии simp |
| `QMULDIVMODC` | лемма вне contract-check | вне: muldivmod | развёртка | предел глубины рекурсии simp |
| `MULADDRSHIFTMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULADDRSHIFTRMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULADDRSHIFTCMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULRSHIFT` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULRSHIFTR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULRSHIFTC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULMODPOW2` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULMODPOW2R` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULMODPOW2C` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULRSHIFTMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULRSHIFTRMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULRSHIFTCMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QMULADDRSHIFTMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QMULADDRSHIFTRMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QMULADDRSHIFTCMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QMULRSHIFT` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QMULRSHIFTR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QMULRSHIFTC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QMULMODPOW2` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QMULMODPOW2R` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QMULMODPOW2C` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QMULRSHIFTMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QMULRSHIFTRMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QMULRSHIFTCMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFTADDDIVMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFTADDDIVMODR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFTADDDIVMODC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFTDIV` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFTDIVR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFTDIVC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFTMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFTMODR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFTMODC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFTDIVMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFTDIVMODR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFTDIVMODC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QLSHIFTADDDIVMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QLSHIFTADDDIVMODR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QLSHIFTADDDIVMODC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QLSHIFTDIV` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QLSHIFTDIVR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QLSHIFTDIVC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QLSHIFTMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QLSHIFTMODR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QLSHIFTMODC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QLSHIFTDIVMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QLSHIFTDIVMODR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QLSHIFTDIVMODC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `ADDINT` | лемма вне contract-check | вне: addInt | развёртка | посчитан, ветвлений 6 |
| `MULINT` | лемма вне contract-check | вне: mulInt | развёртка | посчитан, ветвлений 0 |
| `QADDINT` | лемма вне contract-check | вне: qaddInt | развёртка | посчитан, ветвлений 6 |
| `QMULINT` | лемма вне contract-check | вне: qmulInt | развёртка | посчитан, ветвлений 0 |
| `EQINT` | лемма вне contract-check | вне: eqInt | развёртка | посчитан, ветвлений 6 |
| `LESSINT` | лемма вне contract-check | вне: lessInt | блок: execLessIntCore (private-определение: unfoldModelRun его не разворачивает) | стоит на execLessIntCore |
| `GTINT` | лемма вне contract-check | вне: gtInt | развёртка | посчитан, ветвлений 6 |
| `NEQINT` | лемма вне contract-check | вне: neqInt | развёртка | посчитан, ветвлений 6 |
| `QEQINT` | лемма вне contract-check | вне: qeqInt | развёртка | посчитан, ветвлений 6 |
| `QLESSINT` | лемма вне contract-check | вне: qlessInt | блок: execLessIntCore (private-определение: unfoldModelRun его не разворачивает) | стоит на execLessIntCore |
| `QGTINT` | лемма вне contract-check | вне: qgtInt | развёртка | посчитан, ветвлений 6 |
| `QNEQINT` | лемма вне contract-check | вне: qneqInt | развёртка | посчитан, ветвлений 6 |
| `PUSHPOW2DEC` | лемма вне contract-check | вне: pushPow2Dec | развёртка | посчитан, ветвлений 0 |
| `PUSHNEGPOW2` | лемма вне contract-check | вне: pushNegPow2 | развёртка | посчитан, ветвлений 0 |
| `FITS` | лемма вне contract-check | вне: fits | развёртка | посчитан, ветвлений 6 |
| `UFITS` | лемма вне contract-check | вне: ufits | развёртка | посчитан, ветвлений 6 |
| `QFITS` | лемма вне contract-check | вне: fits | развёртка | посчитан, ветвлений 6 |
| `QUFITS` | лемма вне contract-check | вне: ufits | развёртка | посчитан, ветвлений 6 |
| `PUSHPOW2` | лемма | pushPow2 | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `ADDRSHIFT#MOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `ADDRSHIFTR#MOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `ADDRSHIFTC#MOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `RSHIFT#` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `RSHIFTR#` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `RSHIFTC#` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MODPOW2#` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MODPOW2R#` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MODPOW2C#` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `RSHIFT#MOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `RSHIFTR#MOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `RSHIFTC#MOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULADDRSHIFT#MOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULADDRSHIFTR#MOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULADDRSHIFTC#MOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `MULRSHIFT#` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `MULRSHIFTR#` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `MULRSHIFTC#` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `MULMODPOW2#` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `MULMODPOW2R#` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `MULMODPOW2C#` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `MULRSHIFT#MOD` | развёртка обработчика | — | развёртка | посчитан, ветвлений 10 |
| `MULRSHIFTR#MOD` | развёртка обработчика | — | развёртка | посчитан, ветвлений 10 |
| `MULRSHIFTC#MOD` | развёртка обработчика | — | развёртка | посчитан, ветвлений 10 |
| `LSHIFT#ADDDIVMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFT#ADDDIVMODR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFT#ADDDIVMODC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFT#DIV` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFT#DIVR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFT#DIVC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFT#MOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFT#MODR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFT#MODC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFT#DIVMOD` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFT#DIVMODR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFT#DIVMODC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LSHIFT_VAR` | лемма вне contract-check | вне: lshift | развёртка | посчитан, ветвлений 19 |
| `LSHIFT` | лемма вне contract-check | вне: lshiftConst | развёртка | посчитан, ветвлений 6 |
| `QLSHIFT_VAR` | лемма вне contract-check | вне: lshiftVar | блок: popLongLike (private-определение: unfoldModelRun его не разворачивает) | стоит на popLongLike |
| `QLSHIFT` | лемма вне contract-check | вне: lshiftConst | развёртка | посчитан, ветвлений 6 |
| `RSHIFT_VAR` | лемма вне contract-check | вне: rshift | развёртка | посчитан, ветвлений 14 |
| `RSHIFT` | лемма вне contract-check | вне: rshiftConst | развёртка | посчитан, ветвлений 6 |
| `RSHIFT_ALT` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `QRSHIFT_VAR` | лемма вне contract-check | вне: rshiftVar | блок: popLongLike (private-определение: unfoldModelRun его не разворачивает) | стоит на popLongLike |
| `QRSHIFT` | лемма вне contract-check | вне: rshiftConst | развёртка | посчитан, ветвлений 6 |
| `QRSHIFT_ALT` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `PUSHINT_4` | лемма | pushInt | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUSHINT_8` | лемма | pushInt | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUSHINT_16` | лемма | pushInt | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUSHINT_LONG` | лемма | pushInt | развёртка | лемма срабатывает; посчитан, ветвлений 0 |

### cell

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `SEMPTY` | лемма вне contract-check | вне: sempty | развёртка | посчитан, ветвлений 6 |
| `SDEMPTY` | лемма вне contract-check | вне: sdempty | развёртка | посчитан, ветвлений 6 |
| `SREMPTY` | лемма вне contract-check | вне: srempty | развёртка | посчитан, ветвлений 6 |
| `SDFIRST` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `SDLEXCMP` | развёртка обработчика | — | развёртка | посчитан, ветвлений 28 |
| `SDEQ` | лемма вне contract-check | вне: sdEq | развёртка | посчитан, ветвлений 6 |
| `SDPFX` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SDPFXREV` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SDPPFX` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SDPPFXREV` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SDSFX` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `SDSFXREV` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `SDPSFX` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `SDPSFXREV` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `SDCNTLEAD0` | лемма вне contract-check | вне: sdCntLead0 | развёртка | посчитан, ветвлений 0 |
| `SDCNTLEAD1` | лемма вне contract-check | вне: sdCntLead1 | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `SDCNTTRAIL0` | лемма вне contract-check | вне: sdCntTrail0 | развёртка | посчитан, ветвлений 0 |
| `SDCNTTRAIL1` | лемма вне contract-check | вне: sdCntTrail1 | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `NEWC` | лемма | newc | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `ENDC` | лемма | endc | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `ENDCST` | развёртка обработчика | — | развёртка | посчитан, ветвлений 11 |
| `STBREF` | лемма вне contract-check | вне: stbRef | развёртка | посчитан, ветвлений 11 |
| `STB` | лемма вне contract-check | вне: stb | развёртка | посчитан, ветвлений 6 |
| `STREFR` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `STBREFR` | лемма вне contract-check | вне: stbRef_rev | развёртка | посчитан, ветвлений 11 |
| `STSLICER` | лемма вне contract-check | вне: stSlice_rev | развёртка | предел глубины рекурсии simp |
| `STBR` | лемма вне contract-check | вне: stb_rev | развёртка | посчитан, ветвлений 6 |
| `STREFQ` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `STBREFQ` | лемма вне contract-check | вне: stbRef | развёртка | посчитан, ветвлений 11 |
| `STSLICEQ` | лемма вне contract-check | вне: stSlice | развёртка | посчитан, ветвлений 6 |
| `STBQ` | лемма вне contract-check | вне: stb | развёртка | посчитан, ветвлений 6 |
| `STREFRQ` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `STBREFRQ` | лемма вне contract-check | вне: stbRef_rev | развёртка | посчитан, ветвлений 11 |
| `STSLICERQ` | лемма вне contract-check | вне: stSlice_rev | развёртка | предел глубины рекурсии simp |
| `STBRQ` | лемма вне contract-check | вне: stb_rev | развёртка | посчитан, ветвлений 6 |
| `ENDXC` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `BDEPTH` | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `BBITS` | лемма вне contract-check | вне: bbits | развёртка | посчитан, ветвлений 0 |
| `BREFS` | лемма вне contract-check | вне: brefs | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `BBITREFS` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `BREMBITS` | лемма вне contract-check | вне: brembits | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `BREMREFS` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `BREMBITREFS` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `BCHKREFS` | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | предел глубины рекурсии simp |
| `BCHKBITREFS` | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | предел глубины рекурсии simp |
| `BCHKREFSQ` | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | предел глубины рекурсии simp |
| `BCHKBITREFSQ` | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | предел глубины рекурсии simp |
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
| `SCUTFIRST` | лемма вне contract-check | вне: scutfirst | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 23 |
| `SSKIPFIRST` | лемма вне contract-check | вне: sskipfirst | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 23 |
| `SCUTLAST` | лемма вне contract-check | вне: scutlast | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 23 |
| `SSKIPLAST` | лемма вне contract-check | вне: sskiplast | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 23 |
| `SUBSLICE` | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | предел heartbeats |
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
| `SBITREFS` | лемма вне contract-check | вне: sbitrefs | развёртка | посчитан, ветвлений 0 |
| `LDZEROES` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `LDONES` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `LDSAME` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 15 |
| `SDEPTH` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `CDEPTH` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `CLEVEL` v6 | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `CLEVELMASK` v6 | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `CHASHIX` v6 | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: Cell.computeLevelInfo? |
| `CDEPTHIX` v6 | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: Cell.computeLevelInfo? |
| `LDGRAMS` | лемма вне contract-check | вне: ldGrams | блок: liftM (вне модели, нет леммы vm_run) | стоит на liftM |
| `LDVARINT16` | лемма вне contract-check | вне: ldVarInt | развёртка | предел глубины рекурсии simp |
| `STGRAMS` | лемма вне contract-check | вне: stGrams | развёртка | посчитан, ветвлений 14 |
| `STVARINT16` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LDVARUINT32` | лемма вне contract-check | вне: ldVarInt | развёртка | стоит на liftM |
| `LDVARINT32` | лемма вне contract-check | вне: ldVarInt | развёртка | стоит на liftM |
| `STVARUINT32` | лемма вне contract-check | вне: stVarUInt | развёртка | предел глубины рекурсии simp |
| `STVARINT32` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LDMSGADDR` | лемма вне contract-check | вне: ldMsgAddr, ldMsgAddr_any, ldMsgAddr_error | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `LDMSGADDRQ` | лемма вне contract-check | вне: ldMsgAddr, ldMsgAddr_error | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `STIX` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `STUX` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `STIXR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `STUXR` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `STIXQ` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `STUXQ` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `STIXRQ` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `STUXRQ` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `STILE4` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `STULE4` | развёртка обработчика | — | развёртка | посчитан, ветвлений 10 |
| `STILE8` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `STULE8` | развёртка обработчика | — | развёртка | посчитан, ветвлений 10 |
| `LDIX` | лемма вне contract-check | вне: loadIntVar | развёртка | посчитан, ветвлений 19 |
| `LDUX` | лемма вне contract-check | вне: loadIntVar | развёртка | посчитан, ветвлений 19 |
| `PLDIX` | лемма вне contract-check | вне: loadIntVar | развёртка | посчитан, ветвлений 19 |
| `PLDUX` | лемма вне contract-check | вне: loadIntVar | развёртка | посчитан, ветвлений 19 |
| `LDIXQ` | лемма вне contract-check | вне: loadIntVar | развёртка | посчитан, ветвлений 19 |
| `LDUXQ` | лемма вне contract-check | вне: loadIntVar | развёртка | посчитан, ветвлений 19 |
| `PLDIXQ` | лемма вне contract-check | вне: loadIntVar | развёртка | посчитан, ветвлений 19 |
| `PLDUXQ` | лемма вне contract-check | вне: loadIntVar | развёртка | посчитан, ветвлений 19 |
| `LDSLICEX` | лемма с условием | ldslicex; вне: loadSliceX | развёртка | посчитан, ветвлений 15 |
| `PLDSLICEX` | лемма вне contract-check | вне: loadSliceX | развёртка | посчитан, ветвлений 15 |
| `LDSLICEXQ` | лемма вне contract-check | вне: loadSliceX | развёртка | посчитан, ветвлений 15 |
| `PLDSLICEXQ` | лемма вне contract-check | вне: loadSliceX | развёртка | посчитан, ветвлений 15 |
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
| `STIR` | лемма вне contract-check | вне: stIntFixed_rev | развёртка | предел глубины рекурсии simp |
| `STUR` | лемма вне contract-check | вне: stIntFixed_rev | развёртка | предел глубины рекурсии simp |
| `STIQ` | лемма вне contract-check | вне: stIntFixed | развёртка | предел глубины рекурсии simp |
| `STUQ` | лемма вне contract-check | вне: stIntFixed | развёртка | предел глубины рекурсии simp |
| `STIRQ` | лемма вне contract-check | вне: stIntFixed_rev | развёртка | предел глубины рекурсии simp |
| `STURQ` | лемма вне contract-check | вне: stIntFixed_rev | развёртка | предел глубины рекурсии simp |
| `PLDI` | лемма | loadInt | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `PLDU` | лемма | loadInt | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LDIQ` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `LDUQ` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `PLDIQ` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `PLDUQ` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `PLDUZ` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `PLDSLICE` | лемма | loadSliceFixed; вне: loadSliceFixed_any | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `LDSLICEQ` | лемма вне contract-check | вне: loadSliceFixed_any | развёртка | посчитан, ветвлений 6 |
| `PLDSLICEQ` | лемма вне contract-check | вне: loadSliceFixed_any | развёртка | посчитан, ветвлений 6 |
| `PUSHREF` | лемма | pushRef | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PUSHREFSLICE` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `PUSHREFCONT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SDBEGINSX` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SDBEGINSXQ` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SDBEGINS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SDBEGINSQ` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `STREFCONST` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `STREF2CONST` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `STREF` | лемма | stref | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `STREF_ALT` | лемма | stref | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `STSLICE` | лемма вне contract-check | вне: stSlice | развёртка | посчитан, ветвлений 6 |
| `STSLICE_ALT` | лемма вне contract-check | вне: stSlice | развёртка | посчитан, ветвлений 6 |
| `STI` | лемма вне contract-check | вне: sti | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `STI_ALT` | лемма вне contract-check | вне: stIntFixed | развёртка | предел глубины рекурсии simp |
| `STU` | лемма | stu | развёртка | лемма срабатывает; посчитан, ветвлений 10 |
| `STU_ALT` | лемма вне contract-check | вне: stIntFixed | развёртка | предел глубины рекурсии simp |
| `LDI` | лемма | loadInt | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LDI_ALT` | лемма | loadInt | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LDU` | лемма | ldu | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `LDU_ALT` | лемма | loadInt | развёртка | лемма срабатывает; предел глубины рекурсии simp |
| `LDSLICE` | лемма | loadSliceFixed; вне: loadSliceFixed_any | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `LDSLICE_ALT` | лемма | loadSliceFixed; вне: loadSliceFixed_any | развёртка | лемма срабатывает; посчитан, ветвлений 6 |
| `BCHKBITS_VAR` | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | предел глубины рекурсии simp |
| `BCHKBITS` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `BCHKBITSQ_VAR` | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | предел глубины рекурсии simp |
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
| `CALLCC` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `JMPXDATA` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `CALLXVARARGS` | не исполняется | — | блок: popCallxVarArgBounded (private-определение: unfoldModelRun его не разворачивает) | стоит на popCallxVarArgBounded; остаются термами: VM.call |
| `RETVARARGS` | не исполняется | — | развёртка | стоит на VM.jump; остаются термами: VM.jump |
| `JMPXVARARGS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 16 |
| `CALLCCVARARGS` | не исполняется | — | блок: popCallccVarArgBounded (private-определение: unfoldModelRun его не разворачивает) | стоит на popCallccVarArgBounded; остаются термами: VM.jump |
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
| `SETCONTVARARGS` | не исполняется | — | блок: popSetContVarArgBounded (private-определение: unfoldModelRun его не разворачивает) | предел heartbeats |
| `SETNUMVARARGS` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `BLESS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `BLESSVARARGS` | не исполняется | — | блок: popBlessVarArgMore (private-определение: unfoldModelRun его не разворачивает) | стоит на popBlessVarArgMore |
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
| `BOOLEVAL` | не исполняется | — | развёртка | предел глубины рекурсии simp |
| `SAMEALT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `SAMEALTSAVE` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `SETCONTCTRMANY` v9 | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `CALLCCARGS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `JMPDICT` | лемма | jmpDict | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `PREPAREDICT` | лемма | prepareDict | развёртка | лемма срабатывает; посчитан, ветвлений 0 |
| `JMPXARGS` | не исполняется | — | развёртка | стоит на VM.jump; остаются термами: VM.jump |
| `RETARGS` | не исполняется | — | развёртка | стоит на VM.jump; остаются термами: VM.jump |
| `RETURNARGS` | не исполняется | — | развёртка | предел heartbeats |
| `SETCONTARGS` | лемма вне contract-check | вне: setContArgs_ord | развёртка | предел глубины рекурсии simp |
| `BLESSARGS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 0 |
| `IFBITJMP` | не исполняется | — | блок: popIntFiniteKeepAndBit (private-определение: unfoldModelRun его не разворачивает) | стоит на popIntFiniteKeepAndBit; остаются термами: VM.jump |
| `IFNBITJMP` | не исполняется | — | блок: popIntFiniteKeepAndBit (private-определение: unfoldModelRun его не разворачивает) | стоит на popIntFiniteKeepAndBit; остаются термами: VM.jump |
| `CALLREF` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `JMPREF` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `JMPREFDATA` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `IFREF` | развёртка обработчика | — | развёртка | посчитан, ветвлений 11 |
| `IFNOTREF` | развёртка обработчика | — | развёртка | посчитан, ветвлений 11 |
| `IFJMPREF` | развёртка обработчика | — | развёртка | посчитан, ветвлений 11 |
| `IFNOTJMPREF` | развёртка обработчика | — | развёртка | посчитан, ветвлений 11 |
| `IFREFELSE` | развёртка обработчика | — | развёртка | посчитан, ветвлений 11 |
| `IFELSEREF` | развёртка обработчика | — | развёртка | посчитан, ветвлений 11 |
| `IFREFELSEREF` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads, VM.call |
| `IFBITJMPREF` | не исполняется | — | блок: popIntFiniteKeepAndBit (private-определение: unfoldModelRun его не разворачивает) | стоит на popIntFiniteKeepAndBit; остаются термами: VM.jump |
| `IFNBITJMPREF` | не исполняется | — | блок: popIntFiniteKeepAndBit (private-определение: unfoldModelRun его не разворачивает) | стоит на popIntFiniteKeepAndBit; остаются термами: VM.jump |
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
| `PUSHCTR` | лемма с условием | pushRoot (1/7 аргументов) | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `POPCTR` | лемма с условием | popRoot (1/7 аргументов) | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
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
| `AGAINBRK` | не исполняется | — | развёртка | предел глубины рекурсии simp |
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
| `STDICT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 6 |
| `SKIPDICT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 15 |
| `LDDICTS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 15 |
| `PLDDICTS` | развёртка обработчика | — | развёртка | посчитан, ветвлений 15 |
| `LDDICT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 20 |
| `PLDDICT` | развёртка обработчика | — | развёртка | посчитан, ветвлений 20 |
| `LDDICTQ` | развёртка обработчика | — | развёртка | посчитан, ветвлений 20 |
| `PLDDICTQ` | развёртка обработчика | — | развёртка | посчитан, ветвлений 20 |
| `PFXDICTSET` | не исполняется | — | блок: DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.pushDictRoot (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает) | стоит на DictExt.pushDictRoot, DictExt.prechargeRootLoad |
| `PFXDICTREPLACE` | не исполняется | — | блок: DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.pushDictRoot (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает) | стоит на DictExt.pushDictRoot, DictExt.prechargeRootLoad |
| `PFXDICTADD` | не исполняется | — | блок: DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.pushDictRoot (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает) | стоит на DictExt.pushDictRoot, DictExt.prechargeRootLoad |
| `PFXDICTDEL` | не исполняется | — | блок: DictExt.consumeCreatedGas (private-определение: unfoldModelRun его не разворачивает), DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.pushDictRoot (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает) | стоит на DictExt.pushDictRoot, DictExt.prechargeRootLoad |
| `PFXDICTGETQ` | не исполняется | — | блок: DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает) | стоит на DictExt.prechargeRootLoad |
| `PFXDICTGET` | не исполняется | — | блок: DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает) | стоит на DictExt.prechargeRootLoad |
| `PFXDICTGETJMP` | не исполняется | — | блок: DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает) | стоит на DictExt.prechargeRootLoad |
| `PFXDICTGETEXEC` | не исполняется | — | блок: DictExt.prechargeRootLoad (private-определение: unfoldModelRun его не разворачивает), DictExt.pushBool (private-определение: unfoldModelRun его не разворачивает), DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает) | стоит на DictExt.prechargeRootLoad |
| `DICTIGETJMP` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETJMP` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTIGETEXEC` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETEXEC` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTIGETJMPZ` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETJMPZ` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTIGETEXECZ` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETEXECZ` | лемма с условием | dictGetExec_empty, dictGetExec_found, dictGetExec_noKey, dictGetExec_notFound | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTGET` | лемма с условием | dictGetSlice_found, dictGetSlice_notFound, dictGetSlice_short; вне: dictGetSlice_wf | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTGETREF` | лемма вне contract-check | вне: dictGetSlice_wf | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTIGET` | лемма с условием | dictGetInt_empty, dictGetInt_found, dictGetInt_noKey, dictGetInt_notFound; вне: dictGetInt_wf | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTIGETREF` | лемма с условием | dictGetIntRef_found, dictGetIntRef_notFound (только словарь-константа); вне: dictGetInt_wf | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGET` | лемма с условием | dictGetInt_empty, dictGetInt_found, dictGetInt_noKey, dictGetInt_notFound; вне: dictGetInt_wf | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETREF` | лемма с условием | dictGetIntRef_found, dictGetIntRef_notFound (только словарь-константа); вне: dictGetInt_wf | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTSET` | лемма вне contract-check | вне: dictSetSliceEmpty_flag, dictSetSliceEmpty_set, dictSetSlice_flag, dictSetSlice_set | развёртка | предел глубины рекурсии simp |
| `DICTSETREF` | лемма вне contract-check | вне: dictSetSliceRefEmpty_flag, dictSetSliceRefEmpty_set, dictSetSliceRef_flag, dictSetSliceRef_set | развёртка | предел глубины рекурсии simp |
| `DICTISET` | лемма вне contract-check | вне: dictSetIntEmpty_flag, dictSetIntEmpty_set, dictSetInt_flag, dictSetInt_set | развёртка | предел heartbeats |
| `DICTISETREF` | лемма вне contract-check | вне: dictSetIntRefEmpty_flag, dictSetIntRefEmpty_set, dictSetIntRef_flag, dictSetIntRef_set | развёртка | предел heartbeats |
| `DICTUSET` | лемма вне contract-check | вне: dictSetIntEmpty_flag, dictSetIntEmpty_set, dictSetInt_flag, dictSetInt_set | развёртка | предел heartbeats |
| `DICTUSETREF` | лемма вне contract-check | вне: dictSetIntRefEmpty_flag, dictSetIntRefEmpty_set, dictSetIntRef_flag, dictSetIntRef_set | развёртка | предел heartbeats |
| `DICTSETGET` | лемма вне contract-check | вне: dictSetGetSlice, dictSetGetSliceEmpty | развёртка | предел глубины рекурсии simp |
| `DICTSETGETREF` | лемма вне contract-check | вне: dictSetGetSliceRef, dictSetGetSliceRefEmpty | развёртка | предел глубины рекурсии simp |
| `DICTISETGET` | лемма вне contract-check | вне: dictSetGetInt, dictSetGetIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTISETGETREF` | лемма вне contract-check | вне: dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUSETGET` | лемма вне contract-check | вне: dictSetGetInt, dictSetGetIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUSETGETREF` | лемма вне contract-check | вне: dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTREPLACE` | лемма вне contract-check | вне: dictSetSliceEmpty_flag, dictSetSlice_flag | развёртка | предел heartbeats |
| `DICTREPLACEREF` | лемма вне contract-check | вне: dictSetSliceRefEmpty_flag, dictSetSliceRef_flag | развёртка | предел heartbeats |
| `DICTIREPLACE` | лемма вне contract-check | вне: dictSetIntEmpty_flag, dictSetInt_flag | развёртка | предел heartbeats |
| `DICTIREPLACEREF` | лемма вне contract-check | вне: dictSetIntRefEmpty_flag, dictSetIntRef_flag | развёртка | предел heartbeats |
| `DICTUREPLACE` | лемма вне contract-check | вне: dictSetIntEmpty_flag, dictSetInt_flag | развёртка | предел heartbeats |
| `DICTUREPLACEREF` | лемма вне contract-check | вне: dictSetIntRefEmpty_flag, dictSetIntRef_flag | развёртка | предел heartbeats |
| `DICTREPLACEGET` | лемма вне contract-check | вне: dictSetGetSlice, dictSetGetSliceEmpty | развёртка | предел глубины рекурсии simp |
| `DICTREPLACEGETREF` | лемма вне contract-check | вне: dictSetGetSliceRef, dictSetGetSliceRefEmpty | развёртка | предел глубины рекурсии simp |
| `DICTIREPLACEGET` | лемма вне contract-check | вне: dictSetGetInt, dictSetGetIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTIREPLACEGETREF` | лемма вне contract-check | вне: dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUREPLACEGET` | лемма вне contract-check | вне: dictSetGetInt, dictSetGetIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUREPLACEGETREF` | лемма вне contract-check | вне: dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTADD` | лемма вне contract-check | вне: dictSetSliceEmpty_flag, dictSetSlice_flag | развёртка | предел heartbeats |
| `DICTADDREF` | лемма вне contract-check | вне: dictSetSliceRefEmpty_flag, dictSetSliceRef_flag | развёртка | предел heartbeats |
| `DICTIADD` | лемма вне contract-check | вне: dictSetIntEmpty_flag, dictSetInt_flag | развёртка | предел heartbeats |
| `DICTIADDREF` | лемма вне contract-check | вне: dictSetIntRefEmpty_flag, dictSetIntRef_flag | развёртка | предел heartbeats |
| `DICTUADD` | лемма вне contract-check | вне: dictSetIntEmpty_flag, dictSetInt_flag | развёртка | предел heartbeats |
| `DICTUADDREF` | лемма вне contract-check | вне: dictSetIntRefEmpty_flag, dictSetIntRef_flag | развёртка | предел heartbeats |
| `DICTADDGET` | лемма вне contract-check | вне: dictSetGetSlice, dictSetGetSliceEmpty | развёртка | предел глубины рекурсии simp |
| `DICTADDGETREF` | лемма вне contract-check | вне: dictSetGetSliceRef, dictSetGetSliceRefEmpty | развёртка | предел глубины рекурсии simp |
| `DICTIADDGET` | лемма вне contract-check | вне: dictSetGetInt, dictSetGetIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTIADDGETREF` | лемма вне contract-check | вне: dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUADDGET` | лемма вне contract-check | вне: dictSetGetInt, dictSetGetIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUADDGETREF` | лемма вне contract-check | вне: dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTDELGET` | лемма вне contract-check | вне: dictSetGetSlice, dictSetGetSliceEmpty | развёртка | предел глубины рекурсии simp |
| `DICTDELGETREF` | лемма вне contract-check | вне: dictSetGetSliceRef, dictSetGetSliceRefEmpty | развёртка | предел глубины рекурсии simp |
| `DICTIDELGET` | лемма вне contract-check | вне: dictSetGetInt, dictSetGetIntEmpty | развёртка | предел глубины рекурсии simp |
| `DICTIDELGETREF` | лемма вне contract-check | вне: dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | предел глубины рекурсии simp |
| `DICTUDELGET` | лемма вне contract-check | вне: dictSetGetInt, dictSetGetIntEmpty | развёртка | предел глубины рекурсии simp |
| `DICTUDELGETREF` | лемма вне contract-check | вне: dictSetGetIntRef, dictSetGetIntRefEmpty | развёртка | предел глубины рекурсии simp |
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
| `DICTUREMMIN` | не исполняется | — | развёртка | предел heartbeats |
| `DICTUREMMINREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTREMMAX` | не исполняется | — | развёртка | предел heartbeats |
| `DICTREMMAXREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTIREMMAX` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTIREMMAXREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTUREMMAX` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`); остаются термами: VmState.registerCellLoads |
| `DICTUREMMAXREF` | не исполняется | — | развёртка | предел heartbeats |
| `DICTSETB` | лемма вне contract-check | вне: dictSetSliceBEmpty_flag, dictSetSliceBEmpty_set, dictSetSliceB_flag, dictSetSliceB_set | развёртка | предел heartbeats |
| `DICTISETB` | лемма вне contract-check | вне: dictSetIntBEmpty_flag, dictSetIntBEmpty_set, dictSetIntB_flag, dictSetIntB_set | развёртка | предел heartbeats |
| `DICTUSETB` | лемма вне contract-check | вне: dictSetIntBEmpty_flag, dictSetIntBEmpty_set, dictSetIntB_flag, dictSetIntB_set | развёртка | предел heartbeats |
| `DICTSETGETB` | лемма вне contract-check | вне: dictSetGetSliceB, dictSetGetSliceBEmpty | развёртка | стоит на DictExt.prechargeRootLoad |
| `DICTISETGETB` | лемма вне contract-check | вне: dictSetGetIntB, dictSetGetIntBEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUSETGETB` | лемма вне contract-check | вне: dictSetGetIntB, dictSetGetIntBEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTREPLACEB` | не исполняется | — | развёртка | предел heartbeats |
| `DICTIREPLACEB` | не исполняется | — | развёртка | предел heartbeats |
| `DICTUREPLACEB` | не исполняется | — | развёртка | предел heartbeats |
| `DICTREPLACEGETB` | лемма вне contract-check | вне: dictSetGetSliceB, dictSetGetSliceBEmpty | развёртка | стоит на DictExt.prechargeRootLoad |
| `DICTIREPLACEGETB` | лемма вне contract-check | вне: dictSetGetIntB, dictSetGetIntBEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUREPLACEGETB` | лемма вне contract-check | вне: dictSetGetIntB, dictSetGetIntBEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTADDB` | лемма вне contract-check | вне: dictSetSliceBEmpty_flag, dictSetSliceB_flag | развёртка | предел heartbeats |
| `DICTIADDB` | лемма вне contract-check | вне: dictSetIntBEmpty_flag, dictSetIntB_flag | развёртка | предел heartbeats |
| `DICTUADDB` | лемма вне contract-check | вне: dictSetIntBEmpty_flag, dictSetIntB_flag | развёртка | предел heartbeats |
| `DICTADDGETB` | лемма вне contract-check | вне: dictSetGetSliceB, dictSetGetSliceBEmpty | развёртка | стоит на DictExt.prechargeRootLoad |
| `DICTIADDGETB` | лемма вне contract-check | вне: dictSetGetIntB, dictSetGetIntBEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUADDGETB` | лемма вне contract-check | вне: dictSetGetIntB, dictSetGetIntBEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTDEL` | лемма вне contract-check | вне: dictDelSlice, dictDelSliceEmpty | развёртка | стоит на DictExt.prechargeRootLoad |
| `DICTIDEL` | лемма вне contract-check | вне: dictDelInt, dictDelIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUDEL` | лемма вне contract-check | вне: dictDelInt, dictDelIntEmpty | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTGETOPTREF` | не исполняется | — | развёртка | стоит на DictExt.prechargeRootLoad |
| `DICTIGETOPTREF` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTUGETOPTREF` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `DICTSETGETOPTREF` | не исполняется | — | развёртка | стоит на DictExt.prechargeRootLoad |
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
| `PFXDICTSWITCH` | развёртка обработчика | — | блок: DictExt.registerLoaded (private-определение: unfoldModelRun его не разворачивает) | посчитан до `match` по неизвестному значению (делит `vm_split`) |

### tuple

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `PUSHNULL` | лемма вне contract-check | вне: pushNull | развёртка | посчитан, ветвлений 0 |
| `ISNULL` | лемма вне contract-check | вне: isNull | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `TUPLEVAR` | лемма вне contract-check | вне: mktupleVar | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `INDEXVAR` | лемма вне contract-check | вне: indexVar | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 19 |
| `UNTUPLEVAR` | лемма вне contract-check | вне: untupleVar | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `UNPACKFIRSTVAR` | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `EXPLODEVAR` | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `SETINDEXVAR` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 19 |
| `INDEXVARQ` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 19 |
| `SETINDEXVARQ` | не исполняется | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | предел heartbeats |
| `TLEN` | лемма вне contract-check | вне: tlen | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `QTLEN` | лемма вне contract-check | вне: qtlen, qtlen_other | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `ISTUPLE` | лемма вне contract-check | вне: isTuple | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 0 |
| `LAST` | лемма вне contract-check | вне: last | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `TPUSH` | лемма вне contract-check | вне: tpush | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `TPOP` | лемма вне contract-check | вне: tpop | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `NULLSWAPIF` | лемма вне contract-check | вне: nullSwapIf | развёртка | стоит на ForIn.forIn |
| `NULLSWAPIFNOT` | лемма вне contract-check | вне: nullSwapIfNot | развёртка | стоит на ForIn.forIn |
| `NULLROTRIF` | лемма вне contract-check | вне: nullRotrIf | развёртка | стоит на ForIn.forIn |
| `NULLROTRIFNOT` | лемма вне contract-check | вне: nullRotrIfNot | развёртка | стоит на ForIn.forIn |
| `NULLSWAPIF2` | лемма вне contract-check | вне: nullSwapIf2 | развёртка | стоит на ForIn.forIn |
| `NULLSWAPIFNOT2` | лемма вне contract-check | вне: nullSwapIfNot2 | развёртка | стоит на ForIn.forIn |
| `NULLROTRIF2` | лемма вне contract-check | вне: nullRotrIf2 | развёртка | стоит на ForIn.forIn |
| `NULLROTRIFNOT2` | лемма вне contract-check | вне: nullRotrIfNot2 | развёртка | стоит на ForIn.forIn |
| `TUPLE` | лемма вне contract-check | вне: mktuple | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `INDEX` | лемма вне contract-check | вне: index | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 6 |
| `UNTUPLE` | лемма вне contract-check | вне: untuple | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `UNPACKFIRST` | лемма вне contract-check | вне: unpackFirst | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `EXPLODE` | лемма вне contract-check | вне: explode | блок: ForIn.forIn (вне модели, нет леммы vm_run) | стоит на ForIn.forIn |
| `SETINDEX` | лемма вне contract-check | вне: setIndex | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 10 |
| `INDEXQ` | лемма вне contract-check | вне: indexQ, indexQ_null | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан, ветвлений 10 |
| `SETINDEXQ` | лемма вне contract-check | вне: setIndexQ, setIndexQ_null | блок: ForIn.forIn (вне модели, нет леммы vm_run) | предел heartbeats |
| `INDEX2` | лемма вне contract-check | вне: index2 | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `INDEX3` | лемма вне contract-check | вне: index3 | блок: ForIn.forIn (вне модели, нет леммы vm_run) | предел heartbeats |

### msg/actions

| Форма | Статус | Леммы | Обработчик | Прогон |
|---|---|---|---|---|
| `PARSEMSGADDR` | лемма вне contract-check | вне: parseMsgAddr, parseMsgAddr_error | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `PARSEMSGADDRQ` | лемма вне contract-check | вне: parseMsgAddr, parseMsgAddr_error | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `REWRITESTDADDR` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `REWRITESTDADDRQ` | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `REWRITEVARADDR` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `REWRITEVARADDRQ` | развёртка обработчика | — | блок: ForIn.forIn (вне модели, нет леммы vm_run) | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `SENDRAWMSG` | лемма | sendRawMsg | развёртка | лемма срабатывает; посчитан, ветвлений 14 |
| `RAWRESERVE` | лемма с условием | rawReserve; вне: rawReserve_le15 | развёртка | посчитан, ветвлений 32 |
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
| `GETFORWARDFEE` v6 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `GETPRECOMPILEDGAS` v6 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `GETORIGINALFWDFEE` v6 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `GETGASFEESIMPLE` v6 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
| `GETFORWARDFEESIMPLE` v6 | развёртка обработчика | — | развёртка | посчитан до `match` по неизвестному значению (делит `vm_split`) |
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
| `CDATASIZEQ` | не исполняется | — | развёртка | стоит на MonadExcept.tryCatch |
| `CDATASIZE` | не исполняется | — | развёртка | стоит на MonadExcept.tryCatch |
| `SDATASIZEQ` | не исполняется | — | развёртка | стоит на ForIn.forIn |
| `SDATASIZE` | не исполняется | — | развёртка | стоит на ForIn.forIn |

