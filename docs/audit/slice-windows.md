# Аудит: срезы как окна в ячейке

Эталон: `ton-blockchain/ton` @ `3d478cb`. Дата: 2026-10-30.

## Правило

Срез C++ (`CellSlice`) — окно в своей ячейке: биты `bits_st..bits_en`, ссылки `refs_st..refs_en`.
Инструкции, читающие срез, видят только окно: `size()`, `size_refs()`, `prefetch_ref(i)` (от
`refs_st`), `count_leading`, `get_depth()` (`cells/CellSlice.cpp:803-809`: по ссылкам окна) и т. д.
Срез модели (`Slice`) — ячейка и позиции `bitPos`, `refPos`; окно продолжается до конца ячейки
(инструкции, сужающие окно с конца, — `SDCUTFIRST`, `SCUTFIRST`, `SDCUTLAST`, `SDSKIPLAST` и др. —
строят новую ячейку из окна). Расхождение возможно там, где модель читает у среза его ячейку
(`s.cell.<поле>`) без позиций.

Найдено по `grep` в `TvmLean/Semantics` каждого обращения `s.cell.` к срезу (и `.cell` среза как
целой ячейки) и сверено с обработчиком C++.

## Обращения

| Модель | Что читает | C++ | Вердикт |
|---|---|---|---|
| `Exec/CellOp/Sdepth.lean` (`SDEPTH`) | `s.cell.depth` — глубина всей ячейки | `exec_slice_depth` (cellops.cpp:1397-1401) → `CellSlice::get_depth` (CellSlice.cpp:803-809): ссылки окна | **ошибка**, исправлена: `Slice.depth` (ссылки от `refPos`) |
| `Exec/Cell/Ldref.lean`, `LdrefRtos.lean` (`LDREF`, `PLDREF`, `LDREFRTOS`), `Exec/Dict/Lddict.lean` | `s.cell.refs[s.refPos]` | `exec_load_ref`, `exec_load_ref_rev_to_slice` (cellops.cpp:1014, 1037), `exec_load_dict` (dictops.cpp:149): `fetch_ref` / `prefetch_ref(0)` от `refs_st` | совпадает |
| `Exec/Cell/PldRefIdx.lean`, `Exec/CellOp/PldRefVar.lean` (`PLDREFIDX`, `PLDREFVAR`) | `s.cell.refs[s.refPos + idx]` | `exec_preload_ref_fixed`, `exec_preload_ref` (cellops.cpp:989, 1001): `prefetch_ref(idx)` | совпадает |
| `Exec/Cell/SdCntLead0.lean`, `SdCntTrail0.lean`, `Exec/CellOp/Ext.lean` (`SDCNTLEAD0/1`, `SDCNTTRAIL0/1`) | `s.cell.bits` от `bitPos` до конца ячейки | `count_leading`, `count_trailing` окна (cellops.cpp:329-332) | совпадает (окно модели кончается концом ячейки) |
| `Exec/Cell/Sdcutfirst.lean`, `Sdcutlast.lean`, `Sdskiplast.lean`, `Exec/CellOp/Ext.lean` (`SCUTFIRST`, `SSKIPLAST`, `SCUTLAST`, `SUBSLICE`, `SPLIT`) | `s.cell.bits`/`refs` от позиций; результат — новая ячейка из окна | `only_first`, `skip_first`, `only_last`, `skip_last` того же окна (cellops.cpp:1168-1196, 1254, 1470-1497) | совпадает: у среза-результата те же биты и ссылки окна; ячейку среза (её вид, уровень, хэш) никакая инструкция не читает, кроме `SDEPTH` (по ссылкам окна) |
| `Exec/Misc.lean` (`SDATASIZE`) | `s.cell.refs` от `refPos`, `bitsRemaining` | `exec_compute_data_size` (tonops.cpp:1528) | совпадает |
| `Exec/Dict/DictGet.lean`, `DictGetMinMax.lean`, `Exec/TonEnv/ConfigParam.lean`, `GlobalId.lean`, `Exec/Msg/SendMsg.lean` (значение `REF`) | `v.cell.refs[v.refPos]` значения словаря | `prefetch_ref()` значения (dictops.cpp, tonops.cpp) | совпадает |
| `Exec/Msg/SendMsg.lean:217, 288` | конец среза: `bitPos := cell.bits.size` | `cs.skip_first(cs.size())` (tonops.cpp:2221) | совпадает |
| `Exec/Flow/{CallRef,JmpRef,Ifref,…}.lean`, `Exec/TonEnv/RewriteVarAddr.lean`, `Exec/Flow/Runvm.lean` | `.cell` среза как целой ячейки: ссылки кода (срез ячейки-ссылки целиком), новая ячейка адреса, код дочерней VM (её `cc` задан срезом) | `load_cell_slice_ref`, `exec_rewrite_message_addr`, `exec_runvm_common` | совпадает (срезы целые; у `RUNVM` исполняется срез) |
| `Model/Cell/Primitives.lean` (`lbl.remainder.cell.refs[...]`, словари) | ссылки узла после метки | `prefetch_ref` остатка узла (`refs_st` = 0: у метки нет ссылок) | совпадает |

## Как это проверяется

Случаи оракула и fuzz давали срезы целыми (токен `SB:` — ячейка остатка среза), поэтому такие
расхождения не проявлялись. `Tests.Gen.AdvancedSlices` (`Tests/Harness/Gen/AdvancedSlices.lean`):
каждый случай оракула набора и каждый случай fuzz, у которого на стеке есть целый срез обычной
ячейки, прогоняется ещё раз на срезе большей ячейки — до его битов случайные биты, до его ссылок
до четырёх ссылок (сначала глубокие), — который код сначала читает за эти биты и ссылки (`LDU`,
`LDREF`, `NIP`; срез глубже вершины — через `XCHG s0,s(j)`): инструкция исполняется на окне, C++ —
на том же окне той же ячейки.
