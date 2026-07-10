# Route B — request-local implementation plan

Updated: 2026-07-10 21:39 CEST
Status: `RB0_BLOCKED / NOT_RH / CHALLENGER`

Этот план не переопределяет корневой `IMPLEMENTATION_PLAN.md` и не повышает
Route B над официальным H-bridge. Полная лестница находится в
`ROUTE_B_EXECUTION_CONTROL.md`; текущий машинный адрес — в
`ROUTE_B_EXECUTION_STATE.json`.

## Queue rules

- Ровно один физический bus goal может быть `ACTIVE`.
- Если goal без answer нет, `ACTIVE = NONE`; Codex ждёт и ничего не выбирает.
- Codex берёт только наименьший `NNN` без matching answer.
- Один запуск закрывает ровно один goal и заканчивается `STOP`.
- `plan-only`, `read-only`, `ZERO compute` запрещают исполнение и новые данные.
- Новый goal создаёт только Mythos.

## ACTIVE

`NONE — BUS 008 CLOSED; NO OPEN 009 GOAL`

## WAITING

`RB-0 | obligation=PO-0 | target=repair source/ZEO provenance after Bus 008 | owner=Mythos_then_Codex | physical_goal=ABSENT | next_free_nnn=009 | current=CONTRACT_V2_LOCKED + STATE_LOOP_SYNCED + ZEO_EXPORT_AMBIGUOUS + R13_SOURCE_MISSING | verify=python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check | done_when=PROVENANCE_LOCKED and PO-0 closed | if_fail_then=keep RB-0 open; do not enter level 1`

## NEXT CANDIDATES — not selected

Эти строки — только dependency view. Ни одна из них не становится задачей без
физического goal от Mythos.

1. `RB-1 / PO-1 / ExactDetectorDictionary`
2. `RB-2 / PO-2 / ParityInstrumentLock`
3. `RB-3 / PO-11 / ZEOExportSoundness`
4. `RB-4 / PO-12a / SafeFeasibility`

Порядок внутри уровня 1 выбирается после результата `RB-0`; дальнейшие стадии
`RB-5..RB-10` перечислены только в execution control.
