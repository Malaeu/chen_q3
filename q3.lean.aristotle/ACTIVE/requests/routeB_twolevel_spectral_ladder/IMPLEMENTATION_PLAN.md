# Route B — request-local implementation plan

Updated: 2026-07-12 09:27 CEST
Status: `OWNER_AUTHORIZED_AUTORUN_PAUSED_D0_7E_XWALK_SOURCE_GAP / D0.7e.5_BLOCKED / NOT_RH / CHALLENGER`

Этот план не переопределяет корневой `IMPLEMENTATION_PLAN.md` и не повышает
Route B над официальным H-bridge. Полная лестница находится в
`ROUTE_B_EXECUTION_CONTROL.md`; текущий машинный адрес — в
`ROUTE_B_EXECUTION_STATE.json`.

## Queue rules

- Ровно один физический bus goal может быть `ACTIVE`.
- Если goal без answer нет, в `MANUAL_BUS` Codex ждёт; в текущем
  `OWNER_AUTHORIZED_AUTORUN` он выбирает первый допустимый master leaf.
- Codex берёт только наименьший `NNN` без matching answer.
- Одна физическая bus-транзакция закрывает ровно один goal. После валидации
  `MANUAL_BUS` останавливается, а owner autorun возвращается к master DAG.
- `plan-only`, `read-only`, `ZERO compute` запрещают исполнение и новые данные.
- Новый goal создаёт только Mythos.

## ACTIVE

`D0.7e.5 ExactWPrimeZeoCrosswalk — finite bDet definition PROVED on dependent carrier; XWALK THEOREM_SHAPE_ONLY`

Физическая шина: `001..009` закрыты; unanswered goal отсутствует; `010` —
только свободный номер и не создаётся Codex.

## WAITING

`RB-0 | obligation=PO-0 | status=OPEN_AFTER_NEGATIVE_BUS009 | owner=Mythos_then_Codex | physical_goal=ABSENT | next_free_nnn=010 | current=CONTRACT_V2_LOCKED + STATE_LOOP_SYNCED + OVERCLAIM_LIST + OPEN_CRITICAL_ZEO_EXPORT_AMBIGUOUS + R13_SOURCE_MISSING | verify=python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check | done_when=PROVENANCE_LOCKED and PO-0 closed | scheduler_effect=does_not_block_independent_owner-authorized master leaves`

## Current master transaction

`D0.7a..D0.7d` source-lock `delta_(m,N)`, dependent ground/trial and boundary
normalizations, scalar/phase conventions, and the `b` namespace firewall.
Immutable owner input has now passed the finite-definition audit:
`bDet=Fhat(0)/Xi(0)=sqrt(L)c0/zeta(1/2)` on `TrialNonzero`, with exact
reflection `Fplus=T_m(k1)(-z)`; `G=Fhat/bDet` is defined only on
`BDetNonzero`. The input does not supply a legal `N(lambda)` because `kappa` is
unspecified.

The current leaf is the remaining `PO_D0_7E_XWALK`. It requires exact typed
`alpha`, true `DeltaE`, `delta_dict`, a joint `(m,N)` limit, and a uniform
compact-strip bound. The input calls it a theorem shape to be proved, and the
primary source calls its trial-to-ground ingredient missing. Importing its
cited H3c/H4 ingredients at D0.7e would create a D0 dependency cycle. D0.7e and D0.7
remain blocked until this leaf is genuinely `PROVED`; `CONDITIONAL` cannot
close them. No Bus 010 is created by Codex.

## Physical Route B candidates — not selected

Эти строки — только dependency view. Ни одна из них не становится физической
задачей без immutable goal от Mythos.

1. `RB-1 / PO-1 / ExactDetectorDictionary`
2. `RB-2 / PO-2 / ParityInstrumentLock`
3. `RB-3 / PO-11 / ZEOExportSoundness`
4. `RB-4 / PO-12a / SafeFeasibility`

Порядок внутри уровня 1 выбирается после результата `RB-0`; дальнейшие стадии
`RB-5..RB-10` перечислены только в execution control.
