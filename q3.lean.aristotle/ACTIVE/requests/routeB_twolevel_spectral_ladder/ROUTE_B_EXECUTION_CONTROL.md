# Route B — execution control

Status: `OWNER_AUTHORIZED_AUTORUN_PAUSED_EXTERNAL_OWNER_INPUT / CONTROL_PLANE / NOT_RH / CHALLENGER`
Schema: `route_b_execution_control.v2`
Canonical repo: `/Users/emalam/GitHub/rh_lean_01_2026`
Current address: `RB-LAMPORT-D0 / D0.7e / ExactDetectorBDefinitionAndCrosswalk`

## Owner autorun override — 2026-07-11

Ылша explicitly authorized Codex to remove the unconditional post-answer
STOP and drive the recursive Lamport compiler autonomously. The authoritative
master is:

```text
../routeB_lamport_rh_closure/MASTER_GOAL.md
../routeB_lamport_rh_closure/STATE.json
```

Scheduling rule:

```text
physical unanswered bus goal exists -> execute the smallest NNN first
no physical unanswered goal          -> execute the first eligible master leaf
leaf closes                          -> validate, assemble/zoom out, continue
real mathematical blocker            -> record exact fatal code and pause
```

This is an execution-policy override, not a mathematical override. Bus 009's
`OVERCLAIM_LIST`, ZEO ambiguity, and missing rGap13 provenance remain open.
Route B stays `CHALLENGER / NOT_RH`, and D0 object locking does not count as
closing `PO-0` or ZEO.

Этот файл отвечает на вопрос «как мы идём». Текущий машинный ответ на вопрос
«где мы сейчас» хранится в `ROUTE_B_EXECUTION_STATE.json` и проверяется
командой:

```bash
python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check
```

## Короткий ответ прямо сейчас

```text
GLOBAL MAINLINE: T0-pd -> H-bridge -> H4 -> RH
ROUTE B: challenger / NOT_RH
CURRENT: RB-LAMPORT-D0 / D0.7e / ExactDetectorBDefinitionAndCrosswalk
CONTRACT: v2 locked; PO-0/ZEO blockers retained, not bypassed as facts
BUS: 001..009 closed; active physical goal NONE; next free number 010
MODE: OWNER_AUTHORIZED_AUTORUN_PAUSED_EXTERNAL_OWNER_INPUT
CODEX: D0.1--D0.6 and D0.7a--D0.7d proved; exact detector b is missing;
MYTHOS/OWNER: supply D0_7E_OWNER_INPUT_REQUEST.md; do not create 010;
              bPilot/bWeil aliases and H4d bound smuggling are rejected
```

The retired D0.3g blockers remain historical warnings, not current stops:

```text
D0_3_DETECTOR_OPERATOR_MISSING             [retired by finite ratification]
D0_3_DETECTOR_CROSSWALK_UNRATIFIED         [retired at finite (m,N) scope]
D0_3_MU_PROVENANCE_COLLISION               [repaired by nu/epsilon/theta namespaces]
```

Pro review ratified only `Mfin_(m,N)=WeilOp_(m,N)`. It did not define
`M_lambda`, prove a global rank crosswalk, or identify Schur diagnostics
`theta_j` with exact full/sector spectra. With that firewall, D0.3, D0.4, and
D0.5 are proved. D0.7a--D0.7d now lock `delta_(m,N)`, dependent trial/ground
normalizations, scalar/phase conventions, and the `b` namespace firewall.
The unresolved address is D0.7e: the canonical `b` consumed by `W'` is still
`MISSING` in the later object-lock. Pro review returned the primary verdict
`EXTERNAL_OWNER_INPUT_REQUIRED` and rejected promotion of `bPilot`. The exact
minimal source statement is frozen in `D0_7E_OWNER_INPUT_REQUEST.md`. Autorun
is paused at this external-authority boundary; the uniform nonzero/growth
estimates remain separate H4d obligations.

## Разделение полномочий

У Route B нет одного файла, который законно переопределяет всё. Источники
истины разделены по ролям:

1. `PROJECT_ORCHESTRATOR.md` решает архитектурный ранг маршрута. Route B пока
   не mainline, а challenger.
2. Физические пары `bus/NNN_*.goal.md` / `bus/NNN_*.answer.md` решают, есть ли
   исполнимая задача. Наименьший goal без answer — единственная разрешённая
   задача Codex.
3. `ROUTE_B_EXECUTION_STATE.json` решает текущий адрес `RB-*`, статус ожидания,
   следующий разрешённый актор и состояние очереди.
4. `docs/ROUTE_B_THEOREM_CONTRACT_v2.md` задаёт целевой theorem-DAG и реестр
   обязательств. До закрытия `PO-0` это принятый кандидат контракта, а не
   контрподписанный результат.
5. `ROUTE_B_STATE.md` хранит проверенные факты, вердикты и историю закрытых
   узлов.
6. `loop_state.json` — только compatibility mirror. Он не выбирает новый гейт.
7. `docs/INSIGHTS.md`, карта и изображения — память и объяснение, но не
   operational authority.

При конфликте о наличии работы физическая шина имеет приоритет. При конфликте
о ранге маршрута имеет приоритет глобальный оркестратор.

## Исправленная финальная цепь

```text
ExactDetectorDictionary
  + supply:
      ProjectedProlateDefectEquation
      -> Gate 6A/6B/6C (+ locked 6D)
      -> G04DefectGramBridge / node 3.3 / B* <= 25
      -> G3a
      -> DetectorBridge
      -> SafeAlphaUpper
  + parity-clean SafeGapLower
  + SafeSignAndB
  + SafeRateAssembly
      r_delta - r_alpha > 2*q_b + 1
  -> QuantitativeSafeWitness
      exists lambda_j in Lambda,
      lambda_j -> infinity,
      W'(lambda_j) -> 0
  + ZEOExportSoundness
  -> all zeros of Xi are real
  + XiRealIffRH
  -> RH
```

Здесь

```text
W'(lambda)^2 = |b(lambda)|^2 * lambda * alpha(lambda) / Delta_e(lambda),
Delta_e(lambda) = mu_3(lambda) - mu_1(lambda).
```

Если

```text
|b| <= C_b lambda^q_b,
alpha <= C_alpha lambda^r_alpha exp(-4*pi*lambda^2),
Delta_e >= c_delta lambda^r_delta exp(-4*pi*lambda^2),
```

то

```text
W' <= C lambda^[q_b + (1 + r_alpha - r_delta)/2].
```

Поэтому обязательный строгий запас —
`r_delta - r_alpha > 2*q_b + 1`. Оценка только `mu_1` не заменяет
`SafeAlphaUpper`, а утверждение только `alpha -> 0` не закрывает SAFE.

## Proof-compiler stages

Общий порядок уровней жёсткий. Внутри уровня 1 Mythos выбирает ровно один
физический bus goal после ревью; Codex порядок не придумывает.

| Stage | Contract obligations | Смысл | Текущий статус | Exit | Основной kill |
| --- | --- | --- | --- | --- | --- |
| `RB-0` | `PO-0` | Контрпроверка v2, provenance, синхронизация state/loop | `PO0_OPEN / BLOCKED_AFTER_009` | `CONTRACT_V2_LOCKED`, `STATE_LOOP_SYNCED`, `PROVENANCE_LOCKED` | current: `ZEO_EXPORT_AMBIGUOUS`, `R13_SOURCE_MISSING` |
| `RB-1` | `PO-1` | ExactDetectorDictionary: alpha, crosswalk, N-mode, gap, b | `BLOCKED_BY_RB-0` | `DETECTOR_DICTIONARY_LOCKED` | `ALPHA_OBJECT_MISMATCH`, `B_NONDEGENERACY_OPEN` |
| `RB-2` | `PO-2` | ParityLeakSourceAudit -> ParityProjectedOperatorLock | `BLOCKED_BY_RB-0` | `PARITY_INSTRUMENT_LOCKED` | `PARITY_CONTAMINATION_UNLOCALIZED`, `INSTRUMENT_NOT_CERTIFIED` |
| `RB-3` | `PO-11` | ZEOExportSoundness с точными кванторами и пределом Xi | `BLOCKED_BY_RB-0` | `ZEO_EXPORT_DERIVED` | `ROUCHE_QUANTIFIER_GAP`, `XI_LIMIT_IDENTIFICATION_GAP`, `FINITE_TO_UNIVERSAL_GAP` |
| `RB-4` | `PO-12a` | Ранний SAFE feasibility и falsifier после parity lock | `BLOCKED_BY_RB-0` | `SAFE_RATE_SHAPE_LOCKED` | `SAFE_GAP_LOWER_NO_SOURCE`, `SAFE_IS_RH_REPACKAGING` |
| `RB-5` | `PO-3` | ProjectedProlateDefectEquation со всеми источниками | `BLOCKED_BY_LEVEL_1` | `PROJECTED_DEFECT_EQUATION_DERIVED` | `SOURCE_LEDGER_INCOMPLETE`, `HOMOGENEOUS_ODE_SUBSTITUTION_FATAL` |
| `RB-6` | `PO-4..6` | Gate 6A/6B/6C; единый `X_lambda`; импорт 6D | `BLOCKED_BY_RB-5` | `GATE6_SUPPLY_LOCKED` | `G3_NORMALIZED_DEFECT_MATRIX_POLY_BOUND_FATAL` |
| `RB-7` | `PO-7..9` | Gates 3–5, node 3.3, budget 25, единый G3a ledger | `BLOCKED_BY_RB-6` | `G3A_LEDGER_LOCKED` | `RAYLEIGH_BRIDGE_NOT_DERIVED`, `BUDGET_25_EXCEEDED` |
| `RB-8` | `PO-10` | DetectorBridge, который заканчивается SafeAlphaUpper | `BLOCKED_BY_RB-7` | `SAFE_ALPHA_UPPER_DERIVED` | `DETECTOR_BRIDGE_TARGET_MISMATCH` |
| `RB-9` | `PO-12` | AlphaUpper + GapLower + SignAndB + Rate | `BLOCKED_BY_RB-8` | `QUANTITATIVE_SAFE_WITNESS` | `SAFE_IS_RH_REPACKAGING` |
| `RB-10` | `PO-13` | Lean definitions, тела теорем, export и axiom audit | `BLOCKED_BY_RB-9` | `ZERO_SORRY_ZERO_UNEXPECTED_AXIOMS` | `LEAN_EXPORT_INTERFACE_GAP`, `RH_CONDITIONAL_IMPORT` |

## Transaction discipline

Каждый математический узел проходит один и тот же цикл:

```text
1. /plan: read-only, ZERO compute, theorem shape + judges + stop codes.
2. Proshka: adversarial review, kill + weakest repair.
3. Mythos: immutable physical NNN_*.goal.md with registered predictions.
4. Codex: smallest unanswered NNN only; exactly one task.
5. Codex: matching answer with MYTHOS_PROSHKA_HANDOFF + ACTIONS LOG.
6. Sync: ROUTE_B_STATE -> ROUTE_B_EXECUTION_STATE -> loop_state mirror.
7. Verify: routeb_status.py --check; then STOP in `MANUAL_BUS`, or resume the
   first eligible master leaf in `OWNER_AUTHORIZED_AUTORUN`.
8. Mythos: HIT/MISS and, only if justified, the next physical goal.
```

`ZERO compute`, `plan-only` и `read-only` — жёсткие switches. Они запрещают
новые численные запуски, матрицы и изменение доказательных файлов.

После answer Codex не создаёт следующий физический goal и не превращает
свободный номер в математическую задачу. В `MANUAL_BUS` режиме действует STOP.
В текущем owner-authorized autorun режиме Codex продолжает по master DAG,
сохраняя один active leaf и отдельную валидацию каждого закрытия. Ни один такой
переход не повышает Route B до mainline. Commit/push — только по явной команде
пользователя.

## Transaction при изменении состояния

Смена шага считается завершённой только когда согласованы все применимые
слои:

1. физическая goal/answer пара;
2. факты и история в `ROUTE_B_STATE.md`;
3. текущий адрес в `ROUTE_B_EXECUTION_STATE.json`;
4. compatibility-поля в `loop_state.json`;
5. request-local `IMPLEMENTATION_PLAN.md`;
6. `python3 routeb_status.py --check` возвращает `0`.

Если новая goal/answer пара есть, а mirrors отстают, код состояния —
`CONTROL_PLANE_DRIFT`; он не отменяет физическую очередь, но требует
синхронизации в рамках текущего goal.

## Уже импортированные факты

- Bus `001..009` закрыт физическими парами; `010` — только свободный номер,
  физического goal нет.
- Bus 007: `MIDPOINT_POLE_LEDGER_REPAIR`, exact relative closure
  `2.21795886424e-89`, `C_mid` и `C_pole` присутствуют точно.
- Bus 008: G1 `CONTRACT_V2_LOCKED`, G2 `STATE_LOOP_SYNCED`, G3
  `ZEO_EXPORT_AMBIGUOUS`; подстатус `R13_SOURCE_MISSING`. Поэтому `PO-0`
  остаётся открыт и уровень 1 не выбран.
- Bus 009: negative answer `OVERCLAIM_LIST / MYTHOS_REPAIRS_PRESENT /
  OPEN_CRITICAL_ZEO_EXPORT_AMBIGUOUS / PLANT_INERT`; транзакция закрыта, но
  `PO-0` и ZEO не закрыты математически.
- `C_left` и `C_right` отсутствуют в текущем identity; нового second-edge
  channel нет.
- Route B остаётся `NOT_RH`.
- Самая вероятная математическая стена — безусловный `SafeGapLower`; это
  диагноз, не теорема и не route-kill.

## Запрещённые ложные старты

- Не исполнять старый request `node.md`: он архивный diagnostic spec.
- Не читать статическую таблицу старой очереди как operational truth.
- Не начинать `ProjectedProlateDefectEquation`, пока уровни 0 и 1 не закрыты.
- Не использовать parity-contaminated `W'`, gap или `rGap13` как доказательство.
- Не подменять `alpha` величиной `mu_1`.
- Не занимать универсальный квантор finite fit, сеткой или одним anchor.
- Не использовать RH-conditional статистику нулей в заключительной цепи.

## Связанные файлы

- `ROUTE_B_EXECUTION_STATE.json` — текущий машинный адрес.
- `IMPLEMENTATION_PLAN.md` — ровно одна request-local задача.
- `routeb_status.py` — read-only status/drift check.
- `ROUTE_B_STATE.md` — факты и история.
- `bus/BUS_PROTOCOL.md` — роли и файловая очередь.
- `docs/ROUTE_B_THEOREM_CONTRACT_v2.md` — theorem contract.
- `docs/ROUTE_B_DETECTOR_RH_CLOSURE_MAP_2026-07-10.md` — объясняющая карта.
