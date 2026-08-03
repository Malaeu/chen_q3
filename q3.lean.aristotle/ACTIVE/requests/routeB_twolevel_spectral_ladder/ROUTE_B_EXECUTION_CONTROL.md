# Route B — execution control

Status: `IDLE_AWAITING_EXPLICIT_PROSHKA_MATHEMATICAL_TARGET / CONTROL_PLANE / NOT_RH / CHALLENGER`
Schema: `route_b_execution_control.v2`
Canonical repo: `/Users/emalam/GitHub/rh_lean_01_2026`
Current address: `RB-IDLE / RB-IDLE-CONTROL / NoSelectedMathematicalTarget`

## Post-D0 closeout control — 2026-08-03

Proshka, under the human owner's direct delegation, authorized exactly one
docs/control-plane transaction. It terminally closed the exhausted source-locked
D0.7e.5a branch, preserved the independent finite facts and generic Lean
receivers, and repointed the non-mint CCM package to conditional G3/H2b
evidence with classification:

```text
SOURCE_PARTIAL_NEIGHBORING_DETERMINANT_ONLY
```

The route is now idle. `RB-IDLE-CONTROL` is a validator sentinel only; it is
not a theorem or selected mathematical front. The next action requires a
separate Proshka decision selecting exactly one of G2, G3, G5, or G6. G3 is
the strongest candidate after closeout but is not selected here. Goal 051/M1
is not implicitly authorized.

Current scheduling rule:

```text
physical unanswered bus goal exists -> execute the smallest NNN first
no physical unanswered goal          -> remain RB-IDLE-CONTROL
separate Proshka target arrives       -> execute only that bounded target
no separate target                    -> do not begin mathematics
```

Bus 009's historical verdict, ZEO ambiguity, and missing rGap13 provenance
remain historical/open facts. The closeout does not close H2b, G3, PO-0, S1,
or S2. Route B stays `CHALLENGER / NOT_RH`.

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
CURRENT: RB-IDLE / RB-IDLE-CONTROL / NoSelectedMathematicalTarget
CONTRACT: v2 historical candidate; no mathematical front selected
BUS: 001..009 closed; active physical goal NONE; next free number 010
MODE: IDLE_AWAITING_EXPLICIT_PROSHKA_MATHEMATICAL_TARGET
D0: terminal historical; D0_7E_WPRIME_CONSUMER_MISSING retained only as history
CCM: SOURCE_PARTIAL_NEIGHBORING_DETERMINANT_ONLY -> G3/H2b conditional evidence
NEXT: Proshka selects exactly one of G2/G3/G5/G6 in a separate transaction
GUARDS: Goal 051 not implicitly authorized; Bus 010 VOID; no promotion; NOT_RH
```

## Active direct protocol

1. Proshka selects exactly one bounded mathematical target.
2. Codex checks the source/interface prerequisites for that target.
3. Codex executes and validates only the authorized target.
4. No Mythos handoff is required in this direct loop.
5. No Bus 010, route promotion, or RH claim follows from selection or closure.

## Terminal history — former D0/WPrime control (non-executable)

Everything below this heading is retained for provenance and historical
architecture only. It must not be read as the current address, next action,
live dependency, or selected consumer.

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
The immutable owner input now supplies a finite dependent definition:
`bDet_(m,N)=Fhat_(m,N)(0)/Xi(0)=sqrt(L_m)c0/zeta(1/2)` on `TrialNonzero`.
The audit locks `Fplus(z)=T_m(k1)(-z)`, proves `zeta(1/2)<0` by the eta series,
and defines `G=Fhat/bDet` only on `BDetNonzero`. The unspecified
`N(lambda)=ceil(kappa*lambda^2)` schedule is not accepted.

The remaining crosswalk is now canonically decomposed by the physically
ratified R1--R5. Its active D0.7e.5a audit proves that the exact
dependent locus is
`CentralValueNonzero=BDetNonzero=FhatAtZeroNonzero=BCalNonzero`. On that locus
the central-value normalizing multiplier is
`bZeoMul=Xi(0)/Fhat(0)=bCal^(-1)`, so `G=bZeoMul*Fhat`. `TrialNonzero` does not
imply central nonvanishing.

The completed T0 corpus scan found no independent `FZeo` or `WPrime` consumer.
The historical `W'` row is a target/sketch or diagnostic, while the
physical Option-B ruling defines the desired right-hand side and cannot serve
as the independent consumer required by the latest review. The nested subtree
is canonical, its structural exit is `D0_7E_5_DECOMPOSITION_LOCKED`, and the
canonical active leaf is `D0.7e.5a`. Operational pause is
`OWNER_AUTHORIZED_AUTORUN_PAUSED_D0_7E_5A_WPRIME_CONSUMER_SOURCE_GAP`, with
mathematical stop `D0_7E_WPRIME_CONSUMER_MISSING`; the WPrime `b` orientation
is unpinned. The owner standing order is active, but it cannot ratify an absent
candidate; its no-new-definition limit is still binding.

The owner-launched no-stop sprint then closed `D0.7e.5b` only as an
uninstantiated interface typecheck and `D0.7e.5d` only as exact wording/address
migration. The required `(17,120)` coefficient vector is absent, so T1 is
partial; T2 is `H3E_T2_PINNED_INPUT_SET_INCOMPLETE`. Lean now proves finite
`bDet` reality and `Fplus(0)=sqrt(L)c0`; `zeta_half_ne_zero` remains blocked by
the missing eta-continuation bridge. None of this closes 5a, 5c, H3e, or a
parent.

R2 registers `H3e ExactWPrimeTrackingTheorem` as OPEN/INACTIVE and leaves PO-10
unchanged. R3 locks only the Contract-v2 direct `q_b` convention, not the
FIT_NOT_LAW exponent value. R4 retains independent `(m,N)`. R5 records H0/A1
as alpha's unique home, but `PO-1/A1` and `PO_XWALK_UNIFORM_EVAL` remain
OPEN_CRITICAL external obligations. No H3/H4 theorem was imported into D0.
No H3c/H4 import occurred. The finite calibration does not close D0.7 or prove
RH.

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
