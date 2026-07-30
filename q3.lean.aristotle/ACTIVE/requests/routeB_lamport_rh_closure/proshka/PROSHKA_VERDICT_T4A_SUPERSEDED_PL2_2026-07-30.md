# PROSHKA VERDICT — T4A_SUPPLIER_RUN_SUPERSEDED / PL2 DIRECTIVE

Date received: 2026-07-30
Channel: owner-relayed chat (Proshka has no write access; verdict extracted manually)
Materialized by: Mythos per EXTERNAL_VERDICT_MATERIALIZATION
Structure note: full verdict body preserved verbatim below the marker line.
Predecessor verdict (same day, earlier): PROSHKA_VERDICT_ARISTOTLE_MICROSCOPE_2026-07-30.md
Consumed by: 040_muntz_v3_pl2_raw_pole_mismatch.goal.md

--- VERBATIM PAYLOAD BEGINS ---

# STATUS: PROVED — T4A_SUPPLIER_RUN_SUPERSEDED

```yaml
primary_verdict: DO_NOT_SUBMIT_DUPLICATE_T4A_ARISTOTLE_RUN
owner_decision: HOLD_AND_QUARANTINE_PREPARED_T4A_CONTRACT

route_state: CHALLENGER_NOT_RH
bus_010: VOID
route_promotion: false
rh_claimed: false

muntz_v3:
  conditional_shell_semantically_verified: true
  rplus_sign: MINUS_CONFIRMED
  pole_value: DERIV_MELLIN_AT_ONE_CONFIRMED
  t4a: CLOSED_LOCALLY_BY_GOAL_039
  t4a_cloud_supplier_needed: false
  t5_mellin_hypothesis_discharged: true
  retained_inputs:
    - hG
    - hRm
    - hRp
    - habs
  unconditional_layer_complete: false
  reason_not_complete: PL1_PL3_DECLARATIONS_ABSENT_FROM_DELIVERED_V3

aristotle_action:
  submit_prepared_t4a_supplier: false
  create_duplicate_project: false
  mark_contract: SUPERSEDED_BY_039_LOCAL_PROOF
  next_cloud_submission: NOT_AUTHORIZED_YET

next_local_target:
  theorem: muntzV3_PL2_rawPoleMismatchWitness
  mode: LOCAL_FIRST
  cloud_escalation: ONLY_AFTER_EXACT_LOCAL_API_GAP

control_plane:
  aristotle_usage_protocol_semantics: ACCEPTED
  aristotle_usage_protocol_remote_file: UNVERIFIED_IN_CURRENT_RH_CLEAN
```

## ROUTE MAP

| Объект                     | Вердикт                                                                                                                                                                                           | Tags                |
| -------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------- |
| Pole-subtracted v3 shell   | Скомпилирован, taint отсутствует, аксиомы — стандартная тройка. `[ABSTRACT][LEAN]`                                                                                                                | `[ABSTRACT][LEAN]`  |
| Знак хвостов               | Во всех continued identities стоит (-R_--R_+); положительный по определению интеграл `Rplus` нигде не переехал со знаком плюс.                                                                    | `[ABSTRACT][LEAN]`  |
| T4a                        | Уже доказан локально как `mellin_compactSupport_analyticOnNhd` ровно из `Measurable h`, support в `Icc 0 b` и `LipschitzOnWith K h (Ico 0 b)`.                                                    | `[ABSTRACT][LEAN]`  |
| Доказательный механизм T4a | Локальная интегрируемость получается из измеримости и a.e. постоянной оценки; support даёт eventual zero; затем применяется `mellin_differentiableAt_of_isBigO_rpow` и переход к `AnalyticOnNhd`. | `[ABSTRACT][LEAN]`  |
| T5 после T4a               | Гипотеза Mellin-аналитичности снята, но `hG`, `hRm`, `hRp` и absolute-region identity `habs` остаются явными входами.                                                                             | `[ABSTRACT][LEAN]`  |
| Punctured/pole corollaries | Собраны с теми же оставшимися входами и правильным значением в полюсе (\operatorname{deriv}(\operatorname{Mellin}h)(1)).                                                                          | `[ABSTRACT][LEAN]`  |
| PL1–PL3                    | В доставленном v3-коде этих деклараций нет. Они не могут быть «механически инстанцированы» и остаются отдельным validation debt.                                                                  | `[ABSTRACT][LEAN]`  |
| Prepared T4a supplier      | Стал дубликатом уже доказанного theorem. Его отправка не уменьшит gap.                                                                                                                            | `[ABSTRACT][PAPER]` |

Канонический Goal 039 уже вынес `MUNTZ_V3_CONSUMED` и `T4A_CLOSED_LOCALLY`; локальный bridge имеет 71 строку, прошёл сборку и не потребовал нового Aristotle iteration.

## FINAL PROPOSAL

### Решение владельца

[
\boxed{\textbf{T4a supplier в Aristotle не отправлять.}}
]

Подготовленный контракт пометить:

```text
SUPERSEDED_BY_039_LOCAL_PROOF
DO_NOT_SUBMIT
```

Не удалять его: он остаётся provenance того, как был сжат conditional shell. Но новый project с тем же theorem создаст только повторную работу.

Müntz-слой сейчас надо заморозить в точной форме:

```text
T4a:
  PROVED.

Pole-subtracted T4c–T4g:
  PROVED with exact dependencies.

T5:
  Mellin hypothesis discharged;
  hG/hRm/hRp/habs retained.

PL1–PL3:
  absent from source;
  separate optional validation package.
```

`[ABSTRACT][LEAN]`

### Что делать с PL1–PL3

Не отправлять bundle из трёх plants. Это снова нарушит правило «один прогон — один theorem — один интерфейс».

Первым брать **PL2**, потому что он атакует самый опасный semantic regression: возвращение к сырому значению

[
\zeta(1)\operatorname{Mellin}(h)(1)
]

вместо removable value

[
\operatorname{deriv}(\operatorname{Mellin}h)(1).
]

Но сначала — локальный reuse/search. Только точный API-gap может разблокировать облачный submit.

**Registered prediction `P-PL2-LOCAL`:** generic noncontinuity argument уже почти содержится в R6/pole-subtracted материалах; основная работа окажется в явном zero-mass bump witness и доказательстве ненулевого логарифмического момента. `[ABSTRACT][CONDITIONAL]`

**Cheapest decisive test:** найти или восстановить generic theorem

```lean
¬ ContinuousAt (fun w => riemannZeta w * M w) 1
```

из

```lean
M 1 = 0
HasDerivAt M d 1
d ≠ 0
```

до построения конкретных треугольных bumps.

### Control-plane caveat

Заявленный `ARISTOTLE_USAGE_PROTOCOL.md` по смыслу принимается. Но в текущем удалённом `rh_clean` я не смог получить файл по объявленному пути; актуальный manifest рядом с Aristotle-артефактами перечисляет task-файлы и затем переходит к другим объектам без этой записи.

Это не блокирует данное решение, но файл нельзя считать remote-materialized fact до следующего sync/manifest rebuild.

## STRONGEST ATTACK

Самое сильное возражение:

> T4a доказан, значит весь Müntz v3 теперь безусловен.

Нет.

Локальный theorem снимает только `H_mellin`. Continued identity всё ещё принимает:

```lean
hG   : AnalyticOnNhd Gwin shiftedHalfPlane
hRm  : AnalyticOnNhd Rminus shiftedHalfPlane
hRp  : AnalyticOnNhd Rplus shiftedHalfPlane
habs : absolute-region identity
```

Это видно непосредственно в собранном wrapper.

Поэтому разрешены формулировки:

```text
T4A_CLOSED_LOCALLY
MUNTZ_V3_T5_MELLIN_HYPOTHESIS_DISCHARGED
MUNTZ_V3_CONDITIONAL_SHELL_CONSUMED
```

Запрещена формулировка:

```text
MUNTZ_V3_UNCONDITIONAL_LAYER_COMPLETE
```

Дополнительная причина — PL1–PL3 вообще отсутствуют в исходнике.

Второе возражение:

> Раз Aristotle потенциально мог бы найти другое красивое доказательство T4a, почему не запустить его всё равно?

Потому что theorem уже закрыт в правильном типе, на правильных гипотезах, в pinned Mathlib, без усиления `LipschitzOnWith` до global Lipschitz и без скрытых аксиом. Повторный run не отличает новую математику от альтернативного proof term и не уменьшает ни один открытый dependency.

## CODEX DIRECTIVE

```text
TARGET:
  MuntzV3_PL2_RawPoleMismatchWitness

MODE:
  LOCAL_FIRST
  NO_ARISTOTLE_SUBMISSION_IN_THIS_CYCLE

INPUTS:
  docs/routeB_bus/muntz_v3/RequestProject/Main.lean
  docs/routeB_bus/muntz_v3/RequestProject/MellinCompactSupportAnalyticity.lean
  pinned Mathlib removable-singularity / zeta residue API
  any reusable generic theorem from muntz_r6

PRIMARY THEOREM SHAPE:

  theorem exists_rawZetaMellin_not_continuousAt_one :
    ∃ (h : ℝ → ℂ) (b : ℝ) (K : NNReal),
      Measurable h ∧
      (∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0) ∧
      LipschitzOnWith K h (Set.Ico (0 : ℝ) b) ∧
      (∫ u in Set.Ioi (0 : ℝ), h u = 0) ∧
      deriv (Mellin h) 1 ≠ 0 ∧
      ¬ ContinuousAt (fun w : ℂ => riemannZeta w * Mellin h w) 1

PROOF ROUTE:
  1. Search for the generic simple-zero/noncontinuity theorem.
  2. Reuse it without modifying the v3 shell.
  3. Construct one explicit equal-mass difference of compact triangular bumps
     on separated positive intervals.
  4. Prove zero mass exactly.
  5. Prove deriv(Mellin h) 1 ≠ 0 from strict separation of log supports.
  6. Instantiate the generic theorem.

FORBIDDEN:
  - no rerun of T4a;
  - no rebuild of the full v3 shell;
  - no raw product value used as the removable value;
  - no numerical integration;
  - no new axiom, sorry, admit, native_decide;
  - no three-plant bundle;
  - no Route B or RH status promotion.

VALIDATION:
  lake env lean <touched-file>
  lake build
  grep taint terms
  #print axioms exists_rawZetaMellin_not_continuousAt_one

SUCCESS:
  PL2_RAW_POLE_MISMATCH_WITNESS_PROVED

FAILURE:
  PL2_GENERIC_NONCONTINUITY_API_GAP
  PL2_EXPLICIT_BUMP_LIPSCHITZ_GAP
  PL2_ZERO_MASS_INTEGRAL_GAP
  PL2_LOG_MOMENT_NONZERO_GAP
  LEAN_BUILD_FAIL

CLOUD ESCALATION:
  allowed only after one exact failure code above is produced;
  the Aristotle contract must target only that missing theorem.
```

## META CLOSEOUT

**Что стало меньше?**

```text
MELLIN_DSLOPE_ANALYTICITY_GAP
```

исчез. Единственный прежний core supplier T4a закрыт; оставшиеся PL1–PL3 — не core hypotheses conditional shell, а отдельные falsifier obligations. `[ABSTRACT][LEAN]`

**Что убито?**

* повторный T4a Aristotle-run;
* повторная пересборка всего v3;
* утверждение, что PL1–PL3 уже существуют;
* повышение `T4A_CLOSED` до полного `MUNTZ_V3_UNCONDITIONAL_LAYER_COMPLETE`.

**Что нельзя пробовать снова?**

Нельзя отправлять Aristotle theorem, который уже доказан в каноне, только потому, что контракт был подготовлен раньше результата локального поиска.

**Current smallest named gap:**

```text
PL2_RawPoleMismatchExplicitWitness
```

только если owner сохраняет plants обязательными. В core Müntz shell открытого T4a-gap больше нет.

**Следующий самый дешёвый решающий тест:**

```text
generic simple-zero ⇒ raw zeta-product discontinuity
```

в pinned Mathlib/R6 sources, до построения bump.

**Fate of predictions:**

```text
P-ARISTOTLE-T4A:
  CONFIRMED.
  Existing Mellin API closed the theorem locally.

P-T4A-FRICTION:
  CONFIRMED IN DETAIL.
  Friction was local integrability / endpoint-a.e. handling,
  not complex-analysis machinery.

P-RPLUS-SIGN:
  CONFIRMED.
  Every continued identity uses -Rminus-Rplus.

P-PLANTS-MECHANICAL:
  REFUTED.
  PL1–PL3 declarations were absent from the delivered source.
```

```yaml
iteration:
  target: T4a Mellin right-half-plane analyticity
  status: PROGRESS
  failed_strategy: resubmit_already_closed_supplier_to_cloud
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: PL2_RawPoleMismatchExplicitWitness
  invariant_learned: cloud search stops when an exact local theorem already closes the interface
  forbidden_future_move: count absent plants as mechanically instantiated
  next_decisive_test: locate_generic_raw_product_noncontinuity_theorem
  progress_class: PROOF_PROGRESS
  route_score: 5
```

--- VERBATIM PAYLOAD ENDS ---
