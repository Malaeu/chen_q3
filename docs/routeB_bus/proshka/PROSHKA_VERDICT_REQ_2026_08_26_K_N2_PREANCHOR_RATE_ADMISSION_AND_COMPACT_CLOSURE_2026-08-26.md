# STATUS: PROVED — PRE-ANCHOR SOURCE-SCALED N2 RATE SEMANTICALLY ADMITTED; SELECTED-SHELL COMPACT CLOSURE IS THE ONLY NEXT TRANSACTION
```yaml
PRIMARY: ADMIT_GOAL058_SELECTED_FERRERS_N2_PREANCHOR_SOURCE_SCALED_TAIL_RATE
PRIMARY_COUNT: 1

QUEUE:
  QUEUE_REQ_ID: REQ-2026-08-26-K
  QUEUE_REQ_ID_PROVENANCE: JUDGE_ASSIGNED_TO_EXECUTION_FOLLOWUP_OF_REQ_2026_08_26_J
  SOURCE_QUEUE: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_STATUS_MUTATED: false
  STALE_OPEN_ENTRY_OBSERVED: REQ-2026-08-21-P_HAS_PRIOR_VERDICT_AND_IS_NOT_REANSWERED

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  HEAD: 97160f17e4bd257e529256711bb0838f470bbae0
  HEAD_IS_ORIGIN_RH_CLEAN_AT_AUDIT: true
  PARENT_VERDICT_COMMIT: 106074d48eb93c5ebbbab7a5b820ea116e96e871
  EXECUTION_COMMIT: 97160f17e4bd257e529256711bb0838f470bbae0
  COMMIT_DELTA:
    commits: 1
    added_files: 2
    modified_files: 1
    deleted_files: 0
  W5_APPEND_ONLY_AUDIT:
    additions: 39
    deletions: 0
    existing_declaration_changed: false

ARTIFACTS:
  source_record:
    path: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_N2_PREANCHOR_SCALED_TAIL_RATE_2026-08-26.md
    git_blob: 62e2cf51bf13d839b61ee97188048163940c95c0
    reported_sha256: absent_for_source_record
  lean_1:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5RateAssembly.lean
    git_blob: 6f00ac6dab94b0804ec6e22766fc5990617972a1
    reported_sha256: 767f446afef22171d35f02d35ba5f9bc7894746cd58171eb1b95506a227890cb
    change: APPEND_ONLY_PUBLIC_EXPORT_WRAPPER
  lean_2:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersN2SourceScaledTailRate.lean
    git_blob: 3b2f5f309b0a7ea0aa53e465afee19f18ff40271
    reported_sha256: 8ed297d015bbf4873ec371272665a057b1041720fc2b5c729ecaf9b7beb498a3
    change: NEW_FILE

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN_W5: PASS_EXIT_0
  LINUX_REPORTED_LAKE_BUILD_W5: PASS
  LINUX_REPORTED_Q3_CHECK_W5: PASS
  LINUX_REPORTED_LAKE_ENV_LEAN_N2: PASS_EXIT_0
  LINUX_REPORTED_LAKE_BUILD_N2: PASS
  LINUX_REPORTED_Q3_CHECK_N2: PASS
  LINUX_REPORTED_HOLE_SCAN: PASS
  LINUX_REPORTED_AXIOMS:
    selectedFerrersAbelFourierDecayBudget_rate_of_modeChiThetaRates:
      - propext
      - Classical.choice
      - Quot.sound
    selectedFerrersPreAnchorSourceScaledMellinProjectionTailRate:
      - propext
      - Classical.choice
      - Quot.sound
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_LAKE_BUILD: false
  JUDGE_RERAN_Q3_CHECK: false

RECEIPT_AUDIT:
  SOURCE_RECORD_STARTS_WITH_REQUIRED_YAML: false
  SOURCE_RECORD_COMMIT_FIELD_IS_ACTUAL_SHA: false
  SOURCE_RECORD_CONTAINS_OWN_BLOB_FIELD: false
  LEAN_GIT_BLOBS_PRESENT: true
  LEAN_SHA256_VALUES_REPORTED: true
  CLASSIFICATION: NONFATAL_PROCESS_NONCONFORMITY
  REPAIR_POLICY: VERDICT_SUPPLIES_ACTUAL_COMMIT_AND_GIT_BLOBS_APPEND_ONLY

PUBLIC_SURFACE:
  theorem_1:
    name: selectedFerrersAbelFourierDecayBudget_rate_of_modeChiThetaRates
    role: PUBLIC_EXPORT_OF_EXISTING_ETW13_RATE
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  theorem_2:
    name: selectedFerrersPreAnchorSourceScaledMellinProjectionTailRate
    role: SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN

SEMANTIC_ADMISSION:
  status: SEMANTICALLY_ADMITTED_AS_EXACT_CONDITIONAL_COFINAL_SUPPLIER
  exact_carrier: SELECTED_FERRERS_PREANCHOR_SCHEDULE_M_EQ_N_EQ_K_PLUS_2
  exact_trial: PROLATE_COMBINATION_OF_SELECTED_FERRERS_PREANCHOR_PAIR
  exact_scale: SELECTED_FERRERS_LEMMA73_SOURCE_SCALE
  exact_residual: UNNORMALIZED_GALERKIN_PROJECTION_MINUS_FULL_TRIAL
  scaled_object_identity: SOURCE_SCALE_TIMES_PROJECTION_RESIDUAL_EQUALS_PROJECTION_RESIDUAL_OF_SELECTED_FERRERS_ESTAR_HM
  norm_taken_before_object_identity: false
  old_all_index_S_used: false
  hFamily_used: false
  selectedTrialNormalizer_used: false
  sourceScale_upper_bound_used: false
  inverse_sourceScale_bound_used: false
  subsequence_added: false
  free_compact_rate_premise_added: false
  sigma_endpoint_claimed: false
  new_analytic_input: none

RATE_LEDGER:
  schedule:
    m_k: k_plus_2
    N_k: k_plus_2
    lambda_k: sqrt_k_plus_2
    L_k: log_k_plus_2
  coefficient_constant:
    shape: AF_times_k_plus_2_to_one_quarter_times_sqrt_log_plus_two_plus_Cp_div_four_pi
  exact_tail_square_upper:
    shape: four_times_Ak_squared_times_Lk_div_k_plus_3
  closed_substrip_kernel_envelope:
    shape: sqrt_Lk_times_lambda_k_to_sigma
  weighted_square_majorant:
    shape: constant_times_log_k_plus_two_cubed_div_k_plus_two_to_one_half_minus_sigma
  vanishing_range:
    lower: zero_le_sigma
    upper: sigma_strictly_less_than_one_half
  sigma_equal_one_half: NOT_PROVED_AND_CURRENT_MAJORANT_DOES_NOT_VANISH

CLAIM_LEDGER:
  claim_1:
    statement: exact source scale commutes through the literal Galerkin projection before norms
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  claim_2:
    statement: two_sided_omitted_mode_Parseval_tail_has_upper_bound_four_over_N_plus_one
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  claim_3:
    statement: source_scaled_residual_times_closed_substrip_Mellin_envelope_tends_to_zero
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  claim_4:
    statement: SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE_is_closed
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN

FRONT_STATUS:
  N2_0_SELECTED_SHELL_RESIDUAL_OBJECT_LOCK: OPEN_AS_ASSEMBLY_API
  N2_1_ANCHORED_MAIN_LIMIT: EXISTING_COMPONENTS_READY
  N2_2_CENTER_NORMALIZER_CANCELLATION: PAPER_EXACT_SELECTED_SHELL_LEAN_ASSEMBLY_OPEN
  N2_3_COMPACT_MELLIN_KERNEL_ENVELOPE: PAPER_READY_LEAN_ASSEMBLY_OPEN
  N2_4_SOURCE_FOURIER_TAIL_BOUND: CLOSED_INSIDE_ADMITTED_RATE_THEOREM
  N2_5_SCALE_ENERGY_SCHEDULE_BUDGET: CLOSED
  N2_6_COMPACT_DECAY_ASSEMBLY: OPEN
  N3_SAME_FAMILY_LIMIT_ASSEMBLY: OPEN_AS_COROLLARY_AFTER_N2
  N4_SLOT_S2_ASSEMBLY: OPEN_AS_COROLLARY_AFTER_N3
  SLOT_H2A_SIMPLE_EVEN_GROUND: OPEN_SEPARATE_FRONT
  THEOREM510_REAL_ZERO_BRIDGE: OPEN_SEPARATE_FRONT
  ROUTE_PROMOTION: false
  RH_CLAIM: false

STRONGEST_REMAINING_ATTACK:
  code: PREANCHOR_RAW_SCHEDULE_VS_SELECTED_TAIL_SHELL_API_SEAM
  statement: >-
    The admitted rate is indexed by the literal pre-anchor schedule, while the
    terminal SelectedProlateCofinalSourceData is a theorem-generated finite-prefix
    deletion whose shift is currently private.  The next theorem must expose one
    cofinal reindex receipt and rewrite the exact index, pair and source scale.
  mathematical_wall: false
  type_and_api_wall: true
  cards:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT

CLOSES:
  - SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE
OPENS: []

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_N2_COMPACT_DECAY_ASSEMBLY
  MODE: ONE_GOAL_ONE_COMMIT
  PRIMARY_TARGET: SELECTED_FERRERS_SOURCE_SCALED_MELLIN_COMPACT_DECAY
  ALLOWED_EXTRA_COROLLARIES:
    - SELECTED_FERRERS_SAME_FAMILY_LOCALLY_UNIFORM_LIMIT
    - SELECTED_FERRERS_SLOT_S2
  NEW_ANALYTIC_INPUT_EXPECTED: none
  LEAN_FILES:
    append_only_export:
      path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
      role: EXPOSE_COFINAL_FINITE_PREFIX_REINDEX_RECEIPT
    new_file:
      path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersN2CompactDecayAssembly.lean
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_N2_COMPACT_DECAY_ASSEMBLY_2026-08-26.md
  REQUIRED_PUBLIC_SURFACE:
    - selectedProlateCofinalSourceDataOfPreAnchorPort_exists_cofinal_reindex
    - selectedFerrersCofinalCenteredFinite_sub_anchoredMuntz_tendsto_zero_of_modeChiThetaRates
    - selectedFerrersCofinalCenteredPstar_tendsto_centeredXi_of_modeChiThetaRates
    - selectedFerrersCofinalSlotS2_of_modeChiThetaRates
  SUCCESS_CODE: SELECTED_FERRERS_N2_N3_N4_COMPACT_CLOSURE_LEAN
  FAILURE_CODE: GOAL058_N2_SELECTED_SHELL_TAIL_REINDEX_OR_CENTERED_MELLIN_ASSEMBLY_GAP

NEXT_TRANSACTION_CONTRACT:
  reindex_receipt_must_export:
    - one_shift_function
    - shift_tendsto_atTop
    - exact_index_equality
    - exact_pair_equality
    - exact_sourceScale_equality
  compact_kernel_bound:
    domain: every_compact_subset_of_centeredCriticalStrip
    method: compact_contained_in_one_closed_substrip_plus_Cauchy_Schwarz_on_exact_dStar_window
  exact_center_identity:
    raw_zero: raw_k_zero_equals_trial_normalizer_times_Gwin_k_zero
    cancellation: trial_normalizer_cancels_before_inequality
    centered_error: Xi_zero_div_Gwin_zero_times_Mellin_of_projection_residual
  anchored_ratio:
    input: sourceScale_times_Gwin_zero_tends_to_centeredXi_zero_nonzero
    output: centeredXi_zero_div_sourceScale_times_Gwin_zero_tends_to_one
  final_composition:
    - source_scaled_residual_compact_decay
    - anchored_ratio_tends_to_one
    - selected_Muntz_approximation_tends_to_centeredXi
    - centeredPstar_tends_to_centeredXi
    - SlotS2_with_c_equal_one_and_gamma_equal_one

FORBIDDEN:
  - use_old_ProlateCanonicalSourceData_S_plus_hFamily
  - retain_selectedTrialNormalizerBounded_as_N2_input
  - infer_compact_open_decay_from_bare_L2_decay
  - add_free_compact_rate_premise
  - select_new_subsequence
  - claim_sigma_equal_one_half
  - mutate_selected_shell_schedule_or_constructor
  - reopen_W5_edge_band_top_or_seam_analysis
  - confuse_projection_tail_with_ground_state_tracking
  - claim_H2a_or_Theorem510_or_RH

PREDICTION_FATES:
  P_N2_LEAN_1:
    prior_probability: 0.86
    fate: CONFIRMED
  P_N2_ASSEMBLY_1:
    prior_probability: 0.89
    fate: LIVE_NOT_YET_TESTED
    no_retroactive_repair: true
    note: exact_private_tail_reindex_API_seam_is_packaging_not_new_analysis

NEW_PREDICTIONS:
  P_N2_COMPACT_ASSEMBLY_LEAN_1:
    probability: 0.84
    prediction: selected_shell_compact_decay_closes_after_one_public_reindex_receipt_without_new_analytic_input
  P_N2_SLOT_S2_COROLLARY_1:
    probability: 0.96
    prediction: once_centeredPstar_tends_locally_uniformly_to_centeredXi_the_existing_SlotS2_is_immediate_with_c_one_gamma_one

ARSENAL_MANDATE: ACCEPTED_CURRENT_DECK
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: LEAN_REPORTED_NOT_JUDGE_RERUN
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

Коммит `97160f17e4bd257e529256711bb0838f470bbae0` реализует ровно разрешённую транзакцию. В W5-файл добавлен один публичный wrapper; существующие declarations и proof bodies не изменены. Новый файл доказывает rate на буквальном pre-anchor Ferrers-объекте и не возвращает старый `S + hFamily` scaffold.

Главное объектное тождество доказано до взятия нормы:

\[
 a_k\,(P_kg_k-g_k)=P_kE_k-E_k,
\]

где \(a_k\) — точный source scale, \(g_k\) — unscaled pre-anchor trial, а \(E_k\) — буквальный `selectedFerrersEStarHm`. Поэтому source scale не оценивается сверху и снизу: он исчезает через линейность проекции, а не через две независимые мажоранты.

Parseval и точный двусторонний хвост дают

\[
 \|P_kE_k-E_k\|^2
 \le 4A_k^2\frac{L_k}{k+3}.
\]

После умножения на квадрат Mellin-envelope

\[
 L_k\lambda_k^{2\sigma}
 =\log(k+2)(k+2)^\sigma
\]

получается мажоранта

\[
 C\frac{(\log(k+2)+2)^3}{(k+2)^{1/2-\sigma}},
\]

которая стремится к нулю ровно при каждом фиксированном \(0\le\sigma<1/2\). Endpoint \(\sigma=1/2\) не занят.

Это закрывает N2.5 — substantive moving-window rate wall. Полная locally uniform compact decay пока не заявляется: для неё ещё надо собрать selected-shell residual coordinate, exact center cancellation, compact-substrip envelope и finite-prefix tail reindex в одном theorem.

## FINAL PROPOSAL

Выполнить ровно одну следующую транзакцию:

```text
GOAL058_SELECTED_FERRERS_N2_COMPACT_DECAY_ASSEMBLY
```

Сначала append-only экспортировать public cofinal reindex receipt из generic pre-anchor shell constructor. Затем в одном новом файле:

1. определить буквальный Mellин-координатный residual выбранного tail shell;
2. доказать точное тождество centered finite-minus-anchored main;
3. применить Cauchy–Schwarz на exact `dStar`-окне и admitted rate после cofinal reindex;
4. получить locally uniform decay на каждом compact;
5. сложить с уже существующим `muntzApproximation_tendsto_centeredXi`;
6. вывести `centeredPstar -> centeredXi`;
7. закрыть `SlotS2` с \(c=1\), γ=1.

Новых аналитических suppliers нет.

## STRONGEST ATTACK

Самый сильный риск теперь не rate. Он типовой: текущая rate-теорема живёт до конечного удаления prefix, а terminal shell — после него. Private shift нельзя заменить словами «finite prefix harmless». Нужен публичный theorem, который предъявляет один cofinal shift и точные equalities всех source fields. Иначе это снова C04: одинаковая асимптотическая история, но недоказанное равенство объектов.

Второй риск — попытка взять bare L2 decay и назвать его compact convergence. Это уже убито counterexample-plant старого N2 verdict. Compact kernel amplification должен остаться явным до финального `TendstoUniformlyOn`.

## CODEX DIRECTIVE

```text
TASK_ID:
  GOAL058_SELECTED_FERRERS_N2_COMPACT_DECAY_ASSEMBLY

MODE:
  ONE_GOAL_ONE_COMMIT

CREATE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
    G6N1SelectedFerrersN2CompactDecayAssembly.lean

APPEND_ONLY_EXPORT:
  q3.lean.aristotle/Q3/Proofs/RouteB/
    G6N1PreAnchorLimitZeroModeAndSelectedShell.lean

SOURCE_RECORD:
  docs/routeB_bus/
    LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_N2_COMPACT_DECAY_ASSEMBLY_2026-08-26.md

PUBLIC THEOREMS:
  selectedProlateCofinalSourceDataOfPreAnchorPort_exists_cofinal_reindex
  selectedFerrersCofinalCenteredFinite_sub_anchoredMuntz_tendsto_zero_of_modeChiThetaRates
  selectedFerrersCofinalCenteredPstar_tendsto_centeredXi_of_modeChiThetaRates
  selectedFerrersCofinalSlotS2_of_modeChiThetaRates

INPUTS:
  exact selected Ferrers pre-anchor data;
  selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates;
  hmode, hchi, htheta rate families;
  selectedFerrersPreAnchorSourceScaledMellinProjectionTailRate;
  existing pre-anchor full-Mellin/Gwin identity;
  existing raw-zero normalizer identity;
  existing selected Muntz limit;
  compact-substrip containment.

REQUIRED OBJECT ORDER:
  first exact selected-shell residual identity;
  then norm inequality;
  then compact uniform limit.

FORBIDDEN:
  old S plus hFamily;
  selectedTrialNormalizerBounded premise;
  free compact-rate premise;
  bare L2 to compact-open inference;
  new subsequence;
  sigma equals one-half;
  changing the shell constructor;
  reopening W5;
  H2a, Theorem510, route promotion, RH claim.

VALIDATION:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
    lake build Q3.Proofs.RouteB.G6N1PreAnchorLimitZeroModeAndSelectedShell
    lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersN2CompactDecayAssembly.lean
    lake build Q3.Proofs.RouteB.G6N1SelectedFerrersN2CompactDecayAssembly

  WORKDIR repo root:
    scripts/q3_check.sh Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
    scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersN2CompactDecayAssembly.lean

EXPECTED AXIOMS FOR EVERY PUBLIC THEOREM:
  [propext, Classical.choice, Quot.sound]

SUCCESS:
  SELECTED_FERRERS_N2_N3_N4_COMPACT_CLOSURE_LEAN

FAILURE:
  GOAL058_N2_SELECTED_SHELL_TAIL_REINDEX_OR_CENTERED_MELLIN_ASSEMBLY_GAP
```

## META CLOSEOUT

**Что стало меньше?**

Главная N2 analytic wall

```text
source scale × moving Mellin envelope × projection tail
```

закрыта в Lean на точном pre-anchor объекте.

**Что убито?**

```text
sourceScale upper bound as N2 premise;
inverse sourceScale bound;
selected trial normalizer as N2 premise;
old S + hFamily representation;
bare cofinal bandwidth;
bare L2 convergence.
```

**Что нельзя пробовать снова?**

Нельзя возвращать lossier majorant, выбирать новую подпоследовательность или скрывать private tail shift за словом «eventually».

**Текущая минимальная щель:**

```text
SELECTED_SHELL_COFINAL_REINDEX_AND_CENTERED_MELLIN_ASSEMBLY
```

**Следующий дешёвый решающий тест:**

Доказать public exact reindex receipt. Если он не типизируется без изменения selected-shell constructor, остановить транзакцию до любой compact analysis.

**Fate predictions:**

```text
P_N2_LEAN_1: CONFIRMED.
P_N2_ASSEMBLY_1: LIVE.
```

**Memory entry:**

```yaml
iteration: REQ-2026-08-26-K
  target: SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE
  status: PROGRESS
  failed_strategy: separate_scale_majorants_and_old_family_crosswalk
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SELECTED_SHELL_COFINAL_REINDEX_AND_CENTERED_MELLIN_ASSEMBLY
  invariant_learned: exact_scalar_homogeneity_before_norm_and_same_tail_shift
  forbidden_future_move: bare_L2_to_compact_or_private_shift_handwave
  next_decisive_test: public_cofinal_reindex_receipt
```
