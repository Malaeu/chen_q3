# STATUS: CONDITIONAL — N2 EXPONENT LEDGER RATIFIED WITH AN EXACT PRE-ANCHOR REPRESENTATION REPAIR; ONE LEAN TRANSACTION AUTHORIZED
```yaml
PRIMARY: RUN_GOAL058_SELECTED_FERRERS_N2_PREANCHOR_SCALED_TAIL_RATE
PRIMARY_COUNT: 1

QUEUE:
  QUEUE_REQ_ID: REQ-2026-08-26-J
  QUEUE_REQ_ID_PROVENANCE: JUDGE_ASSIGNED_TO_DIRECT_FOLLOWUP_OF_REQ_2026_08_26_I
  SOURCE_QUEUE: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_STATUS_MUTATED: false
  STALE_OPEN_ENTRY_OBSERVED: REQ-2026-08-21-P_HAS_EXISTING_VERDICT_AND_IS_NOT_REANSWERED

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  HEAD: f3bd773d8d47495709f023d4e2990968503484d8
  HEAD_IS_ORIGIN_RH_CLEAN_AT_AUDIT: true
  PARENT_VERDICT_COMMIT: 6fa176542a7f519c4d3e156f5f86df6ede78159e
  PREFLIGHT_COMMIT: f3bd773d8d47495709f023d4e2990968503484d8
  PREFLIGHT_PATH: docs/routeB_bus/LINUX_SELECTED_FERRERS_N2_COMPACT_RATE_PREFLIGHT_GOAL058_2026-08-26.md
  PREFLIGHT_GIT_BLOB: 998d0707fd5e276b0f6f80d89052a53fdf2c467c
  PREFLIGHT_MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_IN_PREFLIGHT: false
  NUMERICAL_PROBE_IN_PREFLIGHT: false

PREFLIGHT_ADJUDICATION:
  reported_result: SELECTED_FERRERS_N2_COMPACT_RATE_LEAN_READY
  adjudicated_result: RATIFIED_WITH_REPRESENTATION_REPAIR
  center_normalizer_cancellation: PASS
  exact_N2_object: SOURCE_SCALE_TIMES_UNNORMALIZED_PROJECTION_RESIDUAL
  selected_trial_normalizer_as_N2_premise: REJECTED_NOT_LOAD_BEARING
  exponent_ledger_for_every_fixed_sigma_lt_half: PASS
  sigma_equal_half: NOT_PROVED_AND_CURRENT_MAJORANT_DOES_NOT_VANISH
  new_analytic_input_required: none

REPRESENTATION_REPAIR:
  report_proposed_object:
    carrier: old_ProlateCanonicalSourceData_S_plus_hFamily
    bound_method: separate_sourceScale_upper_bound_times_unscaled_residual_bound
    status: MATHEMATICALLY_SUFFICIENT_BUT_NONMINIMAL
  selected_object:
    carrier: literal_selectedFerrersPreAnchorIndex_and_selectedFerrersPreAnchorPair
    bound_method: exact_scalar_projection_homogeneity
    identity: sourceScale_times_gTrial_equals_selectedFerrersEStarHm
    consequence: sourceScale_times_projection_residual_equals_projection_residual_of_selectedFerrersEStarHm
    status: PRIMARY
  removes:
    - ProlateCanonicalSourceData_S
    - SelectedFerrersPreAnchorProductionFamilyCrosswalk_hFamily
    - selectedTrialNormalizerBounded
    - eventual_upper_bound_on_norm_sourceScale73
    - eventual_upper_bound_on_norm_inverse_sourceScale73
    - factor_8_paid_by_inverse_scale_conversion
  preserves:
    - literal_Ferrers_preanchor_packet
    - exact_sourceScale73
    - precommitted_schedule_m_eq_N_eq_k_plus_2
    - moving_window_and_dStar_measure
    - exact_sigma_range_zero_le_sigma_lt_one_half

EXACT_RATE_LEDGER:
  schedule:
    m_k: k_plus_2
    N_k: k_plus_2
    lambda_k: sqrt_k_plus_2
    L_k: log_k_plus_2
    physical_bandwidth_k: two_pi_times_k_plus_3_div_log_k_plus_2
  scaled_coefficient_constant:
    shape: AF_times_k_plus_2_to_one_quarter_times_sqrt_log_plus_two_plus_Cp_div_four_pi
    inverse_source_scale_factor: absent
  scaled_residual_squared:
    upper_shape: four_times_scaled_coefficient_constant_squared_times_L_k_div_k_plus_3
  Mellin_kernel_L2_envelope:
    domain: abs_Im_z_le_sigma
    upper: sqrt_L_k_times_lambda_k_to_sigma
  combined_shape:
    primary: log_k_to_three_halves_times_k_to_sigma_over_two_minus_one_quarter
    delta: one_quarter_minus_sigma_over_two
    vanishes_when: zero_le_sigma_and_sigma_lt_one_half
    at_sigma_equal_half: log_to_three_halves_majorant_does_not_vanish

PUBLIC_SURFACE_AUTHORIZED:
  existing_file_append_only_export:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5RateAssembly.lean
    theorem: selectedFerrersAbelFourierDecayBudget_rate_of_modeChiThetaRates
    role: expose_private_etw13_fourier_budget_rate_without_reopening_W5_analysis
  new_file:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersN2SourceScaledTailRate.lean
    theorem: selectedFerrersPreAnchorSourceScaledMellinProjectionTailRate
    conclusion: source_scaled_projection_residual_times_closed_substrip_kernel_envelope_tends_to_zero
  expected_axiom_profiles:
    selectedFerrersAbelFourierDecayBudget_rate_of_modeChiThetaRates:
      - propext
      - Classical.choice
      - Quot.sound
    selectedFerrersPreAnchorSourceScaledMellinProjectionTailRate:
      - propext
      - Classical.choice
      - Quot.sound

TRANSACTION:
  TASK_ID: GOAL058_SELECTED_FERRERS_N2_PREANCHOR_SCALED_TAIL_RATE
  MODE: ONE_GOAL_ONE_COMMIT
  LEAN_SOURCE_AUTHORIZED: true
  SOURCE_RECORD_REQUIRED_SAME_COMMIT: true
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_N2_PREANCHOR_SCALED_TAIL_RATE_2026-08-26.md
  EXISTING_W5_BYTES_MAY_CHANGE: false
  EXISTING_W5_THEOREM_STATEMENTS_MAY_CHANGE: false
  EXISTING_W5_THEOREM_BODIES_MAY_CHANGE: false
  ALLOWED_W5_CHANGE: append_one_public_export_wrapper_after_existing_content
  NEW_ANALYTIC_INPUT: none
  CLOSES:
    - SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE
  OPENS: []

SUCCESS_CODE: SELECTED_FERRERS_N2_PREANCHOR_SOURCE_SCALED_TAIL_RATE_LEAN
FAILURE_CODE: GOAL058_N2_PREANCHOR_SCALED_RESIDUAL_OR_LOG_RATE_GAP

NEXT_AFTER_SEMANTIC_ADMISSION_ONLY:
  TASK_ID: GOAL058_SELECTED_FERRERS_N2_COMPACT_DECAY_ASSEMBLY
  TARGET: SELECTED_FERRERS_SOURCE_SCALED_MELLIN_COMPACT_DECAY
  NEW_ANALYTIC_INPUT_EXPECTED: none

FORBIDDEN:
  - add_a_free_compact_rate_premise
  - infer_compact_open_decay_from_bare_L2_decay
  - retain_selectedTrialNormalizer_as_N2_input
  - use_old_S_plus_hFamily_when_the_literal_preanchor_object_suffices
  - multiply_two_independent_scale_majorants_when_exact_scalar_homogeneity_cancels_them
  - modify_existing_W5_theorem_statements_or_bodies
  - reopen_edge_band_top_or_seam_analysis
  - select_a_new_subsequence
  - claim_sigma_equal_one_half
  - confuse_projection_tail_with_ground_state_tracking
  - promote_Route_B_or_claim_RH

PREDICTION_FATES:
  P_N2_OBJECT_1:
    prior_probability: 0.90
    fate: CONFIRMED
  P_N2_RATE_1:
    prior_probability: 0.87
    fate: CONFIRMED_AS_SUFFICIENT_NOT_MINIMAL
    no_retroactive_repair: true
    note: bounded_sourceScale_does_pay_the_reported_ledger_but_exact_homogeneity_removes_that_factor_entirely

NEW_PREDICTIONS:
  P_N2_LEAN_1:
    probability: 0.86
    prediction: one_append_only_rate_export_plus_one_new_preanchor_rate_file_pass_the_kernel_without_new_analytic_input
  P_N2_ASSEMBLY_1:
    probability: 0.89
    prediction: after_semantic_admission_the_N2_compact_decay_assembly_closes_without_new_analytic_supplier
  MOST_LIKELY_FAILURE:
    code: LEAN_SCALAR_PROJECTION_RESIDUAL_NORMAL_FORM_MISMATCH
    mathematical_gap_predicted: false

ARSENAL_MANDATE: ACCEPTED_CURRENT_DECK
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. Source and scope lock

The audited branch head is the preflight commit `f3bd773d8d47495709f023d4e2990968503484d8`.  Its only delta from the parent verdict is the read-only preflight report.  No Lean source, route state or numerical artifact changed. `[COFINAL_FAMILY][PAPER]`

The report correctly resolves the main discriminator:

\[
\boxed{
\text{N2 consumes the source-scale-weighted unnormalized projection residual.}
}
\]

The finite projection normalizer cancels in the exact centered identity and must not survive as an N2 premise.  The local-cell normalizer theorem remains a correct supplier for the literal normalized Hilbert residual, but it is not the sharp compact-Mellin consumer. `[COFINAL_FAMILY][PAPER]`

### 2. The exponent ledger is correct

On the frozen schedule

\[
m_k=N_k=k+2,
\qquad
\lambda_k=\sqrt{k+2},
\qquad
L_k=\log(k+2),
\]

the exact physical bandwidth is

\[
B_k=\frac{2\pi(k+3)}{\log(k+2)}.
\]

The W5 first-order coefficient ledger gives a coefficient constant with growth

\[
C_k
=
O\!\left((k+2)^{1/4}\sqrt{\log(k+2)+2}\right).
\]

The first-order tail receiver therefore gives

\[
\|P_kg_k-g_k\|
=
O\!\left(\frac{\log k}{k^{1/4}}\right).
\]

For `|Im z| <= sigma`, the exact moving-window Mellin kernel satisfies

\[
\|u^{-iz}\|_{L^2(d^*u,[\lambda_k^{-1},\lambda_k])}
\le
\sqrt{L_k}\,\lambda_k^\sigma.
\]

Thus the report's product has shape

\[
(\log k)^{3/2}k^{\sigma/2-1/4}.
\]

It tends to zero for every fixed

\[
0\le\sigma<\frac12.
\]

The endpoint `sigma = 1/2` is not covered: the present upper envelope grows like a power of `log k`.  The strict substrip range is therefore load-bearing and must remain explicit. `[COFINAL_FAMILY][PAPER]`

### 3. The report's proposed theorem is sufficient but not minimal

The report proposes proving the rate on the older all-index object

```text
S : ProlateCanonicalSourceData
+ hFamily : SelectedFerrersPreAnchorProductionFamilyCrosswalk S
```

and bounding

\[
\|\text{sourceScale}_k\|\,\|P_kg_k-g_k\|
\]

by multiplying two separately proved estimates:

```text
sourceScale upper bound;
unscaled W5 residual bound.
```

That route is mathematically valid.  It is not the correct primary representation for N2.

The paper port and terminal selected shell are built from the literal pre-anchor Ferrers family.  The old all-index `S` is a transport scaffold, not the final source object.  Retaining it here introduces an unnecessary family crosswalk at the precise point where the route is supposed to become same-family.  This triggers the **C04** question: equal after which forgetful interface, and which source-family data were dropped? `[COFINAL_FAMILY][PAPER]` **[C04]**

More decisively, the repository already proves the exact source relation

\[
g_k
=
\text{sourceScale}_k^{-1}\,E_k,
\]

where `E_k` is the literal `selectedFerrersEStarHm` vector.  Orthogonal projection is linear, so

\[
\boxed{
\text{sourceScale}_k\,(P_kg_k-g_k)
=
P_kE_k-E_k.
}
\]

Therefore the source scale does not need to be estimated at all.  Its norm and inverse norm disappear by exact homogeneity before any inequality is taken.  The report's factor `8`, paid when converting from the scaled packet to the unscaled trial, also disappears.

This is a direct **C10** repair: prove the estimate for the functional the consumer actually needs, not for two neighboring norms followed by a lossy majorization. `[COFINAL_FAMILY][PAPER]` **[C10]**

### 4. Stronger exact rate map

Let

\[
A_k
=
A_F(k+2)^{1/4}\sqrt{\log(k+2)+2}
+
\frac{C_p}{4\pi}.
\]

Using the physical Fourier coefficient envelope directly on `selectedFerrersEStarHm`, Parseval and the two-sided omitted-mode sum give

\[
\|P_kE_k-E_k\|^2
\le
4A_k^2\frac{L_k}{k+3}.
\]

Consequently

\[
\sqrt{L_k}\,\lambda_k^\sigma
\|\text{sourceScale}_k(P_kg_k-g_k)\|
\le
2A_kL_k\frac{(k+2)^{\sigma/2}}{\sqrt{k+3}}.
\]

With

\[
\delta=\frac14-\frac\sigma2>0,
\]

the first term is bounded by a constant times

\[
\frac{(\log(k+2)+2)^{3/2}}{(k+2)^\delta},
\]

and the center term is bounded by a constant times

\[
\frac{\log(k+2)(k+2)^{\sigma/2}}{\sqrt{k+3}}.
\]

Both tend to zero.  No upper bound for the source scale, no inverse-scale bound, no normalizer bound and no new subsequence occur. `[COFINAL_FAMILY][PAPER]`

## FINAL PROPOSAL

Authorize one bounded Lean transaction.

### A. Append-only quantitative export

Append one theorem to

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersW5RateAssembly.lean
```

without changing any existing byte, declaration, theorem statement or theorem body:

```lean
theorem selectedFerrersAbelFourierDecayBudget_rate_of_modeChiThetaRates
    (C0 C4 Cχ Cθ : ℝ)
    (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4)
    (hCχ : 0 ≤ Cχ) (hCθ : 0 ≤ Cθ)
    (hmode : /* exact frozen family */)
    (hχ : /* exact frozen family */)
    (hθ : /* exact frozen family */) :
    ∃ AF : ℝ, 0 ≤ AF ∧
      ∀ᶠ k : ℕ in Filter.atTop,
        selectedFerrersAbelFourierDecayBudget k ≤
          AF *
            (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
              Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2))
```

The proof is a thin public wrapper around the already-kernel-green private `etw13_fourier_budget_rate`.  It exports an existing quantitative fact; it does not reopen W5 analysis. `[COFINAL_FAMILY][CONDITIONAL]`

### B. New exact pre-anchor rate theorem

Create:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersN2SourceScaledTailRate.lean
```

with one main public theorem:

```lean
theorem selectedFerrersPreAnchorSourceScaledMellinProjectionTailRate
    (C0 C4 Cχ Cθ : ℝ)
    (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4)
    (hCχ : 0 ≤ Cχ) (hCθ : 0 ≤ Cθ)
    (hmode : /* exact frozen family */)
    (hχ : /* exact frozen family */)
    (hθ : /* exact frozen family */)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2) :
    Filter.Tendsto
      (fun k : ℕ =>
        Real.sqrt (L_m (selectedFerrersPreAnchorIndex k)) *
          lambda_m (selectedFerrersPreAnchorIndex k) ^ σ *
          ‖selectedFerrersLemma73SourceScale k •
            ((gTrial_m_N
                (selectedFerrersPreAnchorIndex k)
                (prolateCombination (selectedFerrersPreAnchorPair k))
                (selectedFerrersPreAnchorPair_eStar_memLp k) :
                  H_m (selectedFerrersPreAnchorIndex k)) -
              gTrial_m
                (selectedFerrersPreAnchorIndex k)
                (prolateCombination (selectedFerrersPreAnchorPair k))
                (selectedFerrersPreAnchorPair_eStar_memLp k))‖)
      Filter.atTop (nhds 0)
```

Minor elaboration repairs to the displayed syntax are allowed.  The mathematical object, binders and conclusion may not change. `[COFINAL_FAMILY][CONDITIONAL]`

### Required proof route

```text
1. Prove the exact local identity:
     sourceScale • gTrial = selectedFerrersEStarHm.

2. Commute the same scalar through the literal Galerkin projection.

3. Rewrite the scaled projection residual as the projection residual of
   selectedFerrersEStarHm.

4. Use the public coefficient envelope for selectedFerrersEStarHm.

5. Use the new public Abel-budget rate wrapper and the existing F72.6 center rate.

6. Reconstruct the two-sided 1/n² omitted-mode tail or reuse only public Parseval/tail lemmas.

7. Substitute the exact selected schedule and close the two log-versus-power limits.
```

The precommitted schedule remains `m=N=k+2`; this is the **C09** guard. `[COFINAL_FAMILY][PAPER]` **[C09]**

### Verification handoff

**WORKDIR: `q3.lean.aristotle`**

```bash
lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersW5RateAssembly.lean
lake build Q3.Proofs.RouteB.G6N1SelectedFerrersW5RateAssembly

lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersN2SourceScaledTailRate.lean
lake build Q3.Proofs.RouteB.G6N1SelectedFerrersN2SourceScaledTailRate
```

**WORKDIR: repository root**

```bash
scripts/q3_check.sh \
  Q3/Proofs/RouteB/G6N1SelectedFerrersW5RateAssembly.lean

scripts/q3_check.sh \
  Q3/Proofs/RouteB/G6N1SelectedFerrersN2SourceScaledTailRate.lean
```

Required profiles for both public theorems:

```text
[propext, Classical.choice, Quot.sound]
```

The source record must use the current YAML contract and include both Lean Git blobs and SHA-256 receipts.  A diff audit must confirm that the old W5 file changed only by the appended wrapper.

Success:

```text
SELECTED_FERRERS_N2_PREANCHOR_SOURCE_SCALED_TAIL_RATE_LEAN
```

Failure:

```text
GOAL058_N2_PREANCHOR_SCALED_RESIDUAL_OR_LOG_RATE_GAP
```

## STRONGEST ATTACK

The strongest reviewer objection is:

> The report proves a bound on `norm(sourceScale) * norm(residual)`, but N2 needs the Mellin transform of `sourceScale * residual`.  Are these really the same source object, or has the scale been moved across a projection without proof?

This objection is load-bearing.  The next file must prove the exact scalar/projection identity before taking norms.  A mere equality of norm products is not an object crosswalk.  If the projection API does not permit this exact rewrite, the transaction stops with the stated failure code; it may not fall back to a free compact-rate premise or the old normalized residual. `[COFINAL_FAMILY][CONDITIONAL]` **[C04][C10]**

A second attack is the strip endpoint.  The present rate is genuinely strict-substrip only.  No statement at `sigma = 1/2` is authorized, and compact-local promotion must choose a separate `sigma < 1/2` for each compact subset of the open strip. `[COFINAL_FAMILY][PAPER]`

A third attack is that the append-only wrapper may accidentally change the frozen W5 theorem through import or namespace rewiring.  The diff guard is therefore semantic: no existing declaration may change, and both the old W5 theorem and the new wrapper must pass their own axiom audit. `[ABSTRACT][PAPER]`

## CODEX DIRECTIVE

```text
TASK_ID:
  GOAL058_SELECTED_FERRERS_N2_PREANCHOR_SCALED_TAIL_RATE

MODE:
  ONE_GOAL_ONE_COMMIT

READ_FIRST:
  docs/routeB_bus/SUPPLIER_CONTRACT.md
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5RateAssembly.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersMidpointDeltaEnvelope.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFirstOrderBudgetApplication.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarFirstOrderProjectionTailReceiver.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean

WRITE:
  1. Append exactly one public export wrapper to
     G6N1SelectedFerrersW5RateAssembly.lean.

  2. Create
     G6N1SelectedFerrersN2SourceScaledTailRate.lean.

  3. Create the YAML-compliant source record in the same commit.

DO_NOT_WRITE:
  G6N1SelectedFerrersTrialNormalizerClosure.lean
  any edge-band/top/seam source
  any route-state file
  Q3.Main

PUBLIC_THEOREMS:
  selectedFerrersAbelFourierDecayBudget_rate_of_modeChiThetaRates
  selectedFerrersPreAnchorSourceScaledMellinProjectionTailRate

FORBIDDEN:
  hFamily
  arbitrary S : ProlateCanonicalSourceData
  selectedTrialNormalizer
  sourceScale upper or inverse-scale bound
  new subsequence
  free compact-rate hypothesis
  sigma = 1/2
  theorem weakening
  numerical proof

VALIDATION:
  run all four lake commands and both q3_check commands from the stated workdirs;
  print axioms for both public theorems;
  verify the old W5 file changed only by an appended wrapper;
  report exact stdout, exit codes, blobs and SHA-256 receipts.

SUCCESS:
  SELECTED_FERRERS_N2_PREANCHOR_SOURCE_SCALED_TAIL_RATE_LEAN

FAILURE:
  GOAL058_N2_PREANCHOR_SCALED_RESIDUAL_OR_LOG_RATE_GAP
```

## META CLOSEOUT

**What became smaller?**

The moving compact-Mellin wall is no longer an unspecified need for faster Hilbert convergence.  It is one exact rate theorem on the literal source-scaled pre-anchor projection residual. `[COFINAL_FAMILY][PAPER]`

**What was killed?**

The need to carry the finite trial normalizer, the source-scale upper bound, the inverse-scale bound, the old all-index family and the `hFamily` transport into N2. `[COFINAL_FAMILY][PAPER]`

**What must not be tried again?**

Do not multiply separately estimated scale and residual norms when exact scalar homogeneity moves the scale through the projection.  Do not prove compact decay on a neighboring all-index family and relabel it as the selected pre-anchor shell. `[COFINAL_FAMILY][PAPER]`

**Current smallest named gap**

```text
SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE
```

**Next cheapest decisive test**

Kernel-check the exact scalar/projection residual identity.  If that compiles, the remaining rate algebra uses already-proved coefficient and log-versus-power machinery. `[COFINAL_FAMILY][CONDITIONAL]`

**Prediction fate**

`P_N2_OBJECT_1` is confirmed.  `P_N2_RATE_1` is confirmed as a sufficient estimate, but its source-scale-bounded representation was not minimal and is not retroactively rewritten. `[COFINAL_FAMILY][PAPER]`

**Memory entry**

```yaml
iteration:
  target: SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE
  status: PROGRESS
  failed_strategy: separate_sourceScale_upper_times_unscaled_residual
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: PREANCHOR_SCALED_PROJECTION_RESIDUAL_RATE
  invariant_learned: preserve_the_exact_scaled_residual_object_before_taking_norms
  forbidden_future_move: carry_old_S_hFamily_or_normalizer_into_N2
  next_decisive_test: kernel_check_scalar_projection_homogeneity
```
