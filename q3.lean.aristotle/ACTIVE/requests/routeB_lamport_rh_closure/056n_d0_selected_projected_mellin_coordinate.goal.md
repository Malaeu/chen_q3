# GOAL 056 / Phase 4E — selected projected Mellin coordinate

```yaml
GOAL: 056
PHASE: 4E
NODE: D0PstarProjectedMellinCoordinate
STATUS: OPEN
OPERATIVE_CLASS: TRY_G6_S2_D0_ADDITIVE_FIRST_PROJECTED_MELLIN_COORDINATE
TRANSACTION: G6_S2_D0_SELECTED_PROJECTED_MELLIN_COORDINATE_RAW_TRANSFORM
STOP: G6_S2_SELECTED_PROJECTED_MELLIN_COORDINATE_RAW_TRANSFORM_MISSING
SUCCESS: G6_S2_SELECTED_PROJECTED_MELLIN_COORDINATE_EQ_RAW_TRANSFORM_PROVED

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 5
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Delegated strategic decision

The fifth batch in the same living Proshka phase chat selected Route A,
additive-first, under `CODEX_PLUS_PROSHKA` authority at source pin
`9a8fb23054ab1f80209eb9f8920fc692d393977f`. The exact 29,836-byte verdict is
archived at
`proshka/PROSHKA_VERDICT_GOAL056_PROJECTED_MELLIN_COORDINATE_2026-08-06.md`
with SHA-256
`1cb03b92fde9a3f9983e4e80facce236e9d5cad3911490fdfd224dca65b2137d`.

The transaction is one bounded file with exactly one object-first definition,
one additive a.e. representative theorem, and one selected Mellin/raw theorem.
A direct wrapper that bundles all convention seams is rejected by
`MINIMAL_LEMMA`; defining the new coordinate from `rawFplus` is forbidden.

## Knowledge preflight receipt

```yaml
SEARCH_FLAGS:
  address: RouteB.G6.S2.ProjectedMellinCoordinate
  strong:
    - D0KTrialStage3
    - D0_6_EXACT_TRANSFORM_CONVENTION
    - D0PstarMuntzCenteredCoordinateLock
    - D0PstarMuntzGalerkinResidualContract
    - D0FiniteProjectionReconstruction
    - integral_comp_logWindow_dStar
  empty:
    - prior_projected_coordinate_theorem
  false_friend:
    - define_projected_coordinate_from_rawFplus
    - treat_Lp_equality_as_pointwise
    - global_cpow_rewrite_without_positive_window
  opens_branch:
    - selected_full_Mellin_coordinate_to_Gwin

KB_FLAGS:
  - query: RouteB.G6.S2 projected Mellin coordinate
    result: no_recorded_search
  - query: Fourier Mellin projection raw transform
    result: unvisited
  - query: G6 S2
    result: unvisited
KB_ASK:
  query: Goal 056 projected Mellin coordinate rawFplus projection reconstruction Gwin
  result: no_hits
```

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  object: normalized_projected_kTrial_m_N
  index: selectedPairIndex_S_k
  measure: dStar_restrict_I_m
  kernel: u_cpow_minus_I_z
  additive_coordinate: log_lambda_mul_u
  finite_sector: full_modeSet_Icc_minusN_N
  coefficient: inner_V_n_kTrial
  phase: exp_plus_I_z_L_over_2
  raw_rhs: rawFplus_at_minus_z

OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarProjectedMellinCoordinate.lean
PROJECT_IMPORTS:
  - Q3.Proofs.RouteB.D0FiniteProjectionReconstruction
  - Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock
NAMESPACE: Q3.RouteB.D0Pstar
PUBLIC_DEFINITIONS: 1
PUBLIC_THEOREMS: 2
PRIVATE_PRODUCTION_DECLARATIONS: 0
```

Any change to these fields after a plant fires is a new named transaction,
not an in-place repair.

## Exact production surface

```lean
noncomputable def selectedProjectedMellinCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) : ℂ :=
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  let hNonzero := S.source.trialNonzero i
  ∫ u : ℝ,
      (kTrial_m_N i h hLp hNonzero : H_m i) u *
        (u : ℂ) ^ (-Complex.I * z)
    ∂(dStar.restrict (I_m i))

theorem kTrial_m_N_coeFn_ae_eq_finiteLogFourierTrial_logWindow
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star : MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i)))
    (hTrialNonzero : TrialNonzero i hTrial_m hE_star) :
    (fun u : ℝ =>
      (kTrial_m_N i hTrial_m hE_star hTrialNonzero : H_m i) u)
      =ᵐ[dStar.restrict (I_m i)]
    (fun u : ℝ =>
      finiteLogFourierTrial
        (L_m i) (modeSet i)
        (c_n i hTrial_m hE_star hTrialNonzero)
        (Real.log (lambda_m i * u))) := by
  ...

theorem selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) :
    selectedProjectedMellinCoordinate S k z =
      selectedRawTransformCoordinate S k z := by
  ...
```

The helper must use the exact normalized projection and prove only an a.e.
representative identity. The wrapper must derive positivity from
`I_m`, rewrite `Complex.cpow` only on that branch, prove
`Real.log (lambda_m i) = L_m i / 2`, preserve the centered
`exp(+I*z*L/2)` phase, and close the double reflection at
`rawFplus ... (-z)`.

## Load-bearing plants

```yaml
P056N_1_PROJECTED_VS_FULL:
  mutation: replace_kTrial_m_N_by_normalized_gTrial_m
  expected: G6_S2_PROJECTED_MELLIN_FULL_OBJECT_SUBSTITUTION
P056N_2_NORMALIZATION:
  mutation: replace_kTrial_m_N_by_gTrial_m_N
  expected: G6_S2_PROJECTED_MELLIN_NORMALIZATION_MISMATCH
P056N_3_COEFFICIENT_CONJUGATION:
  mutation: replace_inner_V_n_kTrial_by_inner_kTrial_V_n
  control: f_eq_I_smul_V0
  expected: G6_S2_PROJECTED_MELLIN_COEFFICIENT_CONJUGATION_MISMATCH
P056N_4_MODESET_BOUNDARY:
  mutation: erase_positive_N
  control: N_eq_1_and_f_eq_V1
  expected: G6_S2_PROJECTED_MELLIN_MODESET_BOUNDARY_MISMATCH
P056N_5_DSTAR_WINDOW:
  mutations: [replace_dStar_by_volume, shift_or_one_side_window]
  expected: G6_S2_PROJECTED_MELLIN_DSTAR_WINDOW_MISMATCH
P056N_6_CENTERING_PHASE:
  mutations: [delete_exp_plus_I_z_L_over_2, flip_phase_sign]
  expected: G6_S2_PROJECTED_MELLIN_CENTERING_PHASE_MISMATCH
P056N_7_RAW_REFLECTION:
  mutation: replace_rawFplus_at_minus_z_by_rawFplus_at_z
  control: non_even_single_mode_row
  expected: G6_S2_PROJECTED_MELLIN_RAW_REFLECTION_MISMATCH
```

All seven plants must fire independently and every temporary mutation file
must be removed before closeout.

## Validation and boundary

Validation requires source-lock recheck, direct Lean, dedicated target build,
full build, `q3_check`, hole/taint/forbidden-import scans, the exact 1/2/0
public surface, all seven plants, standard-triple axioms, proof-DB reimport,
all orchestration tests, strict Spine, all three SQLite integrity checks,
observability source/stale counts, `git diff --check`, and exact status.

This leaf removes only:

```text
literal normalized projected Lp object
  -> its source-locked finite raw transform coordinate.
```

The sole next node, not authorized here, is
`selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate`.
Raw/Gwin equality, the Phase-4B contract, residual algebra/decay,
compact-open convergence, strict `SlotS2`, Q3.Main, Goal 055, Bus 010,
Aristotle, route promotion, PX, and RH claims are forbidden.
