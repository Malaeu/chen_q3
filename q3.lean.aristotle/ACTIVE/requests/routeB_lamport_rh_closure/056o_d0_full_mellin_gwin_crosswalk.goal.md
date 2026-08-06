# GOAL 056 / Phase 4F — full Mellin/Gwin crosswalk

```yaml
GOAL: 056
PHASE: 4F
NODE: D0PstarFullMellinGwinCrosswalk
STATUS: OPEN
OPERATIVE_CLASS: TRY_G6_S2_D0_SELECTED_FULL_MELLIN_GWIN_CROSSWALK
TRANSACTION: G6_S2_D0_SELECTED_FULL_MELLIN_GWIN_CROSSWALK
STOP: G6_S2_SELECTED_FULL_MELLIN_GWIN_CROSSWALK_MISSING
SUCCESS: G6_S2_SELECTED_FULL_MELLIN_AND_SCALED_GWIN_CROSSWALK_PROVED

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 6
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Delegated strategic decision

The sixth batch in the same living Proshka phase chat selected Candidate
`A_REPAIRED` under `CODEX_PLUS_PROSHKA` authority at corrected source pin
`952d0760a2741ddc2766976295b684cddb26baa4`. The exact 29,951-byte verdict is
archived at
`proshka/PROSHKA_VERDICT_GOAL056_FULL_MELLIN_GWIN_CROSSWALK_2026-08-06.md`
with SHA-256
`0e1363fdc611341a3036a3a19297ded593c93a04b5fd1205116b0d648fa18f5d`.

This transaction proves the literal unnormalized full coordinate, its exact
selected `Gwin` equality, and one definitionally algebraic scaled corollary.
It does not discharge the Phase-4B residual contract: that requires a separate
bounded-kernel `Lp -> L1` linearity bridge, not ring normalization.

## Source lock

```yaml
HEAD: 952d0760a2741ddc2766976295b684cddb26baa4
SUPPLIERS:
  D0KTrialStage2.lean: aabaf47cb484f0157fd7b2ac4f30811aec9595116c1193715e41de8b520393cd
  D0PstarMuntzCenteredCoordinateLock.lean: ce0226f7bd028449a04cae0dfa28e8998a0e835eba5ec0a56a93f0ae18b073a5
  D0PstarMuntzGalerkinResidualContract.lean: 1f9b0f16210271fc699107f991a244421d98bbdafd695d5a585dae4aca4f73ff
  D0PstarProjectedMellinCoordinate.lean: 8f0c764615873a6a3e677d13d86ba6686cc5f4b31354749e4cf171f36fed139e
  WindowEndpointBridge.lean: e3a021173e66f61389ac218ceaf6c898d64bb9854babea50f435b131ae21c44a
  D0LogWindowMeasureTransport.lean: 59c6d9a3a3a3c77427997665216e3ff797b9e2dc925cb63e5e9e6df0df64905b
  MuntzV3/Core.lean: 7df74238ff1462eb750b0f975f4b87f4b9eec5f1f46c104890d1345b8e2cf1ca
ON_MISMATCH: G6_S2_FULL_MELLIN_SOURCE_LOCK_MISMATCH
```

No production edit is permitted if any source lock fails.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  object: gTrial_m_full_unnormalized
  index: selectedPairIndex_S_k
  source_trial: selectedProlateTrial_S_k
  representative_relation: almost_everywhere
  d0_measure: dStar_restrict_I_m
  density: u_inverse
  d0_kernel: u_cpow_minus_I_z
  muntz_source: Estar_same_starred_sum
  muntz_argument: minus_I_times_z
  muntz_exponent: minus_I_z_minus_one
  d0_window: Icc_lambda_inverse_lambda
  muntz_window: Ioo_lambda_inverse_lambda
  endpoints: removed_by_atomless_volume
  base_normalization: none
  scaled_orientation: normalizer_times_coordinate

OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarFullMellinGwinCrosswalk.lean
SOLE_PROJECT_IMPORT: Q3.Proofs.RouteB.D0PstarProjectedMellinCoordinate
NAMESPACE: Q3.RouteB.D0Pstar
PUBLIC_DEFINITIONS: 1
PUBLIC_THEOREMS: 2
PRIVATE_PRODUCTION_DECLARATIONS: 0
```

These fields are frozen for this transaction. Any semantic change after a
plant fires requires a new named boundary.

## Exact production surface

```lean
noncomputable def selectedFullMellinCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) : ℂ :=
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  ∫ u : ℝ,
      (gTrial_m i h hLp : H_m i) u *
        (u : ℂ) ^ (-Complex.I * z)
    ∂(dStar.restrict (I_m i))

theorem selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) :
    selectedFullMellinCoordinate S k z =
      selectedGwinTransformCoordinate S k z := by
  ...

theorem
    selectedTrialNormalizer_mul_selectedFullMellinCoordinate_eq_selectedScaledGwinTransformCoordinate
    (S : ProlateCanonicalSourceData)
    (k : ℕ) (z : ℂ) :
    (selectedTrialNormalizer S k : ℂ) *
        selectedFullMellinCoordinate S k z =
      selectedScaledGwinTransformCoordinate S k z := by
  rw [selectedFullMellinCoordinate_eq_selectedGwinTransformCoordinate]
  rfl
```

The base theorem must travel through `MemLp.coeFn_toLp`,
`integral_congr_ae`, exact `dStar` density expansion, positivity-restricted
`Complex.cpow_sub`/`Complex.cpow_one`, the literal `E_star = Estar` starred
sum, and unconditional `MeasureTheory.integral_Icc_eq_integral_Ioo`.

## Load-bearing plants

```yaml
P056O_1_FULL_NOT_PROJECTED:
  mutation: replace_gTrial_m_by_gTrial_m_N_or_kTrial_m_N
  expected: G6_S2_FULL_MELLIN_PROJECTED_OBJECT_SUBSTITUTION
P056O_2_LP_REPRESENTATIVE:
  mutation: replace_ae_representative_by_global_pointwise_equality
  expected: G6_S2_FULL_MELLIN_LP_POINTWISE_SURROGATE
P056O_3_DSTAR_DENSITY:
  mutation: replace_dStar_by_volume_without_u_inverse
  expected: G6_S2_FULL_MELLIN_DSTAR_DENSITY_MISMATCH
P056O_4_ENDPOINT_ATOM:
  mutation: endpoint_fixture_measure_contains_dirac_atom
  expected: G6_S2_FULL_MELLIN_ENDPOINT_ATOM_MISMATCH
P056O_5_CPOW_EXPONENT:
  mutations: [replace_minus_one_by_plus_one, remove_positive_window_guard]
  expected: G6_S2_FULL_MELLIN_CPOW_EXPONENT_OR_BRANCH_MISMATCH
P056O_6_ESTAR_SOURCE:
  mutations: [omit_sqrt_u, replace_Estar_by_unstarred_h]
  expected: G6_S2_FULL_MELLIN_ESTAR_SOURCE_MISMATCH
P056O_7_SCALE_LEVEL:
  mutation: equate_unnormalized_full_coordinate_to_scaled_Gwin
  expected: G6_S2_FULL_MELLIN_SCALE_LEVEL_MISMATCH
```

All seven plants must fire independently and all temporary mutation files must
be removed before closeout.

## Validation and boundary

Validation requires source-lock recheck, direct Lean, dedicated target build,
full build, `q3_check`, hole/taint/forbidden-import scans, exact 1/2/0 public
surface, all seven plants, the standard axiom triple, proof-DB reimport, all 67
orchestration tests, strict Spine, all three SQLite integrity checks,
observability source/stale counts, `git diff --check`, and exact status.

Aristotle is forbidden. This leaf removes only:

```text
literal unnormalized full gTrial_m coordinate
  -> selected Gwin coordinate, plus the definitionally scaled corollary.
```

The sole next node, not authorized here, is
`G6_S2_D0_RESIDUAL_MELLIN_LINEARITY_AND_CONTRACT_DISCHARGE`, targeting
`selectedGalerkinResidualMellinCoordinate_eq_projected_sub_scaledFull`.
The Phase-4B contract, residual decay, compact-open convergence, strict
`SlotS2`, Q3.Main, Goal 055, Bus 010, Aristotle, route promotion, PX, and RH
claims remain forbidden.
