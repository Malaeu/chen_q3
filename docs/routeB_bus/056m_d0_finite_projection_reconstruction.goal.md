# GOAL 056 / Phase 4D — finite orthogonal-projection reconstruction

```yaml
GOAL: 056
PHASE: 4D
NODE: D0FiniteProjectionReconstruction
STATUS: OPEN
OPERATIVE_CLASS: TRY_G6_S2_D0_FINITE_ORTHOGONAL_PROJECTION_RECONSTRUCTION
TRANSACTION: G6_S2_D0_FINITE_ORTHOGONAL_PROJECTION_RECONSTRUCTION
STOP: G6_S2_FINITE_ORTHOGONAL_PROJECTION_RECONSTRUCTION_MISSING
SUCCESS: G6_S2_P_M_N_FINITE_FOURIER_RECONSTRUCTION_PROVED

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 4
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Delegated strategic decision

The same living Proshka phase chat selected the direct orthonormal-basis route
under `CODEX_PLUS_PROSHKA` authority at source pin
`a04753e0c435006768fde50fd546acdccf1ee0cf`. The exact 25,576-byte verdict is
archived at
`proshka/PROSHKA_VERDICT_GOAL056_FINITE_PROJECTION_RECONSTRUCTION_2026-08-06.md`
with SHA-256
`7390e4ea3722a06e0e42ca7d9412bad814b22566915bde49e88851a63816ef50`.

No weakening is needed. Route A is mandatory:
`OrthonormalBasis.span` followed by exactly one use of
`OrthonormalBasis.orthogonalProjection_eq_sum`. The custom uniqueness route
and any surrogate-basis route are killed for this transaction.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  ambient_carrier: H_m i
  exact_submodule: E_m_N i
  exact_projection: P_m_N i
  exact_finset: modeSet i
  exact_boundary: Icc_negative_N_positive_N
  exact_basis: V_n_m i restricted to modeSet i
  exact_coefficient: inner_V_n_f
  exact_output: ambient_coercion

OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0FiniteProjectionReconstruction.lean
SOLE_PROJECT_IMPORT: Q3.Proofs.RouteB.D0LogWindowMeasureTransport
MATHLIB_IMPORT: Mathlib.Analysis.InnerProductSpace.PiL2
NAMESPACE: Q3.RouteB.D0Pstar
PUBLIC_DEFINITIONS: 0
PUBLIC_THEOREMS: 1
PRIVATE_PRODUCTION_DECLARATIONS: 0
```

Any change to one of these fields after a plant fires is a new named
transaction, not an in-place repair.

## Exact production surface

```lean
theorem coe_P_m_N_apply_eq_sum_inner_V_n_m_smul
    (i : PairIndex) (f : H_m i) :
    (P_m_N i f : H_m i) =
      ∑ n ∈ modeSet i,
        inner ℂ (V_n_m i n) f • V_n_m i n := by
  ...
```

Required route:

1. Install the exact finite-dimensional and complete-space instances for
   `E_m_N i`.
2. Construct `OrthonormalBasis.span (V_n_m_orthonormal i) (modeSet i)`.
3. Normalize its carrier to literal `E_m_N i` with `E_m_N` and
   `Finset.coe_image`.
4. Record its exact application through `OrthonormalBasis.span_apply`.
5. Invoke `OrthonormalBasis.orthogonalProjection_eq_sum` exactly once.
6. Unfold only `P_m_N`, coerce the subtype equality to `H_m i`, and normalize
   the subtype-indexed sum to the literal double Finset sum.

Forbidden routes: custom uniqueness through
`eq_starProjection_of_mem_of_inner_eq_zero`, a new auxiliary Fourier span, an
arbitrary `stdOrthonormalBasis`, reversed coefficient `inner f V_n`, theorem
weakening, or specialization only to `gTrial_m`.

## Load-bearing plants

```yaml
P056M_1_COEFFICIENT_ORIENTATION:
  mutation: inner_f_V_n
  witness: N_0_and_f_eq_I_smul_V0
  expected: G6_S2_FINITE_PROJECTION_COEFFICIENT_ORIENTATION_MISMATCH
P056M_2_MODESET_BOUNDARY:
  mutation: erase_positive_N
  witness: N_1_and_f_eq_V1
  expected: G6_S2_FINITE_PROJECTION_MODESET_BOUNDARY_MISMATCH
P056M_3_LITERAL_CARRIER:
  mutation: project_to_span_with_zero_mode_erased
  witness: N_1_and_f_eq_V0
  expected: G6_S2_FINITE_PROJECTION_CARRIER_MISMATCH
P056M_4_BASIS_NORMALIZATION:
  mutation: replace_span_basis_by_arbitrary_orthonormal_basis
  expected: G6_S2_FINITE_PROJECTION_BASIS_NORMALIZATION_MISMATCH
P056M_5_PROJECTION_NOT_IDENTITY:
  mutation: replace_P_m_N_f_by_f
  witness: N_0_and_f_eq_V1
  expected: G6_S2_FINITE_PROJECTION_NOT_IDENTITY
```

All five plants must fire independently and every temporary mutation file must
be removed before closeout.

## Validation and boundary

Validation requires direct Lean, dedicated target build, full build,
`q3_check`, hole/taint/forbidden-import scans, exactly one public theorem and
zero public/private definitions, all five plants, standard-triple axiom check,
proof-DB reimport, 67 orchestration tests, strict Spine, all three SQLite
integrity checks, `git diff --check`, and an exact status report.

This leaf removes only the dependency

```text
abstract orthogonal projection
  -> literal finite Fourier reconstruction on modeSet i.
```

It does not prove the projected-coordinate/raw-transform identity. The sole
next consumer, not authorized here, is
`Q3.RouteB.D0Pstar.selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate`.
Raw/Gwin equality, the Phase-4B contract, compact-open decay, strict `SlotS2`,
Q3.Main edits, Goal 055 edits, Bus 010, Aristotle, route promotion, PX, and RH
claims are forbidden.
