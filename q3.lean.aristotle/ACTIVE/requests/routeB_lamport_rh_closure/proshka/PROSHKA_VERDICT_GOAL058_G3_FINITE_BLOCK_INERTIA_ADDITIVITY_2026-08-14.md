Ы.

PRIMARY_VERDICT:
ACCEPT_G3_MODE4_FINITE_BLOCK_INERTIA_ADDITIVITY

THEOREM_SURFACE_CHECK:
PASS.

Attachment SHA-256:
`f75c26c1d8fbecba265f82b221e03ab0b2fb1cef6dfaa515f632c8988362654e`.

The patch adds exactly three public declarations:

1. `mode4Finrank_le_hermitianNegativeEigenvalueCount_of_negDefOn`;
2. `mode4Exists_negDefSubspace_finrank_eq_hermitianNegativeEigenvalueCount`;
3. `mode4ActualFiniteJacobiTruncation_negativeCount_eq_schurApprox`.

The first two expose the already existing negative spectral-projector machinery. Neither theorem assumes matrix nonsingularity, determinant nonvanishing, a spectral gap, or invertibility. They characterize the maximal dimension of a strictly negative subspace.

The production theorem has exactly the source hypotheses `hm`, `hK`, `hsep`, and `hΛ`. It proves equality of negative counts for the literal finite Jacobi truncation and the literal terminal-zero Schur approximation. No public placeholder, endpoint count, or classical-spectrum object is introduced. `[FINITE_CELL][LEAN]` 

CONGRUENCE_DIRECTION_CHECK:
PASS.

The generic pullback theorem proves the correct one-sided direction:

```text
negativeCount(Bᴴ Q B) ≤ negativeCount(Q).
```

It maps a maximal negative subspace through `B.mulVecLin`. Injectivity on that subspace follows because a vector in the kernel would have zero pulled-back quadratic form, contradicting strict negativity.

For square invertible `B`, the reverse inequality is obtained by applying the same theorem to `⅟B`. The proof then verifies the exact recovery identity:

```text
(⅟B)ᴴ * (Bᴴ * Q * B) * ⅟B = Q.
```

Thus congruence preserves, rather than merely bounds, the negative count.

In the LDU application the congruence matrix is the explicit invertible upper block-unitriangular matrix:

```text
P = fromBlocks 1 (B * D⁻¹) 0 1.
```

The proof correctly applies congruence through `Pᴴ`; it does not reverse the pullback direction or confuse similarity with congruence. `[ABSTRACT][LEAN]`

POSDEF_TAIL_CHECK:
PASS.

For:

```text
H = fromBlocks A 0 0 D
```

with `D.PosDef`, the proof establishes both inequalities.

For the upper inequality, projection of a negative subspace to the `A` coordinates is injective: if the first component vanished, the remaining nonzero `D` component would have strictly positive quadratic form, contradicting negativity.

The projected image is strictly negative for `A`, because the `D` contribution is nonnegative.

Conversely, a maximal negative subspace for `A` embeds into the first block and remains strictly negative for `H`.

Therefore:

```text
negativeCount(fromBlocks A 0 0 D) = negativeCount(A).
```

The empty eliminated carrier is covered without a hidden `Nonempty` or positive-dimension binder. `D.PosDef` is then vacuous on the empty space, and the same proof remains valid. `[ABSTRACT][LEAN]`

SCHUR_ORIENTATION_CHECK:
PASS.

The proof uses the exact Mathlib bottom-right Schur convention:

```text
S = A - B * D⁻¹ * Bᴴ.
```

The block factorization is:

```text
[ A   B  ]     [ I  B D⁻¹ ] [ S  0 ] [ I     0 ]
[ Bᴴ  D  ]  =  [ 0    I   ] [ 0  D ] [ D⁻¹Bᴴ I ].
```

The proof explicitly derives:

```text
Pᴴ = fromBlocks 1 0 (D⁻¹ * Bᴴ) 1.
```

The `Bᴴ` orientation is therefore correct. `D⁻¹` is Hermitian because `D` is positive definite. No transpose-only or wrong-side inverse is substituted.

Proof-dependent `IsHermitian` arguments are transported only across exact matrix equalities by:

```lean
mode4NegativeCount_eq_of_matrix_eq
```

whose `subst`/`rfl` proof uses proof irrelevance legitimately. `[ABSTRACT][LEAN]` 

SOURCE_SPECIALIZATION_CHECK:
PASS.

The specialization defines:

```text
M = mode4ActualFiniteJacobiTruncation mProject Λ K d
A = M.toBlocks₁₁
B = M.toBlocks₁₂
D = M.toBlocks₂₂.
```

It consumes exactly:

```lean
mode4ActualFiniteJacobiTruncation_tailBlock_posDef
```

and:

```lean
mode4ActualFiniteJacobiTruncation_schurComplement_eq_approx_of_separation.
```

The source block identity is recovered using `Matrix.fromBlocks_toBlocks`; the lower-left block is rewritten from the Hermitian block decomposition as `Bᴴ`.

The exact Schur complement is then rewritten to:

```text
mode4BackwardTailSchurApprox mProject Λ K d.
```

No finite Jacobi surrogate, reversed tail, independently defined Schur matrix, endpoint count, or source-spectrum label enters the theorem. `[FINITE_CELL][LEAN]` 

PLANT_CHECK:
PASS.

The three plants are mathematically relevant and their boundaries are honest:

1. `BLOCK_INERTIA_POSDEF_GUARD_REQUIRED`:
   a negative one-dimensional eliminated block contributes one negative direction while the zero Schur block contributes none.

2. `BLOCK_INERTIA_HERMITIAN_ONLY_MUTATION_REJECTED`:
   Hermitianity alone does not replace positive definiteness.

3. `BLOCK_INERTIA_FINITE_DOES_NOT_SUPPLY_SINGULAR_LIMIT_STABILITY`:
   the sequence `[-1/(d+1)]` has negative count one at every finite stage but converges to the zero matrix with count zero.

The first two overlap deliberately but test distinct unsafe claims: the actual count failure and the insufficiency of the weakened guard. The third blocks finite-to-singular-limit promotion.

The scratch plant source is not a commit artifact. The packet reports direct Lean PASS and standard axioms; this judge did not rerun those commands. `[FINITE_CELL][LEAN_REPORTED]` 

NONCLAIM_CHECK:
PASS.

Acceptance is strictly:

```text
[FINITE_CELL][LEAN]
conditional on hm, hK, hsep, hΛ.
```

The leaf proves none of:

```text
endpoint negative counts 2 or 3;
endpoint nonsingularity;
stabilization at a singular limit;
classical even-spectrum counting;
zero finite-split offset;
degree-four or third-even identification;
root existence;
cofinal simple-even ground package;
G1 closure;
G3 closure;
Route B promotion;
RH.
```

COMMIT_RULING:
AUTHORIZED.

One isolated three-file commit and push is acceptable for exactly:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0Mode4HermitianNegativeCountStability.lean
```

locked at:

```text
55cb32ce2a5b596f9ee1d292968d8dbc1777051c07229be571fff57c8024480f
```

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0Mode4FiniteBlockInertiaAdditivity.lean
```

locked at:

```text
82f9e2547ac679e511a1578bbdbed87a5986589743cd00ed043aa862018d8dda
```

```text
q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
  GOAL058_G3_FINITE_BLOCK_INERTIA_ADDITIVITY_REPORT_2026-08-14.md
```

using the exact report bytes embedded in the controlling packet.

Do not stage:

```text
/tmp/Goal058FiniteBlockInertiaPlants.lean;
inventory or semantic-refresh files;
Route, Bus, runtime, protocol, or unrelated files.
```

Any byte change to either Lean file or the report requires a new review.

G1_STATUS:
OPEN — unchanged.

G3_STATUS:
OPEN — the finite-cell block-inertia transport is accepted, but no source count or mode-index theorem is supplied.

STRONGEST_SURVIVING_WALL:
`SOURCE_COUNTS_AND_INDEX4_IDENTIFICATION_MISSING`.

The accepted theorem transports any independently obtained negative count between the literal actual finite truncation and its exact finite Schur approximation.

It does not produce that count.

The remaining source wall is to identify the eventual finite DLMF count—or an equivalent literal source count—and connect it to the classical ordered even spectrum with exact index, shift, reversal, and zero-offset accounting. The source packet explicitly separates this from the now-proved tail positivity and block-inertia leaves. `[COFINAL_FAMILY][CONDITIONAL]` 

NEXT_EXACT_BOUNDED_LEAF:

```lean
theorem
    mode4ActualFiniteJacobiTruncation_negativeCount_eventually_eq_hermitianSchurMatrix
    (mProject K : ℕ)
    (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20)
    (hdet :
      (mode4HermitianSchurMatrix mProject Λ K).det ≠ 0) :
    ∀ᶠ d in Filter.atTop,
      mode4HermitianNegativeEigenvalueCount
          (mode4ActualFiniteJacobiTruncation
            mProject Λ K d)
          (mode4ActualFiniteJacobiTruncation_isHermitian
            mProject Λ K d)
        =
      mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject Λ K)
          (mode4HermitianSchurMatrix_isHermitian
            mProject K Λ)
```

Required inputs:

```text
mode4ActualFiniteJacobiTruncation_negativeCount_eq_schurApprox;
mode4BackwardTailSchurApprox_tendsto_literal;
mode4HermitianNegativeEigenvalueCount_eventually_eq_of_tendsto_of_det_ne_zero.
```

This leaf is only the exact finite-to-literal count transport at a nonsingular fixed endpoint. It must not assume or conclude a numerical count, a classical index, or endpoint values `2/3`. The convergence and fixed-carrier theorem already have the exact required shapes.

STOP_CODE:
FINITE_BLOCK_INERTIA_ADDITIVITY_PROVED_SOURCE_COUNTS_AND_INDEX4_IDENTIFICATION_MISSING
