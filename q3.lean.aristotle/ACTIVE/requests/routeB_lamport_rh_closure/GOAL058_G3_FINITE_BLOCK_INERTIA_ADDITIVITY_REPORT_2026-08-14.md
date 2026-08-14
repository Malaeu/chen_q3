# Goal 058 G3 — finite block-inertia additivity

Date: 2026-08-14

Status: `FINITE_BLOCK_INERTIA_ADDITIVITY_PROVED`

Boundary: `[FINITE_CELL][CONDITIONAL_ON_PRODUCTION_SEPARATION]`

This report records one bounded G3 leaf. It does **not** close G3 or G1 and
does not authorize a Route B or RH promotion.

## Result

The literal actual finite mode-four Jacobi truncation and its terminal-zero
Schur approximation have the same number of strictly negative eigenvalues on
the already committed production separation range.

New public theorem:

```lean
theorem mode4ActualFiniteJacobiTruncation_negativeCount_eq_schurApprox
    (mProject K d : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    mode4HermitianNegativeEigenvalueCount
        (mode4ActualFiniteJacobiTruncation mProject Λ K d)
        (mode4ActualFiniteJacobiTruncation_isHermitian mProject Λ K d) =
      mode4HermitianNegativeEigenvalueCount
        (mode4BackwardTailSchurApprox mProject Λ K d)
        (mode4BackwardTailSchurApprox_isHermitian mProject K d Λ)
```

File:

`q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FiniteBlockInertiaAdditivity.lean`

Pre-review SHA-256:

`82f9e2547ac679e511a1578bbdbed87a5986589743cd00ed043aa862018d8dda`

The file is 369 lines and 16140 bytes.

## Public support surface added to the existing inertia module

File:

`q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4HermitianNegativeCountStability.lean`

Pre-review SHA-256:

`55cb32ce2a5b596f9ee1d292968d8dbc1777051c07229be571fff57c8024480f`

Two public interfaces expose the existing spectral-projector machinery:

```lean
theorem mode4Finrank_le_hermitianNegativeEigenvalueCount_of_negDefOn
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {W : Submodule ℝ (n → ℝ)}
    (hW : ∀ x ∈ W, x ≠ 0 → star x ⬝ᵥ (A *ᵥ x) < 0) :
    Module.finrank ℝ W ≤ mode4HermitianNegativeEigenvalueCount A hA

theorem mode4Exists_negDefSubspace_finrank_eq_hermitianNegativeEigenvalueCount
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ∃ W : Submodule ℝ (n → ℝ),
      (∀ x ∈ W, x ≠ 0 → star x ⬝ᵥ (A *ᵥ x) < 0) ∧
      Module.finrank ℝ W = mode4HermitianNegativeEigenvalueCount A hA
```

These are an independent Mathlib realization of the subspace form of
Sylvester inertia. The architecture was cross-checked against
`Zeta23/LinAlg/Sylvester.lean` and `Zeta23/LinAlg/Inertia.lean`
(Apache-2.0). No foreign code is copied.

## Proof spine

1. The negative spectral projector produces a strictly negative subspace of
   dimension exactly `mode4HermitianNegativeEigenvalueCount`.
2. Pullback of a Hermitian form through any matrix cannot increase that
   maximum negative dimension.
3. Pullback through an invertible square matrix preserves the negative count,
   by applying the preceding inequality to the matrix and its inverse.
4. For `fromBlocks A 0 0 D` with `D.PosDef`, projection to the `A` coordinates
   is injective on every negative subspace. Its image is negative for `A`.
   Conversely, a maximal negative subspace of `A` embeds into the first block.
   Therefore the positive block contributes zero negative directions.
5. Mathlib's exact block LDU identity
   `Matrix.fromBlocks_eq_of_invertible₂₂` gives

   ```text
   [ A  B  ] = P · [ A - B D⁻¹ Bᴴ   0 ] · Pᴴ,
   [ Bᴴ D  ]       [       0         D ]
   ```

   with an explicit invertible block-unitriangular `P`.
6. The preceding finite-tail leaf supplies
   `mode4ActualFiniteJacobiTruncation_tailBlock_posDef`.
7. The preceding public Schur leaf supplies the literal identity with
   `mode4BackwardTailSchurApprox`.
8. Transport across these exact matrix equalities yields the public source
   theorem above.

## Kernel validation

All commands ran from the canonical checkout on branch `rh_clean`.

```text
lake env lean Q3/Proofs/RouteB/D0Mode4HermitianNegativeCountStability.lean
PASS

lake env lean Q3/Proofs/RouteB/D0Mode4FiniteBlockInertiaAdditivity.lean
PASS

lake build Q3.Proofs.RouteB.D0Mode4FiniteBlockInertiaAdditivity
PASS (7755 jobs)

bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FiniteBlockInertiaAdditivity.lean
PASS (`q3_check ok`)

lake build
PASS (7817 jobs)
```

Printed axioms for all three new public declarations:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`; no `sorry`, `admit`, `exact?`, `unsafe`, or declared `axiom` in
the changed proof surface.

`git diff --check` passed.

The standing package warning about the separately dirty
`.lake/packages/UnicodeBasic` checkout remains unchanged and is not part of
this leaf.

## Planted guards

Scratch-only file:

`/tmp/Goal058FiniteBlockInertiaPlants.lean`

SHA-256:

`ce3c7fbbb89471091a0e70759ba7340f425f915e5b25622c958416d8e80d8b9b`

Size: 139 lines, 5379 bytes.

Direct Lean: PASS. All plant theorems print only standard axioms.

Exact codes:

1. `BLOCK_INERTIA_POSDEF_GUARD_REQUIRED`
   — the negative one-dimensional Hermitian tail has count one while the zero
   Schur cell has count zero.
2. `BLOCK_INERTIA_HERMITIAN_ONLY_MUTATION_REJECTED`
   — Hermitianity of the eliminated tail does not replace positive
   definiteness.
3. `BLOCK_INERTIA_FINITE_DOES_NOT_SUPPLY_SINGULAR_LIMIT_STABILITY`
   — `[-1/(d+1)]` has count one for every finite `d` but converges to the zero
   matrix of count zero.

These plants reject the exact unsafe mutations relevant to this leaf. They do
not claim an exhaustive test of all block-inertia statements.

## Exact consumption and remaining wall

This leaf now permits an independently sourced negative count for the literal
actual finite Jacobi truncation to be transported to the literal Schur
approximation, and conversely.

It does not provide any such source count. In particular it proves none of:

- endpoint count `2` or `3`;
- existence or location of the relevant source eigenvalue/root;
- identification with the classical degree-four even prolate mode;
- stabilization as the finite tail depth or retained cutoff grows;
- zero offset or index-four selection;
- cofinal finite simple-even ground;
- G1 or G3 closure;
- Route B or RH.

The strongest surviving G3 wall is therefore source-side: identify or prove
the required finite/infinite mode-four negative counts on the literal source
family, with the exact parameter/index crosswalk. The judge should name the
smallest next bounded theorem and decide whether this finite block-inertia
leaf is acceptable as committed.

Stop code:

`FINITE_BLOCK_INERTIA_ADDITIVITY_PROVED_SOURCE_COUNTS_AND_INDEX4_IDENTIFICATION_MISSING`
