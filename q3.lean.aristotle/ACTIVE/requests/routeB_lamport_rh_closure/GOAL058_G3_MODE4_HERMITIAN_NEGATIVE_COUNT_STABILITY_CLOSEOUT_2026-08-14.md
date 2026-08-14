# Goal 058 G3 mode-four Hermitian negative-count stability — closeout

Date: `2026-08-14`

Status: `G3_HERMITIAN_NEGATIVE_COUNT_EVENTUAL_STABILITY_PROVED_EXACT_CONTRACT`

Operative class: `TRY_MODE4_HERMITIAN_NEGATIVE_COUNT_STABILITY`

This is the one-file / one-report bounded leaf authorized by the Proshka
finite-limit inertia verdict.  It is infrastructure only.

## Source lock

- source packet:
  `GOAL058_G3_CLASSICAL_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_SOURCE_PACKET_2026-08-14.md`
- source packet SHA-256:
  `2f8072b247e846641b7923974309bc76986108cf0779424c678ee878eae54f14`
- Mythos verdict:
  `GOAL058_G3_FINITE_LIMIT_SOURCE_FORK_MYTHOS_VERDICT_2026-08-14.md`
- Mythos verdict SHA-256:
  `42e98afbe8fad2e40239172620c472d464e5910dcf42593385cdcf9a6fc07f33`
- judge capture:
  `GOAL058_G3_FINITE_LIMIT_INERTIA_ROUTE_PROSHKA_VERDICT_2026-08-14.md`
- repair verdict:
  `GOAL058_G3_MODE4_HERMITIAN_NEGATIVE_COUNT_STABILITY_PROSHKA_REPAIR_VERDICT_2026-08-14.md`

## Owned Lean file

`Q3/Proofs/RouteB/D0Mode4HermitianNegativeCountStability.lean`

Direct project import:

`Q3.Proofs.RouteB.D0Mode4SchurInertiaOrientation`

## Proved leaf

```lean
theorem mode4HermitianNegativeEigenvalueCount_eventually_eq_of_tendsto_of_det_ne_zero
    {K : ℕ}
    (A : ℕ → Matrix (Fin K) (Fin K) ℝ)
    (hA : ∀ d, (A d).IsHermitian)
    (L : Matrix (Fin K) (Fin K) ℝ)
    (hL : L.IsHermitian)
    (hlim : Tendsto A atTop (𝓝 L))
    (hdet : L.det ≠ 0) :
    ∀ᶠ d in atTop,
      mode4HermitianNegativeEigenvalueCount (A d) (hA d) =
        mode4HermitianNegativeEigenvalueCount L hL
```

The theorem uses the exact current project invariant
`mode4HermitianNegativeEigenvalueCount` and the exact Hermitian surface
`Matrix.IsHermitian`.  Its public head contains no positive-dimension binder.
The `K = 0` branch proves both counts zero directly; a private helper retains
the positive-dimension spectral-gap proof.

## Proof architecture

1. Diagonalize the nonsingular Hermitian limit and take the minimum absolute
   eigenvalue as a positive spectral gap.
2. Build its negative and positive spectral projectors.
3. Bound a quadratic-form perturbation by
   `K * ‖A d - L‖ * ‖x‖²` using the elementwise matrix norm.
4. For all sufficiently large `d`, preserve negative definiteness on the
   fixed negative subspace and positive definiteness on the fixed positive
   subspace.
5. Apply finite-dimensional subspace/rank bounds to obtain lower bounds for
   both the negative and positive counts of `A d`.
6. Use eventual nonsingularity from determinant continuity.  Negative plus
   positive multiplicity is then exactly `K`, so both lower bounds force
   equality of the negative counts.

No continuity of Mathlib's chosen eigenvalue labels is assumed.

## Required plant suite

All plant material is private, so it does not enlarge the production API.

1. `P-STAB-1-SINGULAR-LIMIT`: the one-dimensional sequence
   `[-1/(d+1)]` has count `1`, converges to zero, and zero has count `0`.
   Hence `L.det ≠ 0` is load-bearing.
2. `P-STAB-2-DETERMINANT-TENDSTO`: alternating `-I₂` and `I₂` matrices
   have constant determinant `1` but counts `2` and `0`.  Determinant
   convergence does not replace matrix convergence.
3. `P-STAB-3-DETERMINANT-SIGN`: `diag(-1,-1,1)` and `I₃` both have
   determinant `1`, while their exact project counts are `2` and `0`.
   Determinant sign is not an inertia count.
4. `P-STAB-4-HERMITIAN-GUARD`: the real nonsymmetric rotation matrix is
   proved not `Matrix.IsHermitian`.
5. `P-STAB-5-FIXED-CARRIER`: no single `Fin K` can be equivalent to every
   `Fin (d+1)`; a varying-carrier family cannot instantiate the fixed-`K`
   theorem directly.

The file contains all five required stop codes:

```text
G3_INERTIA_STABILITY_SINGULAR_LIMIT_GUARD_DROPPED
G3_INERTIA_STABILITY_MATRIX_TENDSTO_REPLACED_BY_DET
G3_INERTIA_STABILITY_DET_SIGN_NOT_COUNT
G3_INERTIA_STABILITY_HERMITIAN_GUARD_DROPPED
G3_INERTIA_STABILITY_FIXED_CARRIER_DROPPED
```

## Kernel checks

Direct Lean:

```text
lake env lean Q3/Proofs/RouteB/D0Mode4HermitianNegativeCountStability.lean
exit 0
```

Target build:

```text
lake build Q3.Proofs.RouteB.D0Mode4HermitianNegativeCountStability
Build completed successfully (7750 jobs).
```

Full build:

```text
lake build
Build completed successfully (7817 jobs).
```

Repository checker:

```text
bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4HermitianNegativeCountStability.lean
q3_check ok
```

The single public theorem prints only:

```text
[propext, Classical.choice, Quot.sound]
```

The public surface audit finds exactly one public theorem and zero public
definitions.  The forbidden-token scans find no `sorry`, `admit`, `exact?`,
`native_decide`, new `axiom`, or `opaque`.  `git diff --check` passes for all
three owned repair artifacts.

## Exact boundary after the leaf

```yaml
GENERIC_LEAF_5: PROVED_EXACT_AUTHORIZED_CONTRACT
EXACT_AUTHORIZED_HEAD: PASS
PUBLIC_THEOREMS: 1
PUBLIC_DEFINITIONS: 0
PLANTS: 5_OF_5_PASS
SINGULAR_LIMIT_GUARD: LOAD_BEARING
MATRIX_TENDSTO_NOT_DET_TENDSTO: PASS
DET_SIGN_NOT_EXACT_COUNT: PASS
HERMITIAN_GUARD: PASS
FIXED_CARRIER_GUARD: PASS
FINITE_DLMF_MATRIX_TO_LITERAL_SCHUR_CROSSWALK: OPEN
POSITIVE_TAIL_HAYNSWORTH_CONGRUENCE: OPEN
FIXED_CARRIER_EXACT_TAIL_CONVERGENCE: OPEN
OFFSET_ZERO: NOT_PROVED
ENDPOINT_COUNTS_2_3: NOT_AVAILABLE
G1: OPEN
G3: OPEN
ROUTE_B_PROMOTION: FORBIDDEN
RH_CLAIM: FORBIDDEN
```

No commit, push, next crosswalk leaf, Route state, runtime state, or Bus
mutation was performed by this bounded repair.
