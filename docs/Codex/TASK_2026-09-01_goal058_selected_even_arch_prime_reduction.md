# Codex task — Goal 058 selected even-sector Arch-Prime reduction

Date: 2026-09-01
Status: `KERNEL_GREEN_SOURCE_PACKAGE`
Parent: Goal 058 / exact selected reflection-even sector floor

## Exact outcome

Remove the favorable finite `W02` component from the exact selected
reflection-even floor ledger without changing the downstream carrier,
row-complement equation, scalar, or quantifiers:

1. factor the literal finite CCM `W02` matrix as an even rank-one form minus
   an odd rank-one form;
2. prove that the odd coordinate vanishes on the exact reflection-even
   complex carrier;
3. prove nonnegativity of the surviving `W02` quadratic form for arbitrary
   complex coefficients;
4. identify the full shifted source quadratic form as `W02` plus shifted
   `Arch - Prime`;
5. transport an eventual shifted `Arch - Prime` floor to the exact `heven`
   hypothesis consumed by H2A.4.1B.2.

Primary source:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersEvenSectorArchPrimeReduction.lean
```

## Public theorem surface

```text
Q3.RouteB.D0Pstar.ccmW02Quadratic_re_nonneg_of_reflection_even
Q3.RouteB.D0Pstar.sourceCCMFiniteMatrix_shifted_floor_of_archPrimeShifted_floor_even
Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMEvenSectorFloor_eventually_of_archPrimeShifted
```

## Exact consumer

```text
Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual
```

The selected adapter preserves literally:

- `CCMModeFinite` for the same selected `PairIndex` and cell `k`;
- `ccmComplexReflectionMatrix ... *ᵥ x = x`;
- orthogonality to the exact symmetrized selected row;
- the same real floor `beta`;
- one common eventual-atTop quantifier;
- `selectedFerrersFiniteCCMRayleigh P k` as the exact shift;
- `sourceCCMFiniteMatrix` at the same selected index.

## Exact scope

```text
CLOSES:
  SELECTED_FERRERS_EVEN_SECTOR_W02_POSITIVITY
  SELECTED_FERRERS_EVEN_SECTOR_ARCH_PRIME_REDUCTION

OPENS:
  SELECTED_N_EVEN_RETAINED_PRIME_SHIFTED_QUADRATIC_FLOOR
```

The second close is an exact conditional reduction interface, not a proof of
its open antecedent.

## Hypothesis provenance boundary

The eventual uniform shifted `Arch - Prime` floor is classified as
`NEW_OPEN_OBLIGATION` and appears in `OPENS`.  The private Lean plant
`selectedFerrersArchPrimeShifted_zero_reachability_plant` proves only
pointwise zero-vector reachability of the exact antecedent shape.  For every
fixed selected port `P`, cell `k`, and real `beta`, the zero vector satisfies
the literal reflection equation, row-complement orthogonality equation, and
shifted inequality as `0 ≤ 0`.

The plant supplies no nonzero vector, positive norm or margin, beta
positivity, universal floor over admissible vectors, or eventual-atTop
uniformity.  It does not inhabit or imply the open supplier.

## Non-goals and forbidden inferences

This task does not prove:

- `W02` nonnegativity outside the reflection-even sector;
- positive definiteness or a uniform coercivity constant for `W02`;
- the converse from the full floor to the `Arch - Prime` floor;
- the retained-prime shifted floor itself;
- an odd-sector floor, weighted residual decay, or a complement floor;
- a selected Rayleigh upper envelope, simple ground, real zeros, or RH.

Prime tail-norm decay, separate absolute absorption of Prime, and an
unshifted-to-shifted inference without the exact Rayleigh scalar remain
forbidden routes.

## Verification

```text
direct Lean: PASS
target build: PASS (7971/7971 jobs)
q3_check: PASS
source scan: no sorry, admit, exact?, native_decide, unsafe, or new axiom
public axioms: [propext, Classical.choice, Quot.sound]
git diff --check: PASS
independent semantic review: PASS
independent reachability-plant delta review: PASS_WITH_EXACT_SCOPE_LOCK
```

## Semantic quarantine

Kernel acceptance is not semantic admission.  Register exactly one
`KERNEL_GREEN` entry bound to the committed task/source bytes, theorem IDs,
terminal consumer, exact scope, normalization, domain, quantifiers, and
canonical hypothesis-provenance digest.  Do not consume this package in a
later theorem until an external `q3_semantic_attestation.v1` receipt admits
the exact narrow scope.

Route status remains `CHALLENGER / NOT_RH`; `PX_RH_CLAIM: NOT_MADE`.
