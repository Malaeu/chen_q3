# Codex source record — Goal 058 selected even-sector Arch-Prime reduction

```yaml
schema: q3_codex_source_record.v1
date: 2026-09-01
branch: rh_clean
implementation_parent: c937978cd26e66d3426c13b7ba3cd51de362fe0f
source_commit: 47a9350986db5b7d257ee03fc2e0ece181adcb92
status: KERNEL_GREEN_AWAITING_INDEPENDENT_SEMANTIC_ADMISSION
node: SELECTED_FERRERS_EVEN_SECTOR_ARCH_PRIME_REDUCTION
route: CHALLENGER_NOT_RH
route_promotion: false
rh_claim: false
```

## Scoped source bytes

```yaml
task:
  path: docs/Codex/TASK_2026-09-01_goal058_selected_even_arch_prime_reduction.md
  git_blob: f17f76aa08d2cfbf4b7dbed5b23dceb73bca9ce2
  sha256: a8e622b3018b3d5077b062733b5e563f97574a3b1ea9e6e50461e061cf015df5
  bytes: 4269
  lines: 119
  final_lf: true
primary_source:
  path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersEvenSectorArchPrimeReduction.lean
  git_blob: 255131af8f3202b45b909c67fe548facaa4a4956
  sha256: 39ce32ce5e0a325d9740f0dc98630e9cdf4c7f8dfd6404cb0b3e9c6d62bed2c6
  bytes: 17580
  lines: 426
  final_lf: true
```

## Result

The literal finite CCM `W02` matrix is factored as one reflection-even
rank-one form minus one reflection-odd rank-one form.  The odd coordinate
annihilates every exact reflection-even complex coefficient vector, leaving

```text
32 * L * sinh(L / 4)^2 * |a dot x|^2 >= 0.
```

The full source quadratic form is then identified exactly as

```text
W02 + Arch - Prime,
```

with the selected Rayleigh scalar subtracted exactly once.  Therefore an
eventual shifted `Arch - Prime` floor on the literal selected reflection-even
row complement implies the downstream consumer's exact `heven` floor with the
same carrier, equations, scalar, beta, and eventual quantifier.

Public theorem surface:

```text
Q3.RouteB.D0Pstar.ccmW02Quadratic_re_nonneg_of_reflection_even
Q3.RouteB.D0Pstar.sourceCCMFiniteMatrix_shifted_floor_of_archPrimeShifted_floor_even
Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMEvenSectorFloor_eventually_of_archPrimeShifted
```

## Gates

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

```text
CLOSES:
  SELECTED_FERRERS_EVEN_SECTOR_W02_POSITIVITY
  SELECTED_FERRERS_EVEN_SECTOR_ARCH_PRIME_REDUCTION

OPENS:
  SELECTED_N_EVEN_RETAINED_PRIME_SHIFTED_QUADRATIC_FLOOR
```

## Hypothesis provenance

```json
[
  {
    "class": "NEW_OPEN_OBLIGATION",
    "consumer": "Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMEvenSectorFloor_eventually_of_archPrimeShifted",
    "exact_type": "forall-eventually k atTop, for every reflection-even x orthogonal to the exact symmetrized selected row, beta times re(star x dot x) is at most re(sourceArchPrimeSesquilinearForm i_k x x - selectedFerrersFiniteCCMRayleigh P k times (star x dot x))",
    "hypothesis_id": "SELECTED_N_EVEN_RETAINED_PRIME_SHIFTED_QUADRATIC_FLOOR_INPUT",
    "open_obligation_id": "SELECTED_N_EVEN_RETAINED_PRIME_SHIFTED_QUADRATIC_FLOOR",
    "production_inhabitant_or_plant": {
      "blob": "255131af8f3202b45b909c67fe548facaa4a4956",
      "declaration": "selectedFerrersArchPrimeShifted_zero_reachability_plant",
      "exact_type": "for every fixed selected port P, cell k, and real beta, there exists x in the exact selected CCMModeFinite carrier satisfying the literal reflection-even equation, exact selected-row-complement orthogonality, and selected-Rayleigh-shifted Arch-Prime inequality",
      "kind": "REACHABILITY_PLANT",
      "path": "q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersEvenSectorArchPrimeReduction.lean",
      "scope": "POINTWISE_ZERO_VECTOR_REACHABILITY_OF_EXACT_SELECTED_ARCHPRIME_ANTECEDENT_SHAPE_ONLY",
      "verifier": "LEAN_KERNEL_AND_INDEPENDENT_SEMANTIC_DELTA_REVIEW"
    },
    "source_or_supplier": "open selected reflection-even Arch-Prime shifted floor at the exact selected Rayleigh scalar"
  }
]
```

```yaml
hypothesis_provenance_sha256: 00eeb8a9adaea9aa686e6d831678992e23d310743dc65c9f6ffcaf15cc95ff5a
```

The reachability plant proves only pointwise zero-vector reachability of the
exact antecedent shape.  It provides no nonzero vector, positive margin,
positive beta, universal floor, or eventual uniformity and does not inhabit
the open supplier.

This package is kernel-green only.  Its declarations must not be consumed by
a later source theorem until an external `q3_semantic_attestation.v1` receipt
admits the exact narrow scope.

`PX_RH_CLAIM: NOT_MADE`.
