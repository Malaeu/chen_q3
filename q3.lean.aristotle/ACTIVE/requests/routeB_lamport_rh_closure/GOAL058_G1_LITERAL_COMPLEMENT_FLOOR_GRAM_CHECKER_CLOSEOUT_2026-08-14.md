# Goal 058 G1 literal complement-floor Gram checker — closeout

Date: `2026-08-14`

Lane: `CHALLENGER / NOT_RH`

Verdict:

```text
FINITE_CELL_CONDITIONAL_CHECKER_PASS
G1_OPEN
```

Stop code:

```text
G1_LITERAL_COMPLEMENT_FLOOR_GRAM_CHECKER_PROVED_COFINAL_LITERAL_CCM_ARITHMETIC_AND_UNIFORM_TAIL_FLOOR_MISSING
```

## Exact object fixed

The checked predicate is the positive lower floor of the shifted complement
block of one complex unit trial line:

```text
Q = I - q q^*
B = Q (K - a I) Q
beta ||Qx||^2 <= Re <Qx, Bx>,   beta > 0.
```

The source specialization uses, without replacement:

- `D0Pstar.sourceCCMFiniteMatrix i`;
- `D0Pstar.sourceCCMComplexRow S i`;
- `D0Pstar.sourceCCMFiniteRayleigh S i`;
- `sourceCCMComplexTrialComplementBlock S i`.

This is the literal complex P59 trial-line object, not a parity surrogate and
not a newly strengthened source family.

## Kernel-checked suppliers

File:
`Q3/Proofs/RouteB/CCMProposition59ComplexTrialComplementFloor.lean`.

Public heads:

- `complexTrialComplementFloor`;
- `sourceCCMComplexTrialComplementFloor`;
- `complexTrialComplementFloor_of_gramCertificate`;
- `sourceCCMComplexTrialComplementFloor_of_gramCertificate`.

The certificate theorem consumes the exact equality

```text
B - beta Q = R^* R
```

with `beta > 0` and the already proved unit norm of the source row.  It then
derives the floor from `Matrix.posSemidef_conjTranspose_mul_self`.  The theorem
does not assert that `R` or `beta` exists.

## Permanent falsifier

The same file contains an exact `Fin 3` plant with

```text
D = diag(-1,0,1),
K = all-ones,
eta = (1,1,1),
ccmBeta = (-1,0,1).
```

Lean proves the source-shaped rank-two commutator identity exactly.  A
rational complex unit ground vector `q` is selected, and a second explicit
nonzero ground vector `y` is proved orthogonal to `q`.  Consequently:

- `goal058ComplementFloorCollapse_no_positive_floor` rejects every
  `beta > 0`;
- `goal058ComplementFloorCollapse_no_gramCertificate` rejects every proposed
  Gram factorization at a positive floor.

This kernel-checks the decision that rank-two commutation and the present
`ccmBeta` identities cannot by themselves supply G1.

## Knowledge preflight

Three consecutive `ask.sh` queries were recorded at
`Goal058.G1.LiteralComplementFloor.GramChecker`:

1. `sourceCCMComplexTrialComplementFloor exact Gram certificate`;
2. `literal complex trial line complement floor Feshbach residual beta`;
3. `rank two commutator collapse ground kernel dimension two complement floor`.

They found no pre-existing literal supplier.  The resolved local checker and
its next address are recorded in
`ACTIVE/pipeline/oracle_questions/2026_08_14_goal058_g1_literal_complex_trial_complement_floor_gram_checker.md`.

## Validation

- direct `lake env lean`: `PASS`;
- target `lake build Q3.Proofs.RouteB.CCMProposition59ComplexTrialComplementFloor`:
  `PASS` (`7794` jobs);
- `scripts/q3_check.sh`: `PASS`;
- full `lake build`: `PASS` (`7817` jobs);
- forbidden-token scan: `PASS`;
- forbidden-claim scan: `PASS`;
- `git diff --check`: `PASS`;
- public axiom surface: exactly
  `[propext, Classical.choice, Quot.sound]`;
- `sorryAx`: absent.
- semantic-index refresh: `PASS` (`2694` indexed files);
- strict startup:
  `P9_STRICT_PASS ... base_control=PASS semantic_index=PASS tool_manifest=PASS`;
- Route B check:
  `GOAL_058_G3_PROLATE_RATE_AND_FLOOR_OPEN / NOT_RH / ALPHA_ROUTE_REMAINS_CHALLENGER`.

## What remains

The next address is `Goal058.G1.CofinalComplementFloor`.  It must produce an
explicit positive floor for the literal CCM arithmetic on one precommitted
cofinal family, with a finite-head certificate and a Lean-checked uniform tail
reduction.  The already checked same-family residual and projective receivers
can only be consumed after that supplier exists.

## Nonclaims

```text
NO_G1
NO_G3
NO_ROUTE_B_PROMOTION
NO_RH
```
