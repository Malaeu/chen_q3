# Goal 058 G1 literal complement-floor spectral receiver — closeout

Date: `2026-08-14`

Lane: `CHALLENGER / NOT_RH`

Verdict:

```text
FINITE_CELL_CONDITIONAL_RECEIVER_PASS
G1_OPEN
```

Stop code:

```text
G1_LITERAL_COMPLEMENT_FLOOR_GRAM_CHECKER_PROVED_COFINAL_LITERAL_CCM_ARITHMETIC_AND_UNIFORM_TAIL_FLOOR_MISSING
```

## Exact input and output

Input: a Hermitian finite matrix `K`, a unit trial row `q`, its Rayleigh value
`a`, exact residual `r=Kq-aq`, and the already fixed positive predicate

```text
complexTrialComplementFloor K q a beta.
```

Output: a unit bottom eigenvector `xi0`, a global bottom Rayleigh bound, an
`xi0`-orthogonal spectral floor at `epsilon+beta`, separation of every other
eigenvalue, and the exact projective estimate

```text
1 - normSq <xi0,q> <= Re <r,r> / beta^2.
```

The literal wrapper uses without replacement:

- `D0Pstar.sourceCCMFiniteMatrix i`;
- `D0Pstar.sourceCCMComplexRow S i`;
- `D0Pstar.sourceCCMFiniteRayleigh S i`;
- `D0Pstar.sourceCCMFiniteResidual S i`;
- `sourceCCMComplexTrialComplementFloor S i beta`.

## Kernel-checked suppliers

Files:

- `Q3/Proofs/RouteB/HermitianUnitMinimumEigenpair.lean`;
- `Q3/Proofs/RouteB/CCMProposition59ComplexTrialComplementRayleigh.lean`;
- `Q3/Proofs/RouteB/CCMProposition59ComplexTrialResidualTracking.lean`;
- `Q3/Proofs/RouteB/CCMProposition59ComplexTrialComplementSpectral.lean`.

Public heads:

- `hermitian_exists_unit_minimum_eigenpair`;
- `hermitian_unit_trialLine_complementFloor_gives_orthogonalRayleigh`;
- `hermitian_unit_eigen_projective_defect_le_residual_sq_div_beta_sq_of_orthogonal_floor`;
- `hermitian_unit_trialLine_floor_separates_eigenvalues`;
- `hermitian_unit_trialLine_complementFloor_gives_ground_gap_tracking`;
- `sourceCCMFinite_simpleGround_gap_tracking_of_complementFloor`.

The receiver constructs the minimum eigenpair from Mathlib's finite Hermitian
eigenbasis.  It does not add an eigenpair, simplicity, gap, or source theorem
as an assumption.  Its only project-specific quantitative input is the named
literal complement floor.

## Why this is the correct finite receiver

The proof promotes the floor on `q^perp` to a strong floor on `xi0^perp` by an
explicit two-plane combination.  Hermitian cross terms cancel exactly.  The
remaining residual is decomposed into its ground component and orthogonal
component; finite Hilbert-space Cauchy--Schwarz then gives the squared
projective defect.  A separate codimension-one argument proves that every
eigenvalue different from the bottom lies above `a+beta`.

This is stronger than merely naming a lowest eigenvalue, and it is exactly the
receiver demanded by the Goal 058 architecture once a literal positive floor
has been produced.

## Knowledge preflight

The Oracle record at `Goal058.G1.CofinalComplementFloor` contains the three
consecutive searches:

1. `hermitian unit trial line complement floor ground gap tracking`;
2. `codimension one interlacing complex trial complement Rayleigh floor`;
3. `sourceCCMFinite simple ground gap tracking of complement floor`.

No complete project supplier was found.  The local implementation closes the
finite receiver and leaves only the source-arithmetic supplier active.

## Validation

- direct `lake env lean` for all four files: `PASS`;
- target builds: `PASS`;
- public axiom surface: exactly
  `[propext, Classical.choice, Quot.sound]`;
- `sorryAx`: absent;
- forbidden-token scan: `PASS`;
- `git diff --check`: `PASS`.

The full build, `q3_check`, semantic refresh, strict startup, and Route B check
are run as the closing transaction and recorded in the session protocol.

## What remains

The receiver consumes but does not produce `beta`.  G1 still requires literal
CCM arithmetic on one precommitted cofinal family, including a finite-head
certificate and a Lean-checked uniform tail reduction yielding an explicit
positive floor.  The same-family residual must then beat that floor on the
same schedule.

## Nonclaims

```text
NO_G1
NO_G3
NO_ROUTE_B_PROMOTION
NO_RH
```
