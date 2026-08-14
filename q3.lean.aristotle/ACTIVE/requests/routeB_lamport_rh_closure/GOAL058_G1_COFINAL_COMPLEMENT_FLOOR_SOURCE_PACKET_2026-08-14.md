# Goal 058 G1 — cofinal literal complement-floor source packet

Date: `2026-08-14`

Status: `SOURCE_PACKET_READY_FOR_PROSHKA_REVIEW_G1_OPEN`

Boundary: exact object inventory, mismatch proof, and noncircular source
contract only. This packet does not produce a positive complement floor, a
cofinal gap, an even ground, projective convergence, G1/G3 closure, Route B
promotion, or an RH claim.

## Exact production object

For `S : D0Pstar.ProlateCanonicalSourceData` and `i : PairIndex`, set

```text
K = sourceCCMFiniteMatrix i,
q = sourceCCMComplexRow S i,
a = sourceCCMFiniteRayleigh S i,
Q = I - |q><q|.
```

The production predicate is exactly

```lean
sourceCCMComplexTrialComplementFloor S i beta
```

meaning

```text
beta > 0,
beta ||Qx||^2 <= Re <Qx, Q(K-aI)Q x>  for every complex x.
```

The exact finite Feshbach identity and full spectral receiver are already
kernel checked. In particular,

```lean
sourceCCMFinite_simpleGround_gap_tracking_of_complementFloor
```

turns this one predicate into a unit minimum eigenpair, a gap at least `beta`,
and

```text
1 - |<xi0,q>|^2 <= ||sourceCCMFiniteResidual S i||^2 / beta^2.
```

The receiver consumes the floor. It supplies no `beta`, certificate, parity,
source schedule, or residual rate.

## Existing exact checker and permanent falsifier

`CCMProposition59ComplexTrialComplementFloor.lean` proves the exact Gram
certificate checker

```text
Q(K-aI)Q - beta Q = R^* R,  beta > 0
  -> sourceCCMComplexTrialComplementFloor S i beta.
```

It does not assert that `R` or `beta` exists.

The same file contains a kernel-checked `Fin 3` all-ones plant satisfying the
source-shaped rank-two commutator identity while possessing a second ground
vector in `q^perp`. It rejects every positive floor and every corresponding
Gram factorization. Therefore commutator shape and the current `ccmBeta`
identities cannot produce G1 by themselves.

## Overlooked on-disk odd-tail supplier

The repo-wide audit found a real supplier that was not in the latest G1
ledger:

```lean
sourceWeilOddTailAmbientCoercive_explicit (i : PairIndex)
```

in `D0PstarSourceWeilOddTailExplicitCoercivity.lean`. It gives the explicit
floor `1/2` on the literal closed high odd graph tail for every `PairIndex`.

The target shift

```text
sourceWeilOddTargetFloor = 10^(-58)
```

is then transferred to positivity and invertibility of the odd tail in
`D0PstarSourceWeilOddTargetFloorSchurReduction.lean`.

The fixed-cell receiver

```lean
sourceWeilOddTargetFloorSchurPositive13_iff_ccm_corrected_energy
```

exposes `m=13` odd Schur positivity as nonnegativity of a corrected finite CCM
energy. It is an `iff`; it does not prove the sign.

## Why this does not specialize to the production floor

The specialization fails in six independent dimensions.

1. **Carrier.** The supplier floors a closed odd-tail subspace of an
   infinite graph Hilbert space. The target is the rank-one complement of a
   trial line in the finite complex space indexed by `CCMModeFinite i.N`.
   The odd-tail lane is trial-blind: `q` does not occur.
2. **Operator.** The fixed receiver uses
   `ccmWeilMatFinite 13 (sourceWeilOddTailCutoff ...)`; the target uses
   `sourceCCMFiniteMatrix i`. No theorem identifies these matrices for the
   changing schedule parameters.
3. **Shift.** The odd lane subtracts the fixed
   `sourceWeilOddTargetFloor`. The target subtracts the `S`- and `i`-dependent
   Rayleigh value `a`. The exact identity is

   ```text
   B(a) = B(a*) - (a-a*) Q.
   ```

   Every unit of shift error consumes one unit of floor.
4. **Sector.** Odd-tail coercivity says nothing about the even directions in
   `q^perp`. Those directions contain the same-parity competitor governing
   the actual spectral gap.
5. **Schedule.** The supplier is `i`-generic, but the corrected-head receiver
   is fixed at `m=13`. Quantification over its auxiliary `N` does not make a
   single `m=13` fiber cofinal when the frozen schedule has increasing
   physical bandwidth and changing source cells.
6. **Modality.** A tail sign plus an unsigned `iff` exposing a head sign is not
   a positive floor on the full complement.

Consequently no theorem composition currently yields
`sourceCCMComplexTrialComplementFloor` from the odd-tail lane.

## Parity and gap are different obligations

For a reflection-commuting Hermitian matrix, a simple eigenvector has definite
parity, but its parity can be even or odd. The exact `Fin 2` mutation

```text
J = swap,
K = [[0,1],[1,0]]
```

has a simple odd ground. Thus

```text
simple + reflection commuting -> even ground
```

is false.

If the source row is exactly even and the full complement floor plus
`||r||^2/beta^2 < 1` are proved, then the receiver gives a simple ground with
nonzero overlap with the even row; an odd ground would have zero overlap, so
evenness follows downstream. This does not remove the odd lower-bound
obligation: the full floor includes the entire odd sector inside `q^perp`.

Exact evenness of `sourceCCMComplexRow` is itself not exported by the present
source contract. The tree only proves

```lean
sourceCCMComplexRow_even_of_phaseRealification_even
```

from a supplied phase-realification and even real row. Any production
sector-split theorem must either prove those source inputs or carry an honest
odd-contamination error term.

## Sector-split noncircular route

Assuming exact evenness of `q`, reflection invariance splits

```text
q^perp = (even ∩ q^perp) ⊕ odd,
```

and the full floor is the minimum of two floors:

```text
even-complement floor,
odd-sector minimum relative to the same Rayleigh shift a.
```

The smallest source-faithful carrier package has three one-way legs.

### C1 — uniform odd leg

- generalize the fixed-`m=13` corrected-head receiver to the actual schedule;
- bound the inverse-weighted Schur correction by the head-tail coupling using
  the existing tail floor `1/2`;
- prove one uniform corrected-head lower bound for every sufficiently large
  schedule cell.

The exact generic correction is

```lean
oddTailInverseWeightedCorrection D = R^* C^(-1) R.
```

The queued bounded theorem is a quadratic-form estimate of the shape

```text
Re <oddTailInverseWeightedCorrection D x, x>
  <= 2 * ||D.residual x||^2
```

when the outer block has the existing coercive floor `1/2`. This is a useful
receiver leaf, not the missing uniform corrected-head sign.

### C2 — even leg

- prove an even-tail coercivity twin of the odd supplier;
- prove a uniform even-head complement floor at an explicit fixed shift `a*`
  with a fixed `beta* > 0`.

The current low-band square estimate is odd-specific even though the
archimedean multiplier bound is parity-agnostic. The even low-band lemma and
the uniform even-head arithmetic are absent.

### C3 — shift and cofinal link

Prove eventually

```text
|sourceCCMFiniteRayleigh S i_j - a*| <= beta*/2.
```

Then the exact shift identity gives a literal floor at the Rayleigh shift of
at least `beta*/2`. With a fixed positive lower bound, the projective ratio

```text
||sourceCCMFiniteResidual S i_j|| / beta_j
```

tends to zero as soon as the independently proved source residual tends to
zero. The dependency is one-way: G3/source approximation may supply the
Rayleigh/residual rate to G1, but G1 is not used to manufacture that rate.

## Exact next Lean boundary

The full source supplier is not theorem-head ready:

```text
EXACT_NEXT_LEAN_HEAD: NOT_READY
```

The first locally bounded receiver leaf can be investigated under the exact
`OddTailInverseWeightedData` API:

```text
sourceWeilOddTailInverseWeightedCorrection_quadraticForm_le
```

but it must not be misnamed as G1 progress beyond the odd Schur correction.
After it, the genuine new source leaves are the even low-band/tail theorem and
the uniform corrected-head schedule family.

## Planted falsifiers

1. **Parity sign mutation:** the `Fin 2` commuting example above rejects
   simple-plus-symmetry as an even-ground supplier.
2. **Tail-to-complement mutation:** take the existing `Fin 3` collapse plant
   direct-summed with a positive identity tail. The tail has a positive floor,
   while the old second ground vector remains in `q^perp` and rejects every
   positive complement floor.
3. **Shift mutation:** for `K=diag(0,1)` and `q=e0`, the Rayleigh-shifted
   complement floor is `1`; replacing the shift by the scalar `1` makes the
   complement energy zero. This rejects substitution of the fixed target
   floor for the literal Rayleigh value.

Any schedule-quantified conclusion containing an unexplained fixed `13` is a
registered schedule-leak reject.

## Aristotle boundary

```text
ARISTOTLE_BOUNDARY: NOT_AUTHORIZED
```

The correction bound and even-tail supplier are project-internal
infinite-dimensional theorems, not bounded certificate cells. A future exact
rational Gram factorization of one fully specified corrected finite head may
be Aristotle-eligible only after the analytic tail/correction bounds and
literal entries are already supplied locally.

## Requested Proshka verdict

Return exactly:

1. `PRIMARY_VERDICT`: `ACCEPT`, `REVISE`, or `REJECT` for this G1 source
   packet;
2. `OVERLOOKED_SUPPLIER_CHECK`;
3. `OBJECT_MISMATCH_CHECK` for all six mismatch dimensions;
4. `SECTOR_SPLIT_CHECK`, including the row-evenness prerequisite;
5. `MINIMAL_NEW_CARRIER` and whether C1--C3 are noncircular;
6. `EXACT_NEXT_LEAN_HEAD` or `NOT_READY`;
7. `ARISTOTLE_BOUNDARY`;
8. `G1_STATUS`, `G3_STATUS`, and one typed `STOP_CODE`.

## Packet stop code

```text
G1_ODD_TAIL_SUPPLIER_RECOVERED_FULL_COMPLEMENT_FLOOR_MISSING_EVEN_HEAD_SHIFT_AND_COFINAL_CONNECTOR_OPEN
```
