# Route B L0c generic zero transfer — revision 18

Status: `L0C1_PROVED / EXACT_FAMILY_INSTANTIATION_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + REPRESENTATION_PROGRESS`

This transaction proves the generic analytic theorem required by the existing
`ZerosApproachOn` interface and splits the exact Route B obligation from that
reusable theorem.  It does not select the master approximant family, identify
the H3 limit with `centeredXi`, close `L0c`, create Bus 010, or prove RH.

## 1. Exact theorem proved in Lean

For an open set `U`, a target set `S subset U`, entire approximants `F n`, a
nonzero entire limit `f`, and locally uniform convergence of `F n` to `f` on
`U`, the theorem

```text
zerosApproachOn_of_tendstoLocallyUniformlyOn
```

proves

```text
ZerosApproachOn S F f.
```

Thus every zero `z0` of `f` in `S` has a sequence `w n -> z0` such that
`F n (w n) = 0` for every sufficiently large original index `n`.  This is a
full-tail statement, not merely a subsequence statement.

## 2. Quantitative one-disk transfer

The local engine is

```text
exists_zero_closedBall_of_uniform_close.
```

Assume `f(z0)=0`, `||f|| >= epsilon` on the boundary circle, and an entire
function `g` is within `epsilon/4` of `f` on the closed disk.  The proof obtains
boundary separation for `g-g(z0)`, rules out local constancy by the analytic
identity theorem, and applies

```text
DiffContOnCl.ball_subset_image_closedBall
```

to place zero in the image of the closed disk.  This is the exact local
existence statement needed here; no unproved Rouché or Hurwitz theorem is
imported.

## 3. Isolated zeros and locally uniform convergence

For a zero of the nontrivial entire limit, Mathlib's isolated-zero dichotomy
rules out additional zeros in a sufficiently small punctured neighborhood.
Compactness of a boundary circle then supplies a strictly positive minimum of
`||f||`.  Openness of `U` keeps the chosen closed disk inside the convergence
domain, and locally uniform convergence supplies the `epsilon/4` bound on that
disk.  Therefore, for every prescribed radius `R>0`, sufficiently large
approximants have a zero in `closedBall z0 R`.

## 4. Full-tail diagonal selection

The helper

```text
exists_tendsto_of_eventually_exists_closedBall
```

extracts a threshold `N(k)` for each radius `1/(k+1)`.  At index `n` it chooses
the largest certified scale

```text
level(n) = Nat.findGreatest (fun k => N(k) <= n) n.
```

Every fixed `k` is eventually admissible, hence `level(n) -> infinity`; the
chosen radii tend to zero and the selected roots converge to `z0`.  This
discharges the former `L0C_ZERO_SEQUENCE_SELECTION_GAP` without changing the
index filter or passing to a hidden subsequence.

Verdict: `GENERIC_ROUCHE_HURWITZ_ZERO_TRANSFER_LEAN`.

## 5. Honest DAG split

`L0c RoucheHurwitzZeroTransfer` is now an AND node:

```text
L0c
|-- L0c1 GenericLocallyUniformZeroTransfer       PROVED
|-- L0c2 ExactRouteBFamilyInstantiation          OPEN / INELIGIBLE
`-- L0c3 L0cAssembly                             OPEN / INELIGIBLE
```

The definitional contract `L0c.0` is PROVED.  `L0c2` must still instantiate
the theorem with the one exact Route B family, the exact compact-substrip
domain, and `centeredXi`, with the same natural-number/cofinal filter used by
H1, H3, and H4.  In particular it may not identify the raw and completed
trackers, invent a selector, or silently repair `XI_LIMIT_OBJECT_MISMATCH`.

Residual exact stop:

```text
L0C_EXACT_FAMILY_INSTANTIATION_MISSING
```

## 6. Lean and route boundary

Proof artifact:

```text
Q3/Proofs/RouteB/GenericZeroTransfer.lean
```

The file compiles without `sorry`, `admit`, or `exact?`.  Every printed axiom
set is exactly within the project allowance:

```text
propext, Classical.choice, Quot.sound.
```

The canonical ACTIVE leaf remains `D0.7e.5a`, the scheduler stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.
