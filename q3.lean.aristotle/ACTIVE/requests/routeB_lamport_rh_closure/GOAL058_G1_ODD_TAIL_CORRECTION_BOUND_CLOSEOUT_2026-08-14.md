# Goal 058 G1 — odd-tail inverse-weighted correction bound closeout

Date: 2026-08-14

Route state: `CHALLENGER / NOT_RH`

Node verdict: `PROVED`

Goal 058: `OPEN`

## Joint source-wall verdict

The authoritative attachment-based review is preserved in:

- `GOAL058_G1_G3_ANALYTIC_SOURCE_WALL_MYTHOS_VERDICT_2026-08-14.md`;
- `GOAL058_G1_G3_ANALYTIC_SOURCE_WALL_PROSHKA_VERDICT_2026-08-14.md`.

Mythos proposed defining the classical G3 spectrum from a monotone finite
limit and sending the resulting Cauchy/interlacing package to Aristotle.
Proshka rejected that route as circular: a finite-limit definition would make
finite convergence tautological without identifying the differential
Sturm--Liouville spectrum required by DLMF 30.16.3.  The local API audit also
found no ready Cauchy-interlacing theorem on the current import surface.

For G1, both reviews agreed that the recovered source odd-tail coercivity is
not a full complex trial-complement floor.  Proshka selected one noncircular
local C1 leaf: bound the actual inverse-weighted odd-tail correction by the
actual residual norm.  Aristotle was rejected for this internal
infinite-dimensional custom-carrier proof.

## Knowledge preflight

Before the production write:

```text
./orchestrator/kb.py ask "sourceWeilOddTailInverseWeightedCorrection quadratic form residual norm correction bound min mu one"
```

returned no hits.  This is a discovery receipt only.

## Kernel-checked result

Production file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTailCorrectionBound.lean
SHA-256 2442bc565c2f76f37d5f00ff42bbdb624c8f95d0b45e1c5f5e9ae4510835f1b5
```

The public theorem

```text
Q3.RouteB.D0Pstar.sourceWeilOddTailInverseWeightedCorrection_quadraticForm_le
```

proves, for the actual `sourceWeilOddTailInverseWeightedData`,

```text
min mu 1 * Re <R^* C^-1 R x, x> <= 2 * ||R x||^2.
```

The proof sets `y = C^-1 R x`, uses the exact inverse equation `C y = R x`,
the literal graph lower bound

```text
(min mu 1 / 2) * ||y||^2 <= Re <C y, y>,
```

and Cauchy--Schwarz.  The zero/nonzero split on `y` is explicit, so no scalar
inverse surrogate or division-by-zero convention is hidden in the proof.

## Validation

Direct Lean, the 7811-job named target build, the 7817-job full build,
`q3_check`, whitespace and forbidden-token scans pass.  The printed public
axiom surface is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The only build warning is the pre-existing local-change warning for the
external `UnicodeBasic` dependency.

The RouteB inventory was refreshed to 247 files and 2,296 declarations with
`orphans=0` and `uncatalogued=0`.  The proof database has no missing or stale
declaration rows and its SQLite integrity check is `ok`.

## Honest boundary

This theorem closes C1 only: the inverse-weighted odd-tail correction budget.
It does not prove the corrected finite-head sign, exact row evenness, the even
part of the full complex `q`-orthogonal complement, a cofinal shift connector,
or the production complement floor.  The surviving G1 decomposition is C1
plus those still-missing C2/C3 source suppliers.

The G3 stop is unchanged:

```text
DLMF_FULL_FINITE_SPECTRUM_CROSSWALK_PROVED_ORDERED_FINITE_TO_CLASSICAL_LIMIT_ENDPOINT_COUNTS_2_3_AND_INDEX4_IDENTIFICATION_MISSING
```

The G1 stop narrows to:

```text
G1_ODD_TAIL_CORRECTION_BOUND_PROVED_CORRECTED_EVEN_HEAD_ROW_EVENNESS_AND_COFINAL_FULL_COMPLEMENT_FLOOR_MISSING
```

No G1, G3, Route B, or RH promotion follows from this node.
