# Step 30 — Boundary-null sequential exhaustion

## Goal

Package Steps 28 and 29 into the first exhaustion-facing theorem layer.

Step 28 proves that boundary values can be corrected algebraically. Step 29
proves that this correction is asymptotically harmless. Step 30 combines them:
ordinary sequential density plus closure under boundary correction gives
sequential density inside the boundary-null subspace.

## Lean file

`Q3/Proofs/PSD_BoundaryNullExhaustion.lean`

## Main objects

- `OrdinarySequentialExhaustive`
- `BoundaryNullSequentialExhaustive`
- `boundaryCorrected_evalPlus_zero`
- `boundaryCorrected_evalMinus_zero`
- `boundaryNullSequentialExhaustiveOfOrdinary`
- `boundaryNullSequentialExhaustive_exists_of_ordinary`

## Meaning

Given a normed space \(V\), boundary functionals \(E_+,E_-\), and correctors
\(b_+,b_-\), if:

1. the raw family is sequentially dense in \(V\);
2. \(E_+\) and \(E_-\) are continuous;
3. the corrector determinant is nonzero;
4. the family is closed under the fixed boundary correction;

then the same family is sequentially dense in the boundary-null class.

## Status

This is an abstract theorem shell, not the concrete smooth finite-space
exhaustion proof. The remaining analytic burden is to instantiate the
assumptions for the directed finite certificate family.

## Verification

`lake env lean Q3/Proofs/PSD_BoundaryNullExhaustion.lean` passes.

No `sorry`, `admit`, or `exact?` are introduced.

## Next blocker

Instantiate the abstract assumptions:

1. construct the concrete smooth finite spaces;
2. prove ordinary sequential density;
3. prove continuity of the boundary functionals in the chosen topology;
4. prove closure under boundary correction, possibly after directed refinement.
