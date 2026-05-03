# Step 29 -- Boundary-null correction convergence

## Goal

Upgrade the algebraic correction from Step 28 to a convergence statement.

If

\[
g_n\to h,\qquad E_+(h)=E_-(h)=0,
\]

and \(E_\pm\) are continuous, then the explicitly corrected approximants

\[
g_n^\circ
=
g_n-a_{n,+}b_+-a_{n,-}b_-
\]

still satisfy

\[
g_n^\circ\to h.
\]

## Lean file

`Q3/Proofs/PSD_BoundaryNullConvergence.lean`

## Main definitions

- `boundaryCoeffPlus`
- `boundaryCoeffMinus`
- `boundaryCorrected`

## Main theorems

- `boundaryCoeffPlus_tendsto_zero`
- `boundaryCoeffMinus_tendsto_zero`
- `boundaryCorrected_tendsto`
- `boundaryCorrected_tendsto_of_continuous_boundary`

## Meaning

Step 28 proves that the boundary correction exists.

Step 29 proves that the correction is asymptotically harmless: if the raw
approximants converge to a boundary-null limit and the boundary functionals are
continuous, then the correction coefficients tend to zero and the corrected
sequence has the same limit.

Together, Step 28 and Step 29 supply the hinge needed to turn ordinary finite
density into boundary-null finite density.

## Verification status

The new Lean file has no `sorry`, `admit`, or `exact?`.

The theorem file was checked successfully in a clean Lake mirror with fresh
Mathlib cache artifacts:

```bash
lake env lean Q3/Proofs/PSD_BoundaryNullConvergence.lean
```

The main workspace `.lake` cache is still damaged from the earlier failed cache
repair attempt and should be refreshed separately before ordinary local builds.

## Next blocker

Step 30: boundary-null exhaustion theorem.

This should combine:

1. ordinary finite-space density;
2. continuity of boundary functionals;
3. Step 28 algebraic correction;
4. Step 29 convergence of corrected approximants.
