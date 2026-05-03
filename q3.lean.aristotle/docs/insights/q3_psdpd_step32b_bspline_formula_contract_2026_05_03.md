# Step 32B — B-spline formula contract

## Goal

Move one layer below the Step 32A matrix-identification receiver.

Step 32A accepted the abstract entry hypotheses:

\[
\mathcal A(h_v)=v^TAv,\qquad
\mathcal P(h_v)=v^TPv,\qquad
\mathcal W(h_v)=v^TCv,
\]

and a boundary implication from analytic boundary vanishing to \(Qv=0\).

Step 32B discharges two finite algebraic pieces that should not remain manual
fields:

1. \(Q\) is a two-row boundary matrix, up to nonzero row scalings.
2. \(C\) is the entrywise matrix difference \(A-P\).

## Lean file

`Q3/Proofs/PSD_BSplineFormulaContract.lean`

## Main objects

- `matrixSub`
- `quadForm_matrixSub`
- `twoRowBoundaryMatrix`
- `BSplineBoundaryRows`
- `BSplineFormulaContract`

## Main theorem payload

The boundary rows are allowed to have harmless nonzero row scales:

\[
E_+(h_v)=s_+\sum_i q_{+,i}v_i,
\qquad
E_-(h_v)=s_-\sum_i q_{-,i}v_i,
\]

with \(s_+\ne0\) and \(s_-\ne0\).

Then analytic boundary vanishing implies:

\[
Qv=0.
\]

The full matrix is now supplied as:

\[
C=A-P,
\]

and Lean proves:

\[
v^TCv=v^TAv-v^TPv.
\]

## Conversion

`BSplineFormulaContract.toEntryData` converts the formula-level contract into
the Step 32A receiver `BSplinePacketEntryData`.

`BSplineFormulaContract.toFiniteWeilMatrixModel` then produces the Step 31
`FiniteWeilMatrixModel`.

## Verification

- `lake env lean Q3/Proofs/PSD_BSplineFormulaContract.lean`
- hole scan: clean

## Remaining blocker

Step 32C should prove the actual analytic formulas that feed this contract:

1. B-spline packet transform:
   \(H_j(z)=\sqrt{\ell}\,e^{zu_j}E_{\ell,k}(z)\).
2. Boundary row formulas:
   \(q_{+,j}=e^{u_j/2}\), \(q_{-,j}=e^{-u_j/2}\), with nonzero row scales.
3. Correlation identity:
   \(\langle \psi_j,S_a\psi_i\rangle=r_k((u_j-u_i-a)/\ell)\).
4. Arch and prime entry identities.

## Verdict

Step 32B closes the finite algebra around the concrete B-spline formula port.
The remaining work is now genuinely analytic, not bookkeeping:
prove the transform, correlation, Arch, and prime identities.
