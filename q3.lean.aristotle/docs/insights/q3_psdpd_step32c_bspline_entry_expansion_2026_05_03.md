# Step 32C — B-spline entry expansion

## Goal

Move from formula-level contracts to basis-level contracts.

Step 32B expects:

- two-row boundary formulas;
- Arch and prime matrix identities on synthesized packets.

Step 32C proves that these follow from basis-level data:

\[
h_v=\sum_i v_i\psi_i,
\]

boundary values on each \(\psi_i\), and bilinear form entries on pairs
\((\psi_i,\psi_j)\).

## Lean file

`Q3/Proofs/PSD_BSplineEntryExpansion.lean`

## New objects

- `PacketBasisExpansion`
- `PacketBilinearMatrixExpansion`
- `BSplineBasisFormulaContract`

## Boundary payload

If

\[
E_+(\psi_i)=s_+q_{+,i},
\qquad
E_-(\psi_i)=s_-q_{-,i},
\]

then Lean proves:

\[
E_+(h_v)=s_+\sum_i q_{+,i}v_i,
\qquad
E_-(h_v)=s_-\sum_i q_{-,i}v_i.
\]

This feeds the Step 32B `BSplineBoundaryRows` contract.

## Bilinear payload

If a bilinear form has basis entries \(M_{ij}\), Lean proves:

\[
B(h_v,h_v)=v^TMv.
\]

The matrix-entry convention in the Lean file places the row index in the
second bilinear slot:

\[
M_{ij}=B(\psi_j,\psi_i).
\]

For the real symmetric Arch/Prime matrices this is harmless and matches the
finite certificate `quadForm` convention.

## Conversion

`BSplineBasisFormulaContract.toFormulaContract` produces the Step 32B
`BSplineFormulaContract`.

`BSplineBasisFormulaContract.toFiniteWeilMatrixModel` then produces the Step 31
`FiniteWeilMatrixModel`.

## Verification

- `lake env lean Q3/Proofs/PSD_BSplineEntryExpansion.lean`
- hole scan: clean

## Remaining blocker

Step 32D should prove the actual analytic basis identities:

1. \(H_j(z)=\sqrt{\ell}\,e^{zu_j}E_{\ell,k}(z)\).
2. \(E_\pm(\psi_j)=s_\pm e^{\pm u_j/2}\).
3. Arch basis pairings give the Arch matrix \(A\).
4. Prime basis pairings give the Prime matrix \(P\), via the B-spline
   correlation identity.

## Verdict

Step 32C removes another bookkeeping layer.  The remaining Step 32 work is now
the real analytic content: B-spline transform, correlation, and entry formulas.
