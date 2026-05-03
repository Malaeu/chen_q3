# Step 32D — B-spline analytic kernel contract

## Goal

Create the last theorem-facing receiver before the genuine B-spline analytic
proofs.

Steps 32A--32C reduced the matrix identification problem to basis-level data.
Step 32D gives those basis-level data a concrete B-spline shape:

- boundary rows are \(e^{u_i/2}\) and \(e^{-u_i/2}\);
- Arch and Prime matrices are built from kernels with basis-pairing identities.

## Lean file

`Q3/Proofs/PSD_BSplineAnalyticKernelContract.lean`

## New objects

- `bsplineBoundaryPlusRow`
- `bsplineBoundaryMinusRow`
- `matrixOfKernel`
- `PacketKernelPairingData`
- `BSplineAnalyticKernelContract`

## Boundary rows

For centers \(u_i\), Lean now has concrete rows:

\[
q_{+,i}=\exp(u_i/2),
\qquad
q_{-,i}=\exp(-u_i/2).
\]

The contract allows nonzero global row scales:

\[
E_+(\psi_i)=s_+q_{+,i},
\qquad
E_-(\psi_i)=s_-q_{-,i}.
\]

These scales will absorb constants such as
\(\sqrt{\ell}E_{\ell,k}(\pm1/2)\).

## Kernel entries

`PacketKernelPairingData` packages a bilinear form and a kernel with entry
identity:

\[
K_{ij}=B(\psi_j,\psi_i).
\]

It converts to the Step 32C `PacketBilinearMatrixExpansion`, which then gives:

\[
B(h_v,h_v)=v^TKv.
\]

## Conversion chain

`BSplineAnalyticKernelContract` converts through the whole receiver stack:

```text
BSplineAnalyticKernelContract
→ BSplineBasisFormulaContract
→ BSplineFormulaContract
→ FiniteWeilMatrixModel
```

## Verification

- `lake env lean Q3/Proofs/PSD_BSplineAnalyticKernelContract.lean`
- hole scan: clean

## Remaining blocker

Step 32E is now the first genuinely analytic proof step:

1. Prove the B-spline transform formula
   \(H_j(z)=\sqrt{\ell}\,e^{zu_j}E_{\ell,k}(z)\).
2. Deduce nonzero boundary row scales.
3. Prove the B-spline correlation identity.
4. Use those to instantiate the Arch and Prime kernels.

## Verdict

Step 32D closes the final bookkeeping receiver.  The next work is no longer
contract wiring; it is the actual B-spline transform/correlation mathematics.
