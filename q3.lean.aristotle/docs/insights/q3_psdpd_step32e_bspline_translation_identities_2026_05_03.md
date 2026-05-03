# Step 32E — B-spline translated-packet identities

## Goal

Close the next theorem-facing reduction after Step 32D.

Instead of adding another receiver, Step 32E proves that the concrete packet
rows and kernel entries follow from translated-packet covariance:

\[
\psi_i = T_{u_i}\psi_0.
\]

## Lean file

`Q3/Proofs/PSD_BSplineTranslationIdentities.lean`

## Boundary rows

If

\[
E_+(T_u f)=e^{u/2}E_+(f),
\qquad
E_-(T_u f)=e^{-u/2}E_-(f),
\]

and \(E_\pm(\psi_0)\ne0\), then

\[
E_+(\psi_i)=s_+e^{u_i/2},
\qquad
E_-(\psi_i)=s_-e^{-u_i/2}.
\]

This supplies the concrete Step 32D rows

\[
q_{+,i}=e^{u_i/2},
\qquad
q_{-,i}=e^{-u_i/2}.
\]

## Kernel entries

If a bilinear packet pairing satisfies

\[
B(T_u\psi_0,T_v\psi_0)=K(u-v),
\]

then with the Step 32C matrix convention

\[
M_{ij}=B(\psi_j,\psi_i),
\]

the entries are

\[
M_{ij}=K(u_j-u_i).
\]

This is the exact difference-kernel shape needed by the Arch and Prime
matrices.

## Main objects

- `PacketTranslationBoundaryData`
- `PacketTranslationKernelData`
- `BSplineTranslatedAnalyticContract`

## Main conversions

\[
\texttt{BSplineTranslatedAnalyticContract}
\to
\texttt{BSplineAnalyticKernelContract}
\to
\texttt{FiniteWeilMatrixModel}.
\]

## Meaning

Step 32E proves the finite translation algebra behind the B-spline packet
matrix formulas:

- translated basis functions give exponential boundary rows;
- translation-invariant pairings give difference kernels;
- those data instantiate the existing finite Weil matrix model.

## Remaining blocker

Step 32F should prove the actual base B-spline analytic identities:

1. Laplace/Fourier transform of the centered scaled B-spline bump;
2. nonzero boundary scales \(E_{\ell,k}(\pm1/2)\);
3. B-spline autocorrelation profile \(r_k\);
4. Arch and Prime profiles instantiate the two difference kernels.

## Verdict

The packet-translation reduction is now Lean-checked and hole-free.  The next
step is no longer matrix bookkeeping; it is the actual B-spline transform and
correlation analysis.
