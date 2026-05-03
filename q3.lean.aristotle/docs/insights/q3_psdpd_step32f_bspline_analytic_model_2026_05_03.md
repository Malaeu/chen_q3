# Step 32F — B-spline analytic model, generic packet identities

## Goal

Start the real analytic model layer needed to close Step 32F without adding
another receiver.

## Lean file

`Q3/Proofs/PSD_BSplineAnalyticModel.lean`

## What landed

The file proves generic translated/scaled bump identities by actual integral
change-of-variables:

- `realBumpLaplace_scaledTranslated`
- `realBumpLaplace_scaledTranslated_plus`
- `realBumpLaplace_scaledTranslated_minus`
- `complexBumpLaplace_scaledTranslated`
- `realBumpCorrelation_scaledTranslated_shift`

These are the generic analytic identities behind:

\[
\psi_j(u)=\ell^{-1/2}\eta((u-u_j)/\ell),
\qquad
H_j(z)=\sqrt{\ell}e^{zu_j}E_\ell(z),
\]

and

\[
\int \psi_j(u)(S_a\psi_i)(u)\,du
=
r_\eta((u_j-u_i-a)/\ell).
\]

## Meaning

This is not another theorem-facing port.  It is the first real analytic engine
piece under the existing Step 32 consumer.

The generic bump identities now exist in Lean and compile without holes.

## Remaining inside Step 32F

To close Step 32 strictly, the concrete centered-cardinal B-spline facts still
need to be added:

1. define the centered/scaled cardinal B-spline bump;
2. prove its `sinh`/sinc-power transform profile;
3. prove nonzero boundary scales at \(z=\pm1/2\);
4. prove the autocorrelation identity
   \(r_k(x)=b_{2k+1}(s_kx)/c_k\);
5. connect the generic Arch/Prime profiles to the existing
   `BSplineTranslatedAnalyticContract`.

## Verdict

Step 32F now has real Lean analytic content.  It is not fully closed yet, but
the blocker has narrowed from "matrix-identification port" to the concrete
centered-cardinal B-spline closed-form identities.
