# Step 32F — Centered cardinal B-spline concrete object

## Goal

Move Step 32F from generic bump identities to the actual centered cardinal
B-spline bump used by the PSD-pd finite blocks.

## Lean file

`Q3/Proofs/PSD_CenteredCardinalBSpline.lean`

## What landed

The file defines:

- `positivePartPower`;
- `centeredCardinalBSpline`;
- `bsplineScale`;
- `bsplineAutocorrDegree`;
- `bsplineAutocorrNorm`;
- `centeredBSplineEta`;
- `centeredBSplineR`;
- `centeredBSplineCorrelationProfile`;
- `centeredBSplineRealTransformProfile`;
- concrete boundary scales.
- `realConvolution`;
- `CenteredCardinalBSplineEven`;
- `CenteredBSplineSelfConvolutionClosedForm`.

It proves:

- `centeredCardinalBSpline_zero`;
- `bsplineScale_pos`;
- `bsplineScale_ne_zero`;
- `centeredBSplineBoundaryPlus_basis`;
- `centeredBSplineBoundaryMinus_basis`;
- `realBumpCorrelationProfile_eq_realConvolution_neg_of_even`;
- `centeredBSplineEta_even_of_cardinal_even`;
- `CenteredBSplineAutocorrelationClosedForm_of_selfConvolution`;
- `CenteredBSplineAutocorrelationClosedForm_of_cardinalEven_selfConvolution`;
- `centeredBSplineCorrelation_scaledTranslated_shift`;
- `centeredBSplineCorrelation_scaledTranslated_shift_closed`.

## Meaning

The generic Step 32F identities from `PSD_BSplineAnalyticModel.lean` now have a
concrete centered-cardinal B-spline object to specialize to.

The prime-shift correlation has been reduced to one explicit remaining theorem:

\[
\forall x,\quad
\operatorname{realBumpCorrelationProfile}(\eta_k)(x)
=
\frac{b_{2k+1}(s_kx)}{c_k}.
\]

In Lean this target is named:

`CenteredBSplineAutocorrelationClosedForm`.

The sign-sensitive measure-theory bridge is now also closed:

\[
\operatorname{corr}_f(x)
=
(f*f)(-x)
\]

for even \(f\), with the convolution convention

\[
(f*f)(x)=\int f(y)f(x-y)\,dy.
\]

So the remaining proof is reduced to:

1. `CenteredCardinalBSplineEven k`;
2. `CenteredBSplineSelfConvolutionClosedForm k`.

## External sanity check

The object follows the standard cardinal B-spline route:

- cardinal B-splines as convolution powers of the box;
- truncated-power finite-sum representation;
- sinc/sinh-power transform profile.

Useful references:

- Carl de Boor, cardinal B-splines:
  `https://pages.cs.wisc.edu/~deboor/toast/pages005.html`
- bsplines.org, flavors and types:
  `https://bsplines.org/flavors-and-types-of-b-splines/`
- Boost cardinal B-spline documentation:
  `https://www.boost.org/doc/libs/latest/libs/math/doc/html/math_toolkit/sf_poly/cardinal_b_splines.html`

## Remaining inside Step 32F

1. Prove `CenteredCardinalBSplineEven k`.
2. Prove `CenteredBSplineSelfConvolutionClosedForm k`.
3. Prove `bsplineAutocorrNorm k ≠ 0`, preferably positivity.
4. Prove the centered-cardinal `sinh`/sinc-power transform profile.
5. Prove boundary scale nonzero at \(z=\pm1/2\).
6. Feed these into the existing `BSplineTranslatedAnalyticContract`.

## Verdict

This is real concrete Step 32F progress, not a new receiver.  The B-spline
object now exists in Lean; the remaining blocker is the closed-form
autocorrelation/transform theorem package.
