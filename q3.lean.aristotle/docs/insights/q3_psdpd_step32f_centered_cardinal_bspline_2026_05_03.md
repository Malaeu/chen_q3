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
- `centeredBoxSpline`;
- `centeredCardinalBSplineConvPower`;
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
- `CenteredCardinalBSplineMatchesConvPower`;
- `CenteredCardinalBSplineBaseCorrelationClosedForm`;
- `CenteredCardinalBSplineSelfConvolutionClosedForm`;
- `CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm`;
- `CenteredBSplineSelfConvolutionClosedForm`.

It proves:

- `centeredCardinalBSpline_zero`;
- `centeredCardinalBSpline_zero_eq_centeredBoxSpline`;
- `CenteredCardinalBSplineMatchesConvPower_zero`;
- `bsplineScale_pos`;
- `bsplineScale_ne_zero`;
- `centeredBSplineBoundaryPlus_basis`;
- `centeredBSplineBoundaryMinus_basis`;
- `CenteredBSplineAutocorrelationClosedForm_of_baseCorrelation`;
- `CenteredCardinalBSplineBaseCorrelationClosedForm_of_even_selfConvolution`;
- `CenteredCardinalBSplineSelfConvolutionClosedForm_of_convPower`;
- `CenteredBSplineAutocorrelationClosedForm_of_convPowerRoute`;
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

1. positivity of \(c_k=b_{2k+1}(0)\);
2. the unnormalized base identity
   \[
   \operatorname{corr}(b_k)(x)=b_{2k+1}(x).
   \]

The normalizing/scaling step is now Lean-proved:

\[
\operatorname{corr}(\eta_k)(x)
=
\frac{b_{2k+1}(s_kx)}{c_k}
\]

follows from \(c_k>0\) and the unnormalized base identity.

The proof-friendly convolution-power model is also now present:

\[
B_0=\mathbf 1_{[-1/2,1/2]},
\qquad
B_{k+1}=B_k * B_0.
\]

Lean proves the downstream route:

```lean
CenteredBSplineAutocorrelationClosedForm_of_convPowerRoute
```

so the final target follows from:

1. \(0<c_k\);
2. `CenteredCardinalBSplineEven k`;
3. `CenteredCardinalBSplineMatchesConvPower k`;
4. `CenteredCardinalBSplineMatchesConvPower (2*k+1)`;
5. `CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm k`.

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

1. Prove `0 < bsplineAutocorrNorm k`.
2. Prove `CenteredCardinalBSplineEven k`.
3. Prove `CenteredCardinalBSplineMatchesConvPower k` for all degrees needed.
4. Prove the pure convolution-power self-convolution theorem:
   `CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm k`.
5. Prove the centered-cardinal `sinh`/sinc-power transform profile.
6. Prove boundary scale nonzero at \(z=\pm1/2\).
7. Feed these into the existing `BSplineTranslatedAnalyticContract`.

## Verdict

This is real concrete Step 32F progress, not a new receiver.  The B-spline
object now exists in Lean; the remaining blocker is the closed-form
autocorrelation/transform theorem package.
