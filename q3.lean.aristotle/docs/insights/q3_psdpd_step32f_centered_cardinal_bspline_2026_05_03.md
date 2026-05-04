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
- `centeredBoxSpline_neg_half`;
- `centeredBoxSpline_pos_half`;
- `not_CenteredCardinalBSplineEven_zero`;
- `centeredBoxSpline_neg_eq_of_ne_endpoints`;
- `centeredBoxSpline_shiftEvenAE`;
- `CenteredCardinalBSplineShiftEvenAE_zero`;
- `CenteredCardinalBSplineMatchesConvPower_zero`;
- `CenteredCardinalBSplineConvPowerConvolutionLaw_of_assoc`;
- `CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_of_convolutionLaw`;
- `CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_of_assoc`;
- `realBumpCorrelationProfile_eq_realConvolution_neg_of_shiftEvenAE`;
- `CenteredCardinalBSplineBaseCorrelationClosedForm_of_shiftEvenAE_selfConvolution`;
- `CenteredBSplineAutocorrelationClosedForm_of_cardinalShiftEvenAE_cardinalSelfConvolution`;
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

The self-convolution part is now further factored.  Lean proves:

```lean
CenteredCardinalBSplineConvPowerConvolutionLaw_of_assoc
```

which turns associativity of `realConvolution` into the formal degree law

\[
F_k * F_l = F_{k+l+1}.
\]

Lean also proves:

```lean
CenteredCardinalBSplineConvPowerSelfConvolutionClosedForm_of_assoc
```

so the self-convolution target follows from:

1. associativity of `realConvolution` on the relevant functions;
2. evenness of the target convolution power \(F_{2k+1}\).

## Endpoint convention correction

The current strict convention for `positivePartPower 0` makes the centered box
half-open at the endpoints:

\[
B_0(-1/2)=0,\qquad B_0(1/2)=1.
\]

Lean records this as:

```lean
centeredBoxSpline_neg_half
centeredBoxSpline_pos_half
not_CenteredCardinalBSplineEven_zero
```

This is harmless for the integral B-spline identities, because the endpoint is
a null set.  It does mean that a proof route requiring pointwise evenness of
degree zero is too strong.  The next proof step should use an a.e./integral
evenness formulation, or prove the box-convolution recurrence directly under
the integral.

The a.e./integral evenness route is now present in Lean:

```lean
RealFunctionShiftEvenAE
centeredBoxSpline_neg_eq_of_ne_endpoints
centeredBoxSpline_shiftEvenAE
realBumpCorrelationProfile_eq_realConvolution_neg_of_shiftEvenAE
CenteredCardinalBSplineShiftEvenAE
CenteredCardinalBSplineShiftEvenAE_zero
CenteredBSplineAutocorrelationClosedForm_of_cardinalShiftEvenAE_cardinalSelfConvolution
```

So the endpoint convention no longer blocks the main autocorrelation theorem.
The remaining evenness target is propagation of shifted a.e. evenness through
the spline family/convolution-power agreement, not pointwise evenness of the
degree-zero box.

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
4. Prove analytic associativity of `realConvolution` for the relevant
   convolution powers.
5. Propagate shifted a.e. evenness from the degree-zero box to the
   concrete/convolution-power spline where needed, using the new integral-safe
   route.
6. Prove the centered-cardinal `sinh`/sinc-power transform profile.
7. Prove boundary scale nonzero at \(z=\pm1/2\).
8. Feed these into the existing `BSplineTranslatedAnalyticContract`.

## Verdict

This is real concrete Step 32F progress, not a new receiver.  The B-spline
object now exists in Lean; the remaining blocker is the closed-form
autocorrelation/transform theorem package.

## 2026-05-04 update — degree-zero shifted a.e. base

The endpoint-safe base of the a.e. route is now Lean-proved:

```lean
centeredBoxSpline_neg_eq_of_ne_endpoints
centeredBoxSpline_shiftEvenAE
CenteredCardinalBSplineShiftEvenAE_zero
```

This records the exact correction: the strict box is not pointwise even, but it
is shifted-even almost everywhere, and therefore usable under the
autocorrelation integral.

Verification:

```text
lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean
lake build Q3.Proofs.PSD_CenteredCardinalBSpline
lake build Q3.Main
./scripts/check_axioms.sh
```

All pass.  The project axiom profile remains unchanged at 5 total axioms
including the 3 standard Lean axioms.
