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
- `CenteredCardinalBSplineMatchesConvPowerAE`;
- `CenteredCardinalBSplineMatchesConvPowerShiftAE`;
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
- `CenteredCardinalBSplineMatchesConvPowerAE_zero`;
- `CenteredCardinalBSplineMatchesConvPowerShiftAE_zero`;
- `CenteredCardinalBSplineMatchesConvPowerAE_of_pointwise`;
- `CenteredCardinalBSplineMatchesConvPowerShiftAE_of_pointwise`;
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
- `CenteredCardinalBSplineSelfConvolutionClosedForm_of_convPowerAE`;
- `CenteredBSplineAutocorrelationClosedForm_of_convPowerRoute`;
- `CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute`;
- `CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute_pointwise`;
- `CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute_assoc`;
- `bsplineAutocorrNorm_pos_zero`;
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
CenteredCardinalBSplineMatchesConvPowerAE
CenteredCardinalBSplineMatchesConvPowerShiftAE
CenteredCardinalBSplineSelfConvolutionClosedForm_of_convPowerAE
CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute
```

So the endpoint convention no longer blocks the main autocorrelation theorem.
The remaining evenness target is propagation of shifted a.e. evenness through
the spline family/convolution-power agreement, not pointwise evenness of the
degree-zero box.

The endpoint-safe convolution-power route now has the exact theorem shape:

```lean
CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute
CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute_pointwise
CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute_assoc
```

This route uses a.e. agreement for the degree `k` factors under the integral
and shifted-a.e. agreement for the reflected factor.  The degree `2*k+1`
agreement is still pointwise because the final spline value is evaluated at
the external point `x`, not integrated out.

The first concrete normalizer positivity fact is also closed:

```lean
bsplineAutocorrNorm_pos_zero
```

This proves \(0<c_0\).  The all-degree \(0<c_k\) theorem still needs the
square-integral/self-convolution positivity argument.

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
3. Prove `CenteredCardinalBSplineMatchesConvPowerAE k` and
   `CenteredCardinalBSplineMatchesConvPowerShiftAE k`, or prove pointwise
   `CenteredCardinalBSplineMatchesConvPower k` and use the new adapters.
4. Prove pointwise
   `CenteredCardinalBSplineMatchesConvPower (bsplineAutocorrDegree k)` for the
   final target degree, or replace the final pointwise theorem by a stronger
   target-degree regularity bridge.
5. Prove analytic associativity of `realConvolution` for the relevant
   convolution powers.
6. Propagate shifted a.e. evenness from the degree-zero box to the
   concrete/convolution-power spline where needed, using the new integral-safe
   route.
7. Prove the centered-cardinal `sinh`/sinc-power transform profile.
8. Prove boundary scale nonzero at \(z=\pm1/2\).
9. Feed these into the existing `BSplineTranslatedAnalyticContract`.

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

## 2026-05-04 update — convolution-power AE route

The route no longer requires pointwise agreement for every occurrence of
`b_k`.  Lean now has:

```lean
CenteredCardinalBSplineMatchesConvPowerAE
CenteredCardinalBSplineMatchesConvPowerShiftAE
CenteredCardinalBSplineSelfConvolutionClosedForm_of_convPowerAE
CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute
```

This is the honest endpoint-safe route:

```text
shifted a.e. evenness
+ a.e./shifted-a.e. agreement under the integral
+ pointwise agreement for the target degree
+ conv-power self-convolution
=> CenteredBSplineAutocorrelationClosedForm
```

The pointwise target-degree agreement is still required because the final
right-hand side is evaluated at a specific `x`.

## 2026-05-04 update — route adapters and base positivity

Lean now has adapter theorems that let the future recurrence/agreement theorem
feed the endpoint-safe route directly:

```lean
CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute_pointwise
CenteredBSplineAutocorrelationClosedForm_of_convPowerAERoute_assoc
```

The second theorem also discharges the self-convolution input from
`RealConvolutionAssociative` and target-degree evenness via the existing
convolution-power bridge.

The degree-zero normalizer positivity is proved:

```lean
bsplineAutocorrNorm_pos_zero
```

Remaining all-degree blockers are unchanged: recurrence/agreement,
convolution associativity/evenness on the relevant powers, and \(0<c_k\) for
all `k`.

Verification on 2026-05-04:

```text
lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean
lake build Q3.Proofs.PSD_CenteredCardinalBSpline
lake build Q3.Main
./scripts/check_axioms.sh
```

All pass.  The axiom profile is unchanged: three standard Lean axioms and two
documented project axioms.

## 2026-05-05 update — recurrence package assembly

Semantic search on `q3_docs` did not find an already-closed local recurrence
lemma for the centered-cardinal truncated-power definition.  The useful local
hits were the existing Step 32F receiver and old finite-sum/integral proof
style; an external sanity check again confirms the standard route: cardinal
B-splines are convolution powers of the centered box.

Lean now has the formal assembly layer that will consume the remaining
mathematical bricks:

```lean
CenteredCardinalBSplineMatchesConvPower_all_of_succ_eq_conv_box
CenteredBSplineAutocorrelationClosedForm_all_of_convPower_inputs
CenteredBSplineAutocorrelationClosedForm_all_of_recurrence_package
```

Thus the Step 32F autocorrelation target is no longer a loose bundle.  It is
reduced to the precise remaining inputs:

1. prove the recurrence `b_{k+1}=b_k*b_0`;
2. prove `0 < bsplineAutocorrNorm k`;
3. propagate `CenteredCardinalBSplineShiftEvenAE k`;
4. prove the convolution-power self-convolution closed form.

The next live Lean target is still the recurrence, preferably through the
positive-part interval integral plus Pascal telescope.

## 2026-05-07 update — branch export reviewed

The raw branch export at
`/Users/emalam/Documents/GitHub/rh_lean_01_2026/docs/2026-5-5 8-39-57-________Branch_______________________.md`
was reviewed as project memory, but should not be committed or indexed as-is.
The reusable synthesis is recorded in:

```text
docs/insights/q3_branch_operator_difference_step32f_review_2026_05_07.md
```

The review does not change the live theorem frontier.  It confirms the current
route:

1. stay inside Step 32F, not Step 33;
2. close `centeredCardinalBSpline_succ_eq_conv_box`;
3. feed the existing recurrence assembly layer;
4. then close `CenteredBSplineAutocorrelationClosedForm`.

The exact local proof split remains:

```lean
positivePartPower_interval_integral_centered
centeredCardinalBSpline_pascal_telescope
centeredCardinalBSpline_succ_eq_conv_box
```

## 2026-05-07 update — Pascal telescope closed

Lean now proves the finite-sum algebra half of the recurrence route:

```lean
centeredCardinalBSpline_altChoose_shift_sum
centeredCardinalBSpline_pascal_telescope
```

The theorem

```lean
centeredCardinalBSpline_pascal_telescope
```

is the abstract binomial identity:

```text
sum_j (-1)^j choose(n,j) (T_j - T_(j+1))
= sum_j (-1)^j choose(n+1,j) T_j
```

This closes the Pascal bookkeeping needed after the positive-part interval
integral produces the `T_j - T_(j+1)` difference.  The recurrence is now blocked
on the analytic integral/reduction side, not on finite-sum algebra.

Next live target:

```lean
positivePartPower_interval_integral_centered
```

## 2026-05-07 update — positive-part interval integral closed

Lean now proves the analytic integral half of the recurrence route:

```lean
positivePartPower_succ_eq_max
continuous_positivePartPower_succ
intervalIntegrable_positivePartPower_zero
intervalIntegrable_positivePartPower
hasDerivAt_positivePartPower_succ_div_off_zero
positivePartPower_intervalIntegral
positivePartPower_interval_integral_centered
```

The proof respects the strict degree-zero endpoint convention:

- degree `0` is handled as a bounded measurable step function;
- positive degrees use the continuous `(max x 0)^(n+1)` model;
- the antiderivative step uses FTC away from the single kink `{0}`;
- the centered form converts the `Icc` set integral to the oriented interval
  integral and applies the substitution `u = x + A - y`.

Together with the already closed Pascal telescope, the recurrence

```lean
centeredCardinalBSpline (k + 1)
  = realConvolution (centeredCardinalBSpline k) centeredBoxSpline
```

is now blocked on the box-convolution expansion/finite-sum assembly, not on
calculus or Pascal algebra.

Next live target:

```lean
centeredCardinalBSpline_conv_box_after_integral
```
