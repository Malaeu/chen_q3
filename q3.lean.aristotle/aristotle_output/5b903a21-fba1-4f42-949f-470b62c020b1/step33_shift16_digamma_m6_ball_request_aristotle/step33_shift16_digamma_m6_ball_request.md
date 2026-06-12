# Step33A.1-A Request: shift16 m6 digamma main norm

## Context

We are in PSD Step33A.1-A, raw-Omega first endpoint analytic backend.

Current status as of 2026-06-08: Codex has Lean-checked the landing wrappers
down to one clean norm input.  Do not target the older fixed-center ball first
unless the preferred norm target below is impossible.

Already Lean-checked:

```lean
step33FixedLogPiInterval
step33FixedLogPiLower_le
step33FixedLogPi_le_upper
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaAdd16_fixedComplexMainError_logPiChecked
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaAdd16_fixedComplexMainError_logPiChecked_explicitPoint
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaAdd16_fixedComplexMainError_logPiChecked_explicitPoint_of_re_im_abs
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shiftedDigammaAdd16_fixedComplexMainError_logPiChecked_explicitPoint_of_re_im_quarter
```

The fixed first-endpoint `Real.log Real.pi` interval, the argument/log
component wrappers, and the Re/Im projection from a complex norm are closed.
The remaining analytic input is now only the tight m=6 shifted-digamma main
norm.

Do not touch CSV, ARadius, radius floor, LDL, Q3.Main, H1, or PO3.
Do not use `sorry`, `admit`, `exact?`, `axiom`, or `unsafe`.

## Existing local files

Important imports / source files:

```lean
import Q3.DigammaSeries
import Q3.DigammaRemainder
import Q3.Proofs.PSD_CenteredCoeffAnalyticABoundsBackend
```

Existing checked theorem that is too wide:

```lean
Q3.digamma_stieltjes_complex_remainder_bound
```

It is the N=1 Stieltjes/Euler-Maclaurin remainder and cannot meet the endpoint
radius.  We need a higher-order fixed theorem.

New checked local landing support:

```lean
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport

Q3.PSDpd.Step33.step33Shift16DigammaPoint
Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter
Q3.PSDpd.Step33.step33Shift16DigammaM6Main
Q3.PSDpd.Step33.step33_shift16_digamma_fixed_complex_ball_of_m6_main
Q3.PSDpd.Step33.step33_shift16_digamma_fixed_complex_ball_of_component_abs
Q3.PSDpd.Step33.step33_shift16_digamma_fixed_complex_ball_of_m6_component_abs
Q3.PSDpd.Step33.step33Shift16DigammaM6AlgebraicPart
Q3.PSDpd.Step33.step33Shift16DigammaM6Main_eq_log_add_algebraicPart
Q3.PSDpd.Step33.step33_shift16_digamma_m6_center_component_abs_of_log_component_abs
Q3.PSDpd.Step33.step33Shift16DigammaPoint_ne_zero
Q3.PSDpd.Step33.step33Shift16DigammaLog_re_eq
Q3.PSDpd.Step33.step33Shift16DigammaPoint_normSq_eq
Q3.PSDpd.Step33.step33Shift16DigammaPoint_norm_eq_sqrt
Q3.PSDpd.Step33.step33Shift16DigammaLog_re_eq_log_sqrt
Q3.PSDpd.Step33.step33Shift16DigammaLog_im_eq_arg
```

The preferred landing theorem now consumes only:

```lean
Q3.PSDpd.Step33.step33_shift16_digamma_m6_main_component_abs_of_norm

Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport
  .RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
  .primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_main_norm
```

If convenient, the older fixed-center theorem can still be proved by supplying:

```lean
hMain :
  ‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
    Q3.PSDpd.Step33.step33Shift16DigammaM6Main‖ <= mainErr

hCenter :
  ‖Q3.PSDpd.Step33.step33Shift16DigammaM6Main -
    Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter‖ <= centerErr

hErr :
  mainErr + centerErr <=
    Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius
```

Then Lean already derives the required fixed-center ball via
`step33_shift16_digamma_fixed_complex_ball_of_m6_main`.

The component landing route is also checked.  It is enough to supply direct
component estimates:

```lean
|(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
    Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter).re| <=
  Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius

|(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
    Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter).im| <=
  Q3.PSDpd.Step33.step33Shift16DigammaComponentRadius
```

or m6 component estimates:

```lean
|(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
    Q3.PSDpd.Step33.step33Shift16DigammaM6Main).re| <= mainReErr

|(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
    Q3.PSDpd.Step33.step33Shift16DigammaM6Main).im| <= mainImErr

|(Q3.PSDpd.Step33.step33Shift16DigammaM6Main -
    Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter).re| <= centerReErr

|(Q3.PSDpd.Step33.step33Shift16DigammaM6Main -
    Q3.PSDpd.Step33.step33Shift16DigammaFixedCenter).im| <= centerImErr

(mainReErr + mainImErr) + (centerReErr + centerImErr) <=
  Q3.PSDpd.Step33.step33Shift16DigammaTargetRadius
```

These feed the checked endpoint wrappers
`primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_fixed_component_abs`
and
`primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_component_abs`.

There is now an even narrower checked log-component landing route.  It is
enough to supply:

```lean
|(Complex.log Q3.PSDpd.Step33.step33Shift16DigammaPoint).re -
    logReCenter| <= logReErr

|(Complex.log Q3.PSDpd.Step33.step33Shift16DigammaPoint).im -
    logImCenter| <= logImErr

logReErr +
    |logReCenter +
        Q3.PSDpd.Step33.step33Shift16DigammaM6AlgebraicPart.re -
      Q3.PSDpd.Step33.step33Shift16DigammaFixedRe| <= centerReErr

logImErr +
    |logImCenter +
        Q3.PSDpd.Step33.step33Shift16DigammaM6AlgebraicPart.im -
      Q3.PSDpd.Step33.step33Shift16DigammaFixedIm| <= centerImErr
```

plus the component estimates for
`Q3.digamma step33Shift16DigammaPoint - step33Shift16DigammaM6Main` and the
total 5e-22 budget.  These feed:

```lean
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_log_component_abs
```

For the fixed log proof, the following component-shape lemmas are already
checked:

```lean
Q3.PSDpd.Step33.step33Shift16DigammaLog_re_eq
Q3.PSDpd.Step33.step33Shift16DigammaLog_re_eq_log_sqrt
Q3.PSDpd.Step33.step33Shift16DigammaLog_im_eq_arg
```

## Exact target

Please prove the following theorem, or a theorem immediately usable to prove it
with no new analytic assumptions:

```lean
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport

open scoped Real Topology ComplexOrder BigOperators

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

theorem step33_shift16_digamma_m6_main_norm :
    ‖Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaM6Main‖ <=
      step33Shift16DigammaM6MainComponentRadius := by
  -- proof here

end Step33
end PSDpd
end Q3
```

Expanded target:

```lean
‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
    Q3.PSDpd.Step33.step33Shift16DigammaM6Main‖ <=
  Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius
```

Checked adapter targets are also acceptable.  Either of these will immediately
prove the exact target above without adding any new analytic assumption:

```lean
Q3.PSDpd.Step33
  .step33_shift16_digamma_m6_main_norm_of_log_add_algebraicPart_bound

Q3.PSDpd.Step33
  .step33_shift16_digamma_m6_main_norm_of_expanded_asymptotic_bound
```

So Aristotle/Louise may prove the bound in the cleaner form:

```lean
‖Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint -
    (Complex.log Q3.PSDpd.Step33.step33Shift16DigammaPoint +
      Q3.PSDpd.Step33.step33Shift16DigammaM6AlgebraicPart)‖ <=
  Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius
```

or directly against the expanded Bernoulli expression defining
`step33Shift16DigammaM6Main`.

where the radius is:

```lean
Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius
  = (1 : Real) / (10000000000000000000000 : Real)
```

The point is:

```text
step33Shift16DigammaPoint = 129/4 + i/40
```

The m=6 main is:

```lean
step33Shift16DigammaM6Main
  = Complex.log step33Shift16DigammaPoint
    + step33Shift16DigammaM6AlgebraicPart
```

with:

```lean
step33Shift16DigammaM6Main_eq_log_add_algebraicPart
```

Fallback acceptable theorem: if the proof naturally lands directly at the old
fixed center, `step33_shift16_digamma_fixed_complex_ball_explicit` is still
usable.  But prefer the m6-main norm above because all downstream wrappers now
consume that one fact.

## Recommended proof route

Use a high-order Euler-Maclaurin/Bernoulli asymptotic theorem for the digamma
function, specialized to the fixed point `z = 129/4 + i/40`.

The six-term asymptotic main should be:

```lean
Complex.log z
  - (1 / (2 : Complex)) * z⁻¹
  - (1 / (12 : Complex)) * z⁻²
  + (1 / (120 : Complex)) * z⁻⁴
  - (1 / (252 : Complex)) * z⁻⁶
  + (1 / (240 : Complex)) * z⁻⁸
  - (1 / (132 : Complex)) * z⁻¹⁰
  + ((691 : Complex) / 32760) * z⁻¹²
```

This is:

```text
log z - 1/(2z) - Σ_{k=1..6} B_{2k}/(2k z^(2k))
```

with:

```text
B2=1/6, B4=-1/30, B6=1/42, B8=-1/30, B10=5/66, B12=-691/2730.
```

## Numeric diagnostic, not a proof

ACB/Arb at 768-bit precision gives:

```text
‖digamma(z) - fixedCenter‖ <= 1.47e-31
```

Bernoulli asymptotic diagnostic:

```text
m=5  true error about 1.66e-20   too wide
m=6  true error about 6.30e-23   enough
m=7  true error about 3.22e-25   more margin
```

So order 6 is enough in principle:

```text
remainder_m6 + main_to_fixedCenter < 5e-22
```

If order 6 is awkward in Lean, order 7 is acceptable.

## Output expectation

Return only Lean code that compiles in this project.  It is acceptable to add
helper lemmas for:

```text
fixed complex-log interval for z = 129/4 + i/40
fixed Bernoulli/asymptotic main interval
fixed high-order remainder bound
triangle inequality from main ball to fixedCenter
```

But the final delivered theorem should be the exact
`step33_shift16_digamma_m6_main_norm`, or theorem(s) immediately usable to
prove it without adding new analytic assumptions.  The older fixed-center and
quarter-radius statements are fallback landing targets only.

## Checked landing files already available

Codex has already added and Lean-checked:

```lean
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderLanding
```

The preferred landing target is now:

```lean
Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport
  .RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
  .primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_main_norm
```

So it is enough to deliver the analytic input:

```lean
||Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint
    - Q3.PSDpd.Step33.step33Shift16DigammaM6Main||
  <= Q3.PSDpd.Step33.step33Shift16DigammaM6MainComponentRadius
```

Do not rebuild the endpoint payload.  Do not touch CSV, ARadius, radius-floor,
LDL, Q3.Main, H1, or PO3.

## Additional checked landing target

Codex has also Lean-checked a more concrete component landing path:

```lean
Q3.PSDpd.Step33.step33_shift16_digamma_m6_center_component_abs_of_log_re_arg_abs

Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport
  .RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
  .primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_log_re_arg_abs
```

This target can consume:

```lean
|(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint
    - Q3.PSDpd.Step33.step33Shift16DigammaM6Main).re| <= mainReErr
|(Q3.digamma Q3.PSDpd.Step33.step33Shift16DigammaPoint
    - Q3.PSDpd.Step33.step33Shift16DigammaM6Main).im| <= mainImErr

|Real.log (Real.sqrt ((1664101 : Real) / (1600 : Real))) - logReCenter|
  <= logReErr
|Complex.arg Q3.PSDpd.Step33.step33Shift16DigammaPoint - argCenter|
  <= argErr
```

plus the algebraic-part recenter budgets and total `5e-22` budget.  It is
acceptable to deliver either the norm-based m6 inputs or these component
inputs; all landing wrappers are checked.
