# Step33A.1-A Request: shift16 M6 first-omitted digamma remainder

## Goal

Prove the exact Lean theorem below in the Q3 project context:

```lean
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

theorem step33_shift16_digamma_m6_first_omitted_term_remainder_bound :
    ‖Q3.digamma step33Shift16DigammaPoint -
        (let z : Complex := step33Shift16DigammaPoint
        Complex.log z
          - ((1 : Complex) / (2 : Complex)) * z⁻¹
          - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
          + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
          - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
          + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
          - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
          + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
      ((1 : Real) / (12 : Real)) *
        (‖step33Shift16DigammaPoint‖⁻¹) ^ 14 := by
  -- proof here

end Step33
end PSDpd
end Q3
```

## Scope

This is the only requested theorem.  Do not prove the older broad
`m6_main_norm` target first unless it is an immediate consequence of the
theorem above.

It is also acceptable, and currently preferred if the local Euler-Maclaurin
theorem is naturally stated on a right half-plane, to prove the `re`-based
variant below:

```lean
theorem step33_shift16_digamma_m6_re_first_omitted_term_remainder_bound :
    ‖Q3.digamma step33Shift16DigammaPoint -
        (let z : Complex := step33Shift16DigammaPoint
        Complex.log z
          - ((1 : Complex) / (2 : Complex)) * z⁻¹
          - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
          + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
          - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
          + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
          - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
          + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
      ((1 : Real) / (12 : Real)) *
        (step33Shift16DigammaPoint.re⁻¹) ^ 14 := by
  -- proof here
```

That theorem is enough for the current endpoint/hRaw route through the checked
local adapters listed below.

Do not add or use:

```text
sorry
admit
exact?
axiom
unsafe
```

Do not touch:

```text
CSV
ARadius
radius floor
LDL
Q3.Main
H1
PO3
```

## Existing checked local facts

The following facts are already available from:

```lean
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport
```

Use these instead of redoing arithmetic:

```lean
Q3.PSDpd.Step33.step33Shift16DigammaPoint
Q3.PSDpd.Step33.step33Shift16DigammaPoint_re_pos
Q3.PSDpd.Step33.step33Shift16DigammaPoint_re_eq
Q3.PSDpd.Step33.step33Shift16DigammaPoint_ne_zero
Q3.PSDpd.Step33.step33Shift16DigammaPoint_normSq_eq
Q3.PSDpd.Step33.step33Shift16DigammaPoint_norm_eq_sqrt
Q3.PSDpd.Step33.step33Shift16DigammaPoint_norm_ge_32

Q3.PSDpd.Step33.step33Shift16DigammaM6Main
Q3.PSDpd.Step33.step33Shift16DigammaM6Main_eq_log_add_algebraicPart
Q3.PSDpd.Step33.step33Shift16DigammaM6FirstOmittedTermBound_le_componentRadius
Q3.PSDpd.Step33.step33Shift16DigammaM6ReFirstOmittedTermBound_le_componentRadius
Q3.PSDpd.Step33.step33_shift16_digamma_m6_expanded_asymptotic_bound_of_first_omitted_term_bound
Q3.PSDpd.Step33.step33_shift16_digamma_m6_main_norm_of_first_omitted_term_bound
Q3.PSDpd.Step33.step33_shift16_digamma_m6_expanded_asymptotic_bound_of_re_first_omitted_term_bound
Q3.PSDpd.Step33.step33_shift16_digamma_m6_main_norm_of_re_first_omitted_term_bound

Q3.kernel_norm_pow15_le_re
Q3.integrable_kernel_norm_pow15
Q3.integral_one_div_add_pos_pow15
Q3.integral_kernel_norm_pow15_le_re
Q3.digammaM6AsymptoticMain
Q3.digammaM6IntegralRemainderBound
Q3.digamma_m6_re_first_omitted_bound_of_integral_remainder
Q3.digammaM6StepDefect
Q3.digammaM6StepDefect_sum_range
Q3.digamma_m6_remainder_finite_telescope
Q3.digamma_m6_remainder_norm_le_of_finite_telescope
Q3.digammaM6IntegralRemainderBound_of_finite_telescope
Q3.PSDpd.Step33.step33_shift16_digamma_m6_re_first_omitted_term_bound_of_integral_remainder
Q3.PSDpd.Step33.step33_shift16_digamma_m6_re_first_omitted_term_bound_of_generic_integral_remainder
Q3.PSDpd.Step33.step33_shift16_digamma_m6_remainder_finite_telescope
Q3.PSDpd.Step33.step33_digammaM6IntegralRemainderBound_of_finite_telescope
Q3.PSDpd.Step33.step33_shift16_digamma_m6_re_first_omitted_term_bound_of_finite_telescope
```

The last fact is the checked bridge from the standard M6 integral-remainder
shape to the `re`-based first-omitted theorem.  It says that if the analytic
digamma remainder is bounded by:

```text
(7 / 6) * integral over Ioi 0 of 1 / ||x + z||^15
```

at `z = step33Shift16DigammaPoint`, then the required `re`-based
first-omitted bound follows.  Therefore the remaining analytic target may be
the narrower integral-remainder premise consumed by that bridge.

The preferred exact remaining theorem surface is now:

```lean
Q3.digammaM6IntegralRemainderBound
  Q3.PSDpd.Step33.step33Shift16DigammaPoint
```

This expands to the same order-15 integral-remainder estimate, with the M6
main term factored through `Q3.digammaM6AsymptoticMain`.

The hole-free Bernoulli algebraic cancellation table is also checked:

```lean
Q3.PSDpd.Step33.step33Shift16DigammaM6CancelD2
Q3.PSDpd.Step33.step33Shift16DigammaM6CancelD3
Q3.PSDpd.Step33.step33Shift16DigammaM6CancelD4
Q3.PSDpd.Step33.step33Shift16DigammaM6CancelD5
Q3.PSDpd.Step33.step33Shift16DigammaM6CancelD6
Q3.PSDpd.Step33.step33Shift16DigammaM6CancelD7
Q3.PSDpd.Step33.step33Shift16DigammaM6CancelD8
Q3.PSDpd.Step33.step33Shift16DigammaM6CancelD9
Q3.PSDpd.Step33.step33Shift16DigammaM6CancelD10
Q3.PSDpd.Step33.step33Shift16DigammaM6CancelD11
Q3.PSDpd.Step33.step33Shift16DigammaM6CancelD12
Q3.PSDpd.Step33.step33Shift16DigammaM6CancelD13
Q3.PSDpd.Step33.step33Shift16DigammaM6CancelD14
Q3.PSDpd.Step33.step33Shift16DigammaM6LeadingD15
```

These facts close only rational coefficient algebra and downstream arithmetic.
They do not assert the analytic Euler-Maclaurin or digamma asymptotic theorem.

## Mathematical target

Use a high-order Euler-Maclaurin/Bernoulli asymptotic theorem for the digamma
function, specialized at:

```lean
z = step33Shift16DigammaPoint = 129 / 4 + I * (1 / 40)
```

The main expression is:

```text
log z
  - 1/(2 z)
  - 1/(12 z^2)
  + 1/(120 z^4)
  - 1/(252 z^6)
  + 1/(240 z^8)
  - 1/(132 z^10)
  + 691/(32760 z^12)
```

This is:

```text
log z - 1/(2z) - sum_{k=1..6} B_{2k}/(2k z^(2k))
```

with:

```text
B2 = 1/6
B4 = -1/30
B6 = 1/42
B8 = -1/30
B10 = 5/66
B12 = -691/2730
```

The required remainder bound is the first omitted term bound:

```text
||remainder|| <= (1 / 12) * ||z||^(-14)
```

Here `1 / 12` is `|B14| / 14`, since `B14 = 7 / 6`.

## Local proof context

Relevant local files:

```lean
Q3.DigammaSeries
Q3.DigammaRemainder
Q3.Proofs.PSD_CenteredCoeffAnalyticABoundsBackend
Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport
```

`Q3.DigammaRemainder` contains a checked N=1 Stieltjes/Euler-Maclaurin
digamma remainder proof:

```lean
Q3.digamma_stieltjes_identity
Q3.digamma_stieltjes_complex_remainder_bound
```

That theorem is too coarse for this endpoint, but its structure is a useful
template for integration by parts, Bernoulli terms, and norming the remainder.
The order-15 kernel domination, integrability, exact real-tail integral, and
complex-kernel integral-bound lemmas listed above are already available for
the M6 first-omitted remainder integral.
The local bridge
`step33_shift16_digamma_m6_re_first_omitted_term_bound_of_integral_remainder`
then converts that integral-remainder estimate into the checked endpoint route.
The generic bridge
`Q3.digamma_m6_re_first_omitted_bound_of_integral_remainder` performs the same
conversion for any `z` with `0 < z.re`, and the Step33 theorem
`step33_shift16_digamma_m6_re_first_omitted_term_bound_of_generic_integral_remainder`
specializes it to the active endpoint.

The finite right-shift/telescoping receiver is also checked:

```lean
Q3.digammaM6StepDefect
Q3.digammaM6StepDefect_sum_range
Q3.digamma_m6_remainder_finite_telescope
Q3.digamma_m6_remainder_norm_le_of_finite_telescope
Q3.digammaM6IntegralRemainderBound_of_finite_telescope

Q3.PSDpd.Step33.step33_shift16_digamma_m6_remainder_finite_telescope
Q3.PSDpd.Step33.step33_digammaM6IntegralRemainderBound_of_finite_telescope
Q3.PSDpd.Step33.step33_shift16_digamma_m6_re_first_omitted_term_bound_of_finite_telescope
```

It reduces the `m = 6` remainder at a right-half-plane point to the remainder
at `z + N` plus a finite sum of explicit M6 main-term step defects.  Future
proof attempts should reuse this receiver instead of reproving the digamma
finite-shift algebra.

The norm and endpoint variants are also checked.  Therefore a future proof may
close the active endpoint by supplying only rational/computable bounds for:

```text
||digamma(z + N) - M6(z + N)|| <= shiftRad
sum_{n<N} ||M6StepDefect(z+n)|| <= defectRad
shiftRad + defectRad <= target radius
```

at `z = step33Shift16DigammaPoint`.

## Downstream already checked

Once the theorem requested above is available, the repo already has checked
adapters into the first endpoint and first hRaw package:

```lean
Q3.PSDpd.Step33.step33_shift16_digamma_m6_main_norm_of_first_omitted_term_bound

Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport
  .RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
  .primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_first_omitted_term_bound_closedLogPi

Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport
  .RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
  .primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_first_omitted_term_bound_closedLogPi
```

The `re`-based variant is also wired through checked adapters:

```lean
Q3.PSDpd.Step33.step33_shift16_digamma_m6_main_norm_of_re_first_omitted_term_bound

Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport
  .RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
  .primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_re_first_omitted_term_bound_closedLogPi

Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport
  .RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
  .primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_re_first_omitted_term_bound_closedLogPi
```

So the output should not rebuild endpoint payloads or log-pi/fixed-center
facades.

## Output expectation

Return only Lean code that compiles in this project.  It is acceptable to add
helper lemmas for the high-order Euler-Maclaurin/Bernoulli identity and
remainder bound, but the final delivered theorem should be the exact theorem
in the Goal section, the `re`-based variant in the Scope section, or a theorem
immediately usable to prove one of them without any new analytic assumptions.
