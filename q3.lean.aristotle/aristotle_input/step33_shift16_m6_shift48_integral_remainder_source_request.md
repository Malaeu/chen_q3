# Step33A.1-A Request: shift16 M6 shift48 integral-remainder source

Status note, 2026-06-09: this is the narrow source-theorem request behind the
current high-order payload route.

Do not prove the whole endpoint.  Do not revive the exact-prefix/Gauss
absolute-tail route.  The target is only the far-right M6 digamma
Euler-Maclaurin/Stieltjes source theorem at the Step22 shift48 point.

## Goal

Prove this theorem in the real Q3 project context:

```lean
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

theorem step33_shift16_m6_shift48_integral_remainder_bound :
    Q3.digammaM6IntegralRemainderBound
      (step33Shift16DigammaPoint + (16 : Complex)) := by
  -- proof here, no sorry/admit/exact?/axiom/unsafe

end Step33
end PSDpd
end Q3
```

Expanded target definition from `Q3.DigammaRemainder`:

```lean
def Q3.digammaM6IntegralRemainderBound (z : Complex) : Prop :=
  ‖Q3.digamma z - Q3.digammaM6AsymptoticMain z‖ <=
    ((7 : Real) / (6 : Real)) *
      ∫ x in Set.Ioi (0 : Real), 1 / ‖(x : Complex) + z‖ ^ 15
```

Here:

```lean
z = step33Shift16DigammaPoint + (16 : Complex)
```

and the checked identity

```lean
Q3.PSDpd.Step33.step33Shift16DigammaPoint_add_16_eq_generated_shift48
```

identifies this with the Step22 shift48 point:

```lean
CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
  ((1 : Real) / (20 : Real)) 48
```

## Existing consumers

Once the source theorem compiles, it feeds existing checked receivers:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_integral_remainder_component_interval_defects

Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shift48_high_order_asymptotic_error_rectangles_and_component_interval_defects
```

and then the checked endpoint/hRaw wrappers:

```lean
Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_shift48_high_order_asymptotic_error_rectangles_and_component_interval_defects_closedLogPi

Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_shift48_high_order_asymptotic_error_rectangles_and_component_interval_defects_closedLogPi
```

## Available local infrastructure

Use these from `Q3.DigammaRemainder` and the support import.  Do not reprove
their statements unless the proof genuinely needs a missing intermediate.

```lean
Q3.digammaM6AsymptoticMain
Q3.digammaM6IntegralRemainderBound
Q3.digamma_m6_re_first_omitted_bound_of_integral_remainder
Q3.digamma_m6_remainder_finite_telescope
Q3.digamma_m6_remainder_norm_le_of_finite_telescope
Q3.digammaM6IntegralRemainderBound_of_finite_telescope
Q3.integral_kernel_norm_pow15_le_re

Q3.PSDpd.Step33.step33Shift16DigammaPoint
Q3.PSDpd.Step33.step33Shift16DigammaPoint_re_pos
Q3.PSDpd.Step33.step33Shift16DigammaPoint_add_nat_re_pos
Q3.PSDpd.Step33.step33Shift16DigammaPoint_add_16_eq_generated_shift48
```

The current support file also has checked rational Bernoulli cancellation
lemmas:

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

## Intended proof route

Use a real Euler-Maclaurin/Stieltjes digamma remainder proof for the m=6
Bernoulli asymptotic main, specialized to the fixed right-half-plane point
`step33Shift16DigammaPoint + 16`.

The theorem may be proved either:

1. directly from the local `Q3.digamma` / `Q3.digammaM6AsymptoticMain`
   definitions and an Euler-Maclaurin remainder identity, or
2. by adding one reusable local lemma in `Q3.DigammaRemainder` that proves
   `Q3.digammaM6IntegralRemainderBound z` for all `z` with `0 < z.re`, then
   specializing it here.

If a reusable general lemma is easier, prefer this shape:

```lean
lemma Q3.digammaM6IntegralRemainderBound_of_re_pos
    (z : Complex) (hz : 0 < z.re) :
    Q3.digammaM6IntegralRemainderBound z := by
  -- Euler-Maclaurin/Stieltjes proof
```

Then the target theorem should be:

```lean
theorem step33_shift16_m6_shift48_integral_remainder_bound :
    Q3.digammaM6IntegralRemainderBound
      (step33Shift16DigammaPoint + (16 : Complex)) := by
  exact Q3.digammaM6IntegralRemainderBound_of_re_pos
    (step33Shift16DigammaPoint + (16 : Complex))
    (step33Shift16DigammaPoint_add_nat_re_pos 16)
```

## Hard constraints

```text
No sorry/admit/exact?/axiom/unsafe.
No exact-prefix absolute tail.
No seriesN ~ 1e24.
No trusted Arb numerics.
No CSV/ARadius/radius-floor/LDL edits.
No Q3.Main/H1/PO3.
Do not weaken theorem statements.
```

## Stop condition

Success:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_shift48_integral_remainder_bound
```

compiles in the Q3 project with no holes.

If blocked, report:

```text
SHIFT48_M6_INTEGRAL_REMAINDER_SOURCE_BLOCKER:
- theorem:
- file:
- missing lemma:
- exact Lean goal:
- failed proof route:
- whether a reusable general lemma is plausible:
- smallest next lemma to request:
```
