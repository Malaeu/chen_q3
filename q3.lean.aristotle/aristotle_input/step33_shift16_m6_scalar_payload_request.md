# Step33A.1-A Request: shift16 M6 scalar finite-telescope payload

Status note, 2026-06-09: this scalar exact-prefix request is historical
fallback only.  The exact-prefix/Gauss absolute-tail route is blocked as-is by
the `seriesN ~ 1e24` tail sanity check.  Use it only if a separate
acceleration/compression theorem removes that absolute-tail blocker.

The current live request is:

```text
q3.lean.aristotle/aristotle_input/step33_shift16_m6_high_order_payload_request.md
```

## Goal

Prove a Lean-checked scalar payload for the current Q3 Step33A.1-A
raw-Omega first endpoint route.

Target file context:

```lean
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

theorem step33_shift16_m6_finite_telescope_scalar_payload :
    Step33Shift16M6FiniteTelescopeScalarPayload := by
  -- proof here

end Step33
end PSDpd
end Q3
```

Do not treat this scalar structure as the live strongest route.  It remains a
valid shortcut target only after the exact-prefix tail has been accelerated.

## Secondary checked receiver

Use this checked constructor from
`Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport`:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_scalar_payload_N16_of_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_defect_sum
```

This is the scalar shortcut route after the 2026-06-09 Pro/Louise review and
local `#check` audit.  The live preferred exact-prefix route is now the
component-interval term receiver:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_component_interval_defects
```

The shifted-integral receiver below is checked, but it is blocked as a
proof-producing target until a non-recursive source theorem for
`Q3.digammaM6IntegralRemainderBound (step33Shift16DigammaPoint + 16)` exists.

The exact-prefix receiver proves:

```lean
Step33Shift16M6FiniteTelescopeScalarPayload
```

from proof-producing data for the Step22 shift48 point:

```text
seriesN : Nat
gammaN : Nat
shiftRad defectRad shiftReRad shiftImRad tailRadius : Real
digammaReLower digammaReUpper digammaImLower digammaImUpper : Real
mainReLower mainReUpper mainImLower mainImUpper : Real

one complex tail norm bound for:
  step22OmegaArchWeightShiftedDigammaArg (1/20) 48

final exact-prefix Re/Im containment comparisons
Euler-Mascheroni bracket derived from gammaN
main M6 rectangle at step33Shift16DigammaPoint + 16
component rectangle containment into shiftReRad / shiftImRad
aggregate defect norm sum:
  (Finset.range 16).sum
    (fun n => ‖Q3.digammaM6StepDefect
      (step33Shift16DigammaPoint + (n : Complex))‖) <= defectRad
final total comparison:
  shiftRad + defectRad <=
    ((1 : Real) / (12 : Real)) *
      (step33Shift16DigammaPoint.re⁻¹) ^ 14
```

## Blocked shifted-integral receiver

Prefer this checked constructor from
`Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport`:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_scalar_payload_N16_of_shifted_integral_remainder_and_defect_sum
```

It proves:

```lean
Step33Shift16M6FiniteTelescopeScalarPayload
```

from the following proof-producing data:

```text
shiftRad defectRad : Real

shifted integral/asymptotic remainder:
  Q3.digammaM6IntegralRemainderBound
    (step33Shift16DigammaPoint + (16 : Complex))

first-omitted comparison:
  ((1 : Real) / (12 : Real)) *
      (((step33Shift16DigammaPoint + (16 : Complex)).re)⁻¹) ^ 14 <=
    shiftRad

aggregate defect norm sum:
  (Finset.range 16).sum
    (fun n : Nat =>
      ‖Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (n : Complex))‖) <= defectRad

final total comparison:
  shiftRad + defectRad <=
    ((1 : Real) / (12 : Real)) *
      (step33Shift16DigammaPoint.re⁻¹) ^ 14
```

This receiver is checked, but it is not the live proof-producing route right
now.  Local Lean inspection shows that the available
`Q3.digammaM6IntegralRemainderBound_of_finite_telescope` theorem still requires
a direct shifted norm premise `hShift` and therefore only moves the analytic
source problem farther right.

## Exact preferred constructor signature

```lean
def step33_shift16_m6_finite_telescope_scalar_payload_N16_of_shifted_integral_remainder_and_defect_sum
    (shiftRad defectRad : Real)
    (hShiftIntegral :
      Q3.digammaM6IntegralRemainderBound
        (step33Shift16DigammaPoint + (16 : Complex)))
    (hShiftRad :
      ((1 : Real) / (12 : Real)) *
          (((step33Shift16DigammaPoint + (16 : Complex)).re)⁻¹) ^ 14 <=
        shiftRad)
    (hDefects :
      (Finset.range 16).sum
          (fun n : Nat =>
            ‖Q3.digammaM6StepDefect
              (step33Shift16DigammaPoint + (n : Complex))‖) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeScalarPayload
```

## Exact-prefix constructor signature

The live constructor is:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_scalar_payload_N16_of_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_defect_sum
```

It has this shape:

```lean
def step33_shift16_m6_finite_telescope_scalar_payload_N16_of_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_defect_sum
    (seriesN gammaN : Nat)
    (shiftRad defectRad shiftReRad shiftImRad tailRadius : Real)
    (digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper : Real)
    (hTailNorm :
      (∑' n : Nat,
          ‖1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 +
                  ((n + seriesN : Nat) : Complex))‖) <=
        tailRadius)
    (hReLower :
      digammaReLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) -
          tailRadius)
    (hReUpper :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) +
          tailRadius <=
        digammaReUpper)
    (hImLower :
      digammaImLower <=
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) -
          tailRadius)
    (hImUpper :
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) +
          tailRadius <=
        digammaImUpper)
    (hMainReLower :
      mainReLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re)
    (hMainReUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re <=
      mainReUpper)
    (hMainImLower :
      mainImLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im)
    (hMainImUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im <=
      mainImUpper)
    (hShiftReLower : -shiftReRad <= digammaReLower - mainReUpper)
    (hShiftReUpper : digammaReUpper - mainReLower <= shiftReRad)
    (hShiftImLower : -shiftImRad <= digammaImLower - mainImUpper)
    (hShiftImUpper : digammaImUpper - mainImLower <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad)
    (hDefects :
      (Finset.range 16).sum
          (fun n : Nat =>
            ‖Q3.digammaM6StepDefect
              (step33Shift16DigammaPoint + (n : Complex))‖) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeScalarPayload
```

## Why this request is smaller than the previous one

The previous request targeted:

```lean
Step33Shift16M6FiniteTelescopeTermPayload
```

and required `Fin 16` Re/Im intervals for every M6 step defect.  The current
checked scalar receiver only needs one aggregate theorem:

```lean
(Finset.range 16).sum
  (fun n : Nat =>
    ‖Q3.digammaM6StepDefect
      (step33Shift16DigammaPoint + (n : Complex))‖) <= defectRad
```

If proving this aggregate sum is easier via per-term bounds, that is allowed,
but the final theorem should return the scalar payload.

## Existing checked landing wrappers

Once the scalar payload exists, these checked wrappers consume it:

```lean
Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_finite_telescope_scalar_payload_closedLogPi

Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_finite_telescope_scalar_payload_closedLogPi
```

There are also direct wrappers for this exact-prefix scalar shape:

```lean
Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_defect_sum_closedLogPi

Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_defect_sum_closedLogPi
```

And direct wrappers for the currently blocked shifted-integral-remainder scalar shape:

```lean
Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_shifted_integral_remainder_and_defect_sum_closedLogPi

Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_shifted_integral_remainder_and_defect_sum_closedLogPi
```

Do not rebuild endpoint/log-pi/hRaw receivers.

## Policy

Return only Lean code that compiles in this project.  Do not use or introduce:

```text
sorry
admit
exact?
axiom
unsafe
```

Do not touch or depend on:

```text
CSV
ARadius
radius floor
LDL
Q3.Main
H1/PO3
```

If the full scalar payload cannot be closed, return a smaller hole-free theorem
for exactly one of these blockers:

```lean
-- shifted digamma rectangle from exact-prefix series/tail
theorem step33_shift16_m6_shift48_exact_prefix_shifted_remainder_bound : ...

-- aggregate defect sum only
theorem step33_shift16_m6_defect_sum_bound :
  (Finset.range 16).sum
    (fun n : Nat =>
      ‖Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (n : Complex))‖) <= defectRad := ...

-- main M6 rectangle at the shifted point
theorem step33_shift16_m6_shift48_main_rectangle : ...
```

But do not return a theorem with holes.
