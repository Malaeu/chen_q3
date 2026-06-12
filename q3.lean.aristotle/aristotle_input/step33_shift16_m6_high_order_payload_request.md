# Step33A.1-A Request: shift16 M6 high-order payload

Status note, 2026-06-09: this is the current live external-worker request for
the first Step33A.1-A raw-Omega endpoint anchor.

Narrow source theorem request:

```text
q3.lean.aristotle/aristotle_input/step33_shift16_m6_shift48_integral_remainder_source_request.md
```

If the source theorem

```lean
Q3.PSDpd.Step33.step33_shift16_m6_shift48_integral_remainder_bound
```

is proved first, use the existing shifted-integral-remainder receiver instead
of reproving the endpoint source inside this payload theorem.

The exact-prefix/Gauss absolute-tail route is blocked as-is: the tail premise
decays like `47.25 / seriesN`, while the first-anchor target radius is about
`6.33e-23`; ordinary exact-prefix replay would need `seriesN ~ 1e24`.

Do not use:

```text
exact-prefix absolute tail
seriesN ~ 1e24
trusted Arb numerics
CSV / ARadius / radius-floor / LDL edits
Q3.Main / H1 / PO3
sorry / admit / exact? / axiom / unsafe
```

## Live receiver

Use the checked receiver:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shift48_high_order_asymptotic_error_rectangles_and_component_interval_defects
```

It was added in:

```text
Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean
```

The endpoint and hRaw landing wrappers are checked in:

```lean
Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_shift48_high_order_asymptotic_error_rectangles_and_component_interval_defects_closedLogPi

Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_shift48_high_order_asymptotic_error_rectangles_and_component_interval_defects_closedLogPi
```

The concrete theorem to prove is:

```lean
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

theorem primaryFiniteRow0Parent0Split100Sub0_shift16_m6_term_payload_N16_of_shift48_high_order_generated :
    Step33Shift16M6FiniteTelescopeTermPayload := by
  -- proof here, no sorry/admit/exact?/axiom/unsafe

end Step33
end PSDpd
end Q3
```

## Required generated data

Generate exact rational proof data for:

```text
shiftRad defectRad shiftReRad shiftImRad
errorReLower errorReUpper errorImLower errorImUpper
termReLower termReUpper termImLower termImUpper : Fin 16 -> Real
termReRad termImRad termRad : Fin 16 -> Real
```

The error rectangle is for the high-order asymptotic remainder at the Step22
shift48 point:

```lean
Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
  Q3.digammaM6AsymptoticMain
    (step33Shift16DigammaPoint + (16 : Complex))
```

The receiver then needs:

```text
errorReLower <= error.re
error.re <= errorReUpper
errorImLower <= error.im
error.im <= errorImUpper
-shiftReRad <= errorReLower
errorReUpper <= shiftReRad
-shiftImRad <= errorImLower
errorImUpper <= shiftImRad
shiftReRad + shiftImRad <= shiftRad

Fin 16 interval bounds for:
  Q3.digammaM6StepDefect (step33Shift16DigammaPoint + n)

component radius containments:
  -termReRad n <= termReLower n
  termReUpper n <= termReRad n
  -termImRad n <= termImLower n
  termImUpper n <= termImRad n
  termReRad n + termImRad n <= termRad n

Finset.univ.sum termRad <= defectRad
shiftRad + defectRad <= ((1 : Real) / 12) * (step33Shift16DigammaPoint.re⁻¹)^14
```

## Analytic source theorem

The hard source is the high-order Euler-Maclaurin/Bernoulli digamma
asymptotic rectangle.  A useful helper theorem shape is:

Route review checkpoint, 2026-06-09:

```text
Pro/Louise chose the direct high-order rectangle route.
The exact-prefix/Gauss absolute-tail route is historical/support only unless
a separate acceleration/compression theorem is proved.

Aristotle project 5b903a21-fba1-4f42-949f-470b62c020b1 completed with errors
for the older shift16 M6 ball/main-norm request.  Its Step33Norm.lean contains
`sorry`, so do not integrate it.  It only confirms that the missing hard source
is Euler-Maclaurin/Stieltjes digamma asymptotic remainder infrastructure.
```

Preferred backend theorem shape:

```lean
theorem digammaM6_shift48_high_order_asymptotic_rect :
  -- exact repo-real statement may use a certificate structure instead
  -- of these four scalar bounds, but it must prove the same rectangle.
  errorReLower <=
      (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
        Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re
  ∧
      (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
        Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re <= errorReUpper
  ∧
      errorImLower <=
      (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
        Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im
  ∧
      (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
        Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im <= errorImUpper := by
  -- high-order Euler-Maclaurin/Bernoulli proof
```

Then feed that rectangle into:

```lean
theorem primaryFiniteRow0Parent0Split100Sub0_shift16_m6_shift48_high_order_error_rect :
  errorReLower <=
      (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
        Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re
  ∧
      (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
        Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re <= errorReUpper
  ∧
      errorImLower <=
      (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
        Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im
  ∧
      (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
        Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im <= errorImUpper := by
  -- high-order Euler-Maclaurin/Bernoulli proof
```

DLMF 5.11 is acceptable as an external reference for the standard
digamma/Psi asymptotic expansion and error-bound direction.  The Lean proof
must still come from local definitions and checked lemmas.

## Stop condition

Success:

```lean
primaryFiniteRow0Parent0Split100Sub0_shift16_m6_term_payload_N16_of_shift48_high_order_generated
```

compiles with no markers.

Blocker format:

```text
SHIFT48_HIGH_ORDER_ASYMPTOTIC_BLOCKER:
- theorem:
- file:
- z:
- z+48:
- order:
- failing premise:
  sector / norm lower / Bernoulli bound / remainder / rectangle / hTotal
- generated bound:
- required bound:
- excess:
- missing reusable lemma:
```
