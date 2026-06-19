# Step33A.1-A Request: shift16 M6 integral-remainder source at z0

Status note, 2026-06-20: this is the current smallest proof-producing
source-theorem request for the first Step33A.1-A raw-Omega endpoint anchor.
It supersedes the shift48 high-order rectangle route as the next theorem to
request first.  The shift48 route remains checked support/fallback, but it
adds telescope, defect-table, and rectangle obligations before the missing
M6 Euler-Maclaurin/Stieltjes source is proved.

Do not prove the whole endpoint.  Do not edit CSV, ARadius, radius-floor,
LDL, Q3.Main, H1, or PO3.  Do not add `sorry`, `admit`, `exact?`, `axiom`,
or `unsafe`.

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

theorem step33_shift16_digamma_m6_integral_remainder_bound :
    Q3.digammaM6IntegralRemainderBound step33Shift16DigammaPoint := by
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
z = step33Shift16DigammaPoint = 129 / 4 + I * (1 / 40)
```

The M6 main term is:

```text
log z
  - 1/(2z)
  - 1/(12z^2)
  + 1/(120z^4)
  - 1/(252z^6)
  + 1/(240z^8)
  - 1/(132z^10)
  + 691/(32760 z^12)
```

## Existing consumers

Once this source theorem compiles, it feeds existing checked receivers without
adding the shift48 finite-telescope layer:

```lean
Q3.PSDpd.Step33.step33_shift16_digamma_m6_re_first_omitted_term_bound_of_generic_integral_remainder
```

and then:

```lean
Q3.PSDpd.Step33.step33_shift16_digamma_m6_main_norm_of_re_first_omitted_term_bound

Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_re_first_omitted_term_bound_closedLogPi

Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_re_first_omitted_term_bound_closedLogPi
```

Therefore the proof-producing route is:

```text
step33_shift16_digamma_m6_integral_remainder_bound
  -> re_first_omitted bound
  -> m6 main norm
  -> endpoint interval cert
  -> hRawCenterCoeffAbs
```

## Why this request is smaller than the alternatives

Option A, the generic theorem

```lean
∀ z : Complex, 0 < z.re -> Q3.digammaM6IntegralRemainderBound z
```

is mathematically cleaner, but it asks Lean to prove the whole half-plane
Euler-Maclaurin/Stieltjes M6 theorem before the first active endpoint can move.

Option C, the shifted `z0 + 16` high-order rectangle, remains useful support,
but it adds finite-telescope, component-defect, total-radius, and rectangle
payload obligations.  Those obligations are not the first missing source
theorem.

Option D can help only after a proof-grade M6 source or rectangle is available;
by itself it does not close the source premise.

## Available local infrastructure

Use these from `Q3.DigammaRemainder` and the Step33 support import.  Do not
reprove their statements unless the proof genuinely needs a missing
intermediate.

```lean
Q3.digammaM6AsymptoticMain
Q3.digammaM6IntegralRemainderBound
Q3.digamma_m6_re_first_omitted_bound_of_integral_remainder
Q3.integral_kernel_norm_pow15_le_re

Q3.PSDpd.Step33.step33Shift16DigammaPoint
Q3.PSDpd.Step33.step33Shift16DigammaPoint_re_pos
Q3.PSDpd.Step33.step33Shift16DigammaPoint_re_eq
Q3.PSDpd.Step33.step33Shift16DigammaPoint_ne_zero
Q3.PSDpd.Step33.step33Shift16DigammaPoint_normSq_eq
Q3.PSDpd.Step33.step33Shift16DigammaPoint_norm_eq_sqrt
Q3.PSDpd.Step33.step33Shift16DigammaPoint_norm_ge_32
```

The support file also has checked rational Bernoulli cancellation lemmas:

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

These close coefficient algebra only.  They do not prove the analytic
Euler-Maclaurin/Stieltjes M6 remainder theorem.

## Proof skeleton

1. Start from the existing N=1 Stieltjes/Euler-Maclaurin development in
   `Q3.DigammaRemainder`.
2. Generalize the integration-by-parts chain far enough to express the M6
   remainder after the `z^-12` term.
3. Reuse the checked Bernoulli cancellation table for the rational main-term
   coefficients.
4. Bound the remaining kernel by the repository's `digammaM6IntegralRemainderBound`
   right-hand side:

   ```lean
   ((7 : Real) / (6 : Real)) *
     ∫ x in Set.Ioi (0 : Real), 1 / ‖(x : Complex) + z‖ ^ 15
   ```

5. Specialize at `step33Shift16DigammaPoint` using
   `step33Shift16DigammaPoint_re_pos`.

## First likely Lean obstruction

`Q3.DigammaRemainder` currently contains the checked N=1 Stieltjes remainder
proof and M6 receiver definitions, but not the six-step M6
Euler-Maclaurin/Stieltjes identity.  The first hard Lean obstruction is
expected to be a reusable integration-by-parts/remainder lemma whose final
coefficient, power, and norm must match exactly:

```text
coefficient = 7 / 6
kernel power = 15
target = Q3.digammaM6IntegralRemainderBound step33Shift16DigammaPoint
```

External references such as DLMF 5.11 can guide the theorem shape, but the
accepted proof object must be local Lean code.
