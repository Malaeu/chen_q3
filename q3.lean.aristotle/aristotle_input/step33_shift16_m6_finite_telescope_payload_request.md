# Step33A.1-A Request: shift16 M6 finite-telescope payload

Status note, 2026-06-09: this exact-prefix request is superseded as the live
proof-producing route.  A local tail sanity check showed that the absolute
complex-tail premise below has size about `47.25 / seriesN`, so matching the
`~6.33e-23` first-anchor target would require `seriesN ~ 1e24`.  That is not
proof-operational without a separate acceleration theorem.

Keep this file only as historical/support documentation for the checked
exact-prefix receivers.  The current live request is:

```text
q3.lean.aristotle/aristotle_input/step33_shift16_m6_high_order_payload_request.md
```

The checked, now non-live, Step22 shift48 exact-prefix term receiver is:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_component_interval_defects
```

Do not target this theorem unless a new acceleration/compression theorem
removes the absolute-tail `seriesN ~ 1e24` blocker:

```lean
theorem primaryFiniteRow0Parent0Split100Sub0_shift16_m6_term_payload_N16_of_shift48_exact_prefix_generated :
    Step33Shift16M6FiniteTelescopeTermPayload := by
  -- proof here, no sorry/admit/exact?/axiom/unsafe
```

Use `seriesN`, `gammaN`, one complex tail norm bound at Step22 shift48, exact
finite-prefix Re/Im containment comparisons, one rectangle for
`Q3.digammaM6AsymptoticMain (step33Shift16DigammaPoint + 16)`, `Fin 16` Re/Im
intervals for `Q3.digammaM6StepDefect (step33Shift16DigammaPoint + n)`,
component-radius containment, term-radius comparisons, one `Finset.univ`
defect sum comparison, and one final total-radius comparison.

## Goal

Prove a Lean-checked payload for the current Step33A.1-A first raw-Omega
endpoint route:

```lean
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

theorem step33_shift16_m6_finite_telescope_term_payload :
    Step33Shift16M6FiniteTelescopeTermPayload := by
  -- proof here

end Step33
end PSDpd
end Q3
```

Historical generic fallback: the proof may choose the payload fields:

```lean
N : Nat
shiftRad : Real
defectRad : Real
termRad : Nat -> Real
```

The live first attempt is fixed at `N = 16` through the shift48 exact-prefix
receiver below.  A different concrete `N` is only acceptable after a route
audit; do not silently switch away from the fixed first anchor.

There is checked support for building the payload from a shifted
integral-remainder theorem plus explicit term bounds:

```lean
Q3.PSDpd.Step33.step33Shift16DigammaPoint_add_nat_re_pos
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_scalar_payload_of_shifted_integral_remainder
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_of_shifted_integral_remainder
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_of_shifted_integral_remainder_component_defects
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_of_shifted_integral_remainder_component_interval_defects
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_integral_remainder_component_interval_defects
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_of_shifted_remainder_bound_component_interval_defects
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_remainder_bound_component_interval_defects
Q3.PSDpd.Step33.complex_norm_sub_le_of_component_rectangles
Q3.PSDpd.Step33.step33_shift16_m6_shifted_remainder_bound_of_component_rectangles
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_component_rectangles_and_component_interval_defects
```

Using that helper is not the current live route.  It can reduce `hShift` to:

```lean
Q3.digammaM6IntegralRemainderBound
  (Q3.PSDpd.Step33.step33Shift16DigammaPoint + (N : Complex))
```

plus the rational comparison:

```lean
((1 : Real) / (12 : Real)) *
    (((Q3.PSDpd.Step33.step33Shift16DigammaPoint + (N : Complex)).re)⁻¹) ^ 14
  <= shiftRad
```

## Exact payload contract

The target structure is already checked in:

```lean
Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport
```

It is:

```lean
structure Step33Shift16M6FiniteTelescopeTermPayload where
  N : Nat
  shiftRad : Real
  defectRad : Real
  termRad : Nat -> Real
  hShift :
    ‖Q3.digamma (step33Shift16DigammaPoint + (N : Complex)) -
        Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (N : Complex))‖ <= shiftRad
  hDefectTerm : ∀ n : Nat, n < N ->
    ‖Q3.digammaM6StepDefect
      (step33Shift16DigammaPoint + (n : Complex))‖ <= termRad n
  hDefectSum :
    (Finset.range N).sum termRad <= defectRad
  hTotal :
    shiftRad + defectRad <=
      ((1 : Real) / (12 : Real)) *
        (step33Shift16DigammaPoint.re⁻¹) ^ 14
```

## Historical shifted-integral fixed-N receiver

This checked fixed `N = 16` component-interval receiver is retained as support:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_integral_remainder_component_interval_defects
```

It accepts:

```lean
shiftRad defectRad : Real
termReLower termReUpper termImLower termImUpper
  termReRad termImRad termRad : Fin 16 -> Real
```

plus these proof obligations:

```lean
Q3.digammaM6IntegralRemainderBound
  (step33Shift16DigammaPoint + (16 : Complex))

((1 : Real) / (12 : Real)) *
    (((step33Shift16DigammaPoint + (16 : Complex)).re)⁻¹) ^ 14 <= shiftRad

∀ n : Fin 16,
  termReLower n <=
    (Q3.digammaM6StepDefect
      (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re

∀ n : Fin 16,
    (Q3.digammaM6StepDefect
      (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re <=
  termReUpper n

∀ n : Fin 16,
  termImLower n <=
    (Q3.digammaM6StepDefect
      (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im

∀ n : Fin 16,
    (Q3.digammaM6StepDefect
      (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im <=
  termImUpper n

∀ n : Fin 16, -termReRad n <= termReLower n
∀ n : Fin 16, termReUpper n <= termReRad n
∀ n : Fin 16, -termImRad n <= termImLower n
∀ n : Fin 16, termImUpper n <= termImRad n
∀ n : Fin 16, termReRad n + termImRad n <= termRad n

(Finset.univ.sum (fun n : Fin 16 => termRad n)) <= defectRad

shiftRad + defectRad <=
  ((1 : Real) / (12 : Real)) *
    (step33Shift16DigammaPoint.re⁻¹) ^ 14
```

This receiver internally converts the `Fin 16` tables into the older
`Nat`/`Finset.range 16` adapter.  It is better than the generic `N : Nat`
interface, but the live exact-prefix shift48 receiver below is still preferred.

## Alternative direct-shift receiver

If proving the shifted integral-remainder theorem is the hard part, use the
direct-shift fixed `N = 16` receiver instead:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_remainder_bound_component_interval_defects
```

It has the same `Fin 16` component interval obligations as the shifted-integral
receiver above, but replaces:

```lean
Q3.digammaM6IntegralRemainderBound
  (step33Shift16DigammaPoint + (16 : Complex))
```

and the `hShiftRad` comparison with the direct premise:

```lean
‖Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
    Q3.digammaM6AsymptoticMain
      (step33Shift16DigammaPoint + (16 : Complex))‖ <= shiftRad
```

The output is still the same:

```lean
Q3.PSDpd.Step33.Step33Shift16M6FiniteTelescopeTermPayload
```

## Preferred rectangle-to-payload receiver

The lowest-noise receiver is now:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_component_rectangles_and_component_interval_defects
```

Use it when the proof can provide:

```text
digamma(z+16) Re/Im rectangle
digammaM6AsymptoticMain(z+16) Re/Im rectangle
shiftReRad / shiftImRad bounds for the component difference
the same Fin 16 defect interval data as above
```

Lean then derives the shifted remainder norm internally with:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_shifted_remainder_bound_of_component_rectangles
```

If the term-payload target is too large, it is acceptable to return a
hole-free helper theorem proving one of:

```lean
∀ n : Nat, n < 16 ->
  ‖Q3.digammaM6StepDefect
    (step33Shift16DigammaPoint + (n : Complex))‖ <= termRad n

(Finset.range 16).sum termRad <= defectRad

‖Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
    Q3.digammaM6AsymptoticMain
      (step33Shift16DigammaPoint + (16 : Complex))‖ <= shiftRad
```

but the best output is the full structure theorem above.

## Already checked local bridge

Once the payload exists, these checked theorems finish the first endpoint and
first hRaw gate:

```lean
Q3.PSDpd.Step33.step33_shift16_digamma_m6_re_first_omitted_term_bound_of_finite_telescope_term_payload

Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_shift16_m6_finite_telescope_term_payload_closedLogPi

Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0_hRawCenterCoeffAbs_of_shift16_m6_finite_telescope_term_payload_closedLogPi
```

So do not rebuild endpoint certificates or log-pi/fixed-center facades.

## Available checked facts

Use these rather than reproving local arithmetic:

```lean
Q3.PSDpd.Step33.step33Shift16DigammaPoint
Q3.PSDpd.Step33.step33Shift16DigammaPoint_re_pos
Q3.PSDpd.Step33.step33Shift16DigammaPoint_re_eq
Q3.PSDpd.Step33.step33Shift16DigammaPoint_ne_zero
Q3.PSDpd.Step33.step33Shift16DigammaPoint_normSq_eq
Q3.PSDpd.Step33.step33Shift16DigammaPoint_norm_eq_sqrt
Q3.PSDpd.Step33.step33Shift16DigammaPoint_norm_ge_32

Q3.digammaM6AsymptoticMain
Q3.digammaM6StepDefect
Q3.digammaM6StepDefect_sum_range
Q3.digamma_m6_remainder_finite_telescope
Q3.digamma_m6_remainder_norm_le_of_finite_telescope
Q3.PSDpd.Step33.step33_shift16_digamma_m6_remainder_finite_telescope
Q3.PSDpd.Step33.step33_shift16_digamma_m6_re_first_omitted_term_bound_of_finite_telescope
Q3.PSDpd.Step33.step33Shift16DigammaPoint_add_nat_re_pos
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_scalar_payload_of_shifted_integral_remainder
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_of_shifted_integral_remainder

Q3.kernel_norm_pow15_le_re
Q3.integrable_kernel_norm_pow15
Q3.integral_one_div_add_pos_pow15
Q3.integral_kernel_norm_pow15_le_re
```

The checked payload adapter already performs:

```text
per-n defect bounds
-> finite sum defect bound
-> scalar payload
-> re-first-omitted M6 endpoint bound
-> first endpoint / hRaw gate
```

The newest checked adapter also accepts componentwise defect bounds:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_of_shifted_integral_remainder_component_defects
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_of_shifted_integral_remainder_component_interval_defects
```

So a generated proof may give intervals, for each `n < N`:

```lean
termReLower n <=
  (Q3.digammaM6StepDefect (step33Shift16DigammaPoint + (n : Complex))).re
(Q3.digammaM6StepDefect (step33Shift16DigammaPoint + (n : Complex))).re
  <= termReUpper n
termImLower n <=
  (Q3.digammaM6StepDefect (step33Shift16DigammaPoint + (n : Complex))).im
(Q3.digammaM6StepDefect (step33Shift16DigammaPoint + (n : Complex))).im
  <= termImUpper n
-termReRad n <= termReLower n
termReUpper n <= termReRad n
-termImRad n <= termImLower n
termImUpper n <= termImRad n
termReRad n + termImRad n <= termRad n
```

The older component-absolute form is also accepted:

```lean
|(Q3.digammaM6StepDefect (step33Shift16DigammaPoint + (n : Complex))).re|
  <= termReRad n
|(Q3.digammaM6StepDefect (step33Shift16DigammaPoint + (n : Complex))).im|
  <= termImRad n
termReRad n + termImRad n <= termRad n
```

Lean then derives the complex norm bound using the checked
`complex_norm_le_abs_re_add_abs_im` bridge.

## Mathematical guidance

At `z = step33Shift16DigammaPoint`, Lean has:

```text
z = 129/4 + I*(1/40)
z.re = 129/4
```

The target total radius is:

```lean
((1 : Real) / (12 : Real)) *
  (Q3.PSDpd.Step33.step33Shift16DigammaPoint.re⁻¹) ^ 14
```

A useful route is:

1. Bound the far-right shifted remainder at `z + N`.
2. Bound each explicit `Q3.digammaM6StepDefect (z+n)`.
3. Sum those term bounds.
4. Prove the final rational inequality against the total target radius.

Historical shifted-integral route, now superseded by the exact-prefix shift48
receiver:

1. Prove the standard shifted integral-remainder theorem at `z + N`.
2. Use
   `step33_shift16_m6_finite_telescope_term_payload_of_shifted_integral_remainder`
   to turn it into `hShift`.
3. Use interval per-term `M6StepDefect` Re/Im bounds, then use the
   component-interval adapter to derive component absolute bounds and complex
   norm bounds.
4. Prove one exact rational sum comparison and the final total-radius
   comparison.

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
H1
PO3
```

## 2026-06-09 local receiver update

Earlier local receiver update: the checked fixed-`N = 16` receiver:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_digamma_series_prefix_tail_abs_main_rectangles_and_component_interval_defects
```

It consumes:

```text
seriesN prefix/tail Re/Im bounds for digamma(step33Shift16DigammaPoint + 16)
EulerGamma lower/upper bounds
Re/Im rectangle bounds for digammaM6AsymptoticMain(step33Shift16DigammaPoint + 16)
shift rectangle containment comparisons
Fin 16 Re/Im interval bounds for digammaM6StepDefect(step33Shift16DigammaPoint + n)
component-radius containments
term-radius comparisons
one Finset.univ sum bound
one final total-radius comparison
```

This receiver is Lean-checked locally and is better than any generic `N : Nat`
theorem request for the first endpoint, but it is superseded by the shift48
exact-prefix receiver below.

## 2026-06-09 shift48 receiver update

The Step22-shifted target is:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shift48_digamma_series_prefix_tail_abs_main_rectangles_and_component_interval_defects
```

Use Step22 notation for the far-right digamma series:

```lean
Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
  ((1 : Real) / (20 : Real)) 48
```

Lean has checked:

```lean
Q3.PSDpd.Step33.step33Shift16DigammaPoint_add_16_eq_generated_shift48
```

so this is exactly the same point as `step33Shift16DigammaPoint + 16`.

## 2026-06-09 exact-prefix complex-tail receiver update

The preferred target is now:

```lean
Q3.PSDpd.Step33.step33_shift16_m6_finite_telescope_term_payload_N16_of_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_component_interval_defects
```

This target removes separate `gammaLower/gammaUpper`, prefix lower/upper, and
separate Re/Im tail proof surfaces.  Provide:

```text
gammaN
seriesN
one complex tail norm bound at Step22 shift48
final Re/Im containment comparisons using exact prefix sums
main M6 Re/Im rectangle bounds
Fin 16 defect Re/Im interval bounds
component radius and term/sum/total comparisons
```
