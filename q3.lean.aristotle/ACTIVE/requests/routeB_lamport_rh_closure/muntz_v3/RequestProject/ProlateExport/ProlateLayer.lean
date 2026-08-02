/-
Provenance source: q3.lean.aristotle/Q3/Proofs/RouteB/ProlateLayer.lean
Source commit: 6e78e4e54fe972fc756cc1843a96d6ae8d94f9d5
Source Git blob: 71f523672481aa6449c93fd84a5e3ad7db4196f6
Provenance SHA-256: 3c2099c97df6cd0fb45f7b367d24898d11c031ed297fe9031b25ee5b9dc0edf4
exported verbatim, imports unchanged
Export date: 2026-08-02
-/

import Mathlib

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- The formal prolate differential expression

`PW_lambda f = -d/dx ((lambda^2-x^2) d/dx f)
  + (2*pi*lambda*x)^2 f`.

This is only the pointwise expression.  It carries no operator domain,
self-adjointness, spectral, or existence assertion.

Source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/011_concrete_htrial_source_lock.answer.md:69-73`;
`docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:33-43`;
`literature/zotero/H8ULBMAL/fulltext.md:1293-1297`.
-/
def prolateWaveExpression
    (lambda : ℝ)
    (f : ℝ → ℂ)
    (x : ℝ) : ℂ :=
  -fderiv ℝ
      (fun y : ℝ =>
        (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * (fderiv ℝ f y) 1))
      x 1
    + (((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) * f x

/-- Data wrapper for the formal prolate differential expression.

`action_eq` pins the stored action to `prolateWaveExpression`; this structure
does not assert a domain, symmetry, self-adjointness, or any eigenfunction.
-/
structure ProlateOperatorData where
  lambda : ℝ
  action : (ℝ → ℂ) → ℝ → ℂ
  action_eq : action = prolateWaveExpression lambda

/-- A source-indexed pair of prolate-mode candidates.

All analytic facts are fields (hypotheses), not existence theorems.  The index
lock is `h0 <-> chi0` and `h4 <-> chi2`; in particular there is no `chi4`
field.  No sign or ordering hypothesis is included.

Source lock:
`docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:45-75,93-112,232-243`;
`ACTIVE/requests/routeB_lamport_rh_closure/D0_5_GROUND_AND_TRIAL_TYPES.md:55-75`.
-/
structure ProlatePair where
  pw : ProlateOperatorData
  h0 : ℝ → ℂ
  h4 : ℝ → ℂ
  chi0 : ℝ
  chi2 : ℝ
  I0 : ℝ
  I4 : ℝ
  h0_even : Function.Even h0
  h4_even : Function.Even h4
  h0_support : Function.support h0 ⊆ Icc (-pw.lambda) pw.lambda
  h4_support : Function.support h4 ⊆ Icc (-pw.lambda) pw.lambda
  h0_integrable : Integrable h0
  h4_integrable : Integrable h4
  h0_sqNorm_integrable : Integrable (fun x : ℝ => ‖h0 x‖ ^ 2)
  h4_sqNorm_integrable : Integrable (fun x : ℝ => ‖h4 x‖ ^ 2)
  h0_normalized : (∫ x : ℝ, ‖h0 x‖ ^ 2) = 1
  h4_normalized : (∫ x : ℝ, ‖h4 x‖ ^ 2) = 1
  I0_eq_integral : (I0 : ℂ) = ∫ x : ℝ, h0 x
  I4_eq_integral : (I4 : ℂ) = ∫ x : ℝ, h4 x
  h0_fourier_center : (I0 : ℂ) = (chi0 : ℂ) * h0 0
  h4_fourier_center : (I4 : ℂ) = (chi2 : ℂ) * h4 0

/-- The source denominator `sqrt(I0^2 + I4^2)`.

Nonvanishing is intentionally not asserted in the type layer.
-/
def ProlatePair.normalizingDenominator (P : ProlatePair) : ℝ :=
  Real.sqrt (P.I0 ^ 2 + P.I4 ^ 2)

/-- The canonical plus-phase two-mode packet

`(I4*h0 - I0*h4) / sqrt(I0^2 + I4^2)`.

This supplies the `hTrial_m` input of the existing D0 `E_star -> gTrial_m`
chain.  Nonzero normalization and all sign claims belong to later layers.

Source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_5_GROUND_AND_TRIAL_TYPES.md:55-92`;
`docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:93-112`.
-/
def prolateCombination (P : ProlatePair) (x : ℝ) : ℂ :=
  ((P.I4 : ℂ) * P.h0 x - (P.I0 : ℂ) * P.h4 x) /
    (P.normalizingDenominator : ℂ)

@[simp] theorem ProlateOperatorData.action_apply
    (P : ProlateOperatorData) (f : ℝ → ℂ) (x : ℝ) :
    P.action f x = prolateWaveExpression P.lambda f x := by
  rw [P.action_eq]

@[simp] theorem ProlatePair.normalizingDenominator_eq
    (P : ProlatePair) :
    P.normalizingDenominator = Real.sqrt (P.I0 ^ 2 + P.I4 ^ 2) :=
  rfl

@[simp] theorem prolateCombination_apply
    (P : ProlatePair) (x : ℝ) :
    prolateCombination P x =
      ((P.I4 : ℂ) * P.h0 x - (P.I0 : ℂ) * P.h4 x) /
        (P.normalizingDenominator : ℂ) :=
  rfl

#print axioms prolateWaveExpression
#print axioms ProlateOperatorData
#print axioms ProlatePair
#print axioms ProlatePair.normalizingDenominator
#print axioms prolateCombination
#print axioms ProlateOperatorData.action_apply
#print axioms ProlatePair.normalizingDenominator_eq
#print axioms prolateCombination_apply

end Q3.RouteB.D0Pstar
