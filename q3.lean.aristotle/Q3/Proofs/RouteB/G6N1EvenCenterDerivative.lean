import Q3.Proofs.RouteB.G6N1CenterAnchorScalarLock

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# W13.11 — the derivative of an even function at the centre

Checklist item W13.11 of the judge's REQ-2026-08-20-K verdict
(`docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_20_K_F72_0B2_CENTER_NORMALIZED_SATZ9_SOURCE_BIND_2026-08-20.md`),
marked `DERIVABLE; public wrapper open` and `LEAN_READY`.

The uniqueness receiver
`complex_prolate_divergence_solution_unique_of_center` needs the first
derivative at the centre, not only the value there. For even functions that
derivative is zero, and the argument is three lines. The verdict notes that the
existing helper `derivative_value_zero_of_even` is `private`, so either a public
wrapper is added or the three lines are repeated at every use — this file adds
the wrapper and applies it to the two selected modes.

This is not a new analytic hypothesis. It is a consequence of parity, which the
selected modes already carry as `ProlatePair` fields.

LEDGER:
  CLOSES: [W13_11_PROJECT_CENTER_DERIVATIVE_PUBLIC_WRAPPER]
  OPENS:  []
-/

/-- Public wrapper: an even function differentiable at the centre has zero
derivative there.  Proof by uniqueness of the derivative against the reflected
function. -/
theorem hasDerivAt_zero_of_even
    (f : ℝ → ℂ) (d : ℂ) (heven : Function.Even f)
    (hderiv : HasDerivAt f d 0) :
    d = 0 := by
  have hneg : HasDerivAt (fun x : ℝ ↦ f (-x)) (-d) 0 := by
    have hAtNegZero : HasDerivAt f d (-0) := by simpa using hderiv
    convert hAtNegZero.scomp 0 (hasDerivAt_neg 0) using 1
    all_goals norm_num
  have hfun : (fun x : ℝ ↦ f (-x)) = f := by
    funext x
    exact heven x
  rw [hfun] at hneg
  exact CharZero.neg_eq_self_iff.mp (hneg.unique hderiv)

/-- The mode-zero carrier of the selected pair has zero derivative at the
centre, whenever it is differentiable there. -/
theorem selectedFerrersPreAnchorPair_h0_deriv_zero
    (k : ℕ) (d : ℂ)
    (hderiv : HasDerivAt (selectedFerrersPreAnchorPair k).h0 d 0) :
    d = 0 :=
  hasDerivAt_zero_of_even _ d (selectedFerrersPreAnchorPair k).h0_even hderiv

/-- The mode-four carrier of the selected pair has zero derivative at the
centre, whenever it is differentiable there. -/
theorem selectedFerrersPreAnchorPair_h4_deriv_zero
    (k : ℕ) (d : ℂ)
    (hderiv : HasDerivAt (selectedFerrersPreAnchorPair k).h4 d 0) :
    d = 0 :=
  hasDerivAt_zero_of_even _ d (selectedFerrersPreAnchorPair k).h4_even hderiv

/-- The same statement for any even source candidate, which is the form the
generic receiver consumes: it does not mention the project modes at all, so a
paper representative can be fed to it without any identification. -/
theorem hasDerivAt_zero_of_even_source
    (p : ℝ → ℂ) (dp : ℂ) (hpEven : Function.Even p)
    (hpDeriv : HasDerivAt p dp 0) :
    dp = 0 :=
  hasDerivAt_zero_of_even p dp hpEven hpDeriv

/-- Centre data in exactly the shape the uniqueness receiver takes: two even
functions differentiable at the centre with equal centre values already agree
in both arguments the receiver needs. -/
theorem center_data_of_even
    (f p : ℝ → ℂ) (df dp : ℂ)
    (hfEven : Function.Even f) (hpEven : Function.Even p)
    (hfDeriv : HasDerivAt f df 0) (hpDeriv : HasDerivAt p dp 0)
    (hcenter : f 0 = p 0) :
    f 0 = p 0 ∧ df = dp := by
  refine ⟨hcenter, ?_⟩
  rw [hasDerivAt_zero_of_even f df hfEven hfDeriv,
    hasDerivAt_zero_of_even p dp hpEven hpDeriv]

#print axioms hasDerivAt_zero_of_even
#print axioms selectedFerrersPreAnchorPair_h0_deriv_zero
#print axioms selectedFerrersPreAnchorPair_h4_deriv_zero
#print axioms hasDerivAt_zero_of_even_source
#print axioms center_data_of_even

end Q3.RouteB.D0Pstar
