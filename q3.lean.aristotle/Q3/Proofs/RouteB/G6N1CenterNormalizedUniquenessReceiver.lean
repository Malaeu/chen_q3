import Q3.Proofs.RouteB.G6N1EvenCenterDerivative
import Q3.Proofs.RouteB.D0Mode4FerrersPhysicalFourierScalarProportionality

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# F72.0B2C — the center-normalized uniqueness receiver

Floors F72.0B2C (`center-normalized wrappers`) and the `generic_receiver` /
`endpoint_extension` pair of F72.0B2, all marked `LEAN_READY` in the judge's
REQ-2026-08-20-K verdict
(`docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_20_K_F72_0B2_CENTER_NORMALIZED_SATZ9_SOURCE_BIND_2026-08-20.md`).

The architecture the verdict selected is a private source witness feeding a
generic kernel receiver. This file is that receiver, and its defining property
is what it does **not** mention: no selected Ferrers mode, no `ps`, no paper
object, no spheroidal anything. It takes two functions that happen to solve the
same divergence-form prolate equation, are even, and do not vanish at the
centre, and concludes that their center-normalized views coincide.

Consequently nothing here can be a surrogate identification. A paper
representative is fed in as an argument; it is never defined to be ours.

The whole content is that scalar division preserves a homogeneous linear
equation, plus the observation from `G6N1EvenCenterDerivative.lean` that parity
kills the derivative at the centre, which is the second datum the existing
uniqueness theorem requires.

LEDGER:
  CLOSES: [F72_0B2C_CENTER_NORMALIZED_WRAPPERS,
           F72_0B2_GENERIC_RECEIVER,
           F72_0B2_ENDPOINT_EXTENSION]
  OPENS:  []
-/

/-- The center-normalized view of a function. -/
noncomputable def centerNormalized (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  f x / f 0

@[simp] theorem centerNormalized_at_zero (f : ℝ → ℂ) (h : f 0 ≠ 0) :
    centerNormalized f 0 = 1 := by
  rw [centerNormalized, div_self h]

/-- Scalar division preserves parity. -/
theorem centerNormalized_even {f : ℝ → ℂ} (hf : Function.Even f) :
    Function.Even (centerNormalized f) := by
  intro x
  rw [centerNormalized, centerNormalized, hf x]

/-- Scalar division preserves differentiability, dividing the derivative. -/
theorem hasDerivAt_centerNormalized {f : ℝ → ℂ} {d : ℂ} {x : ℝ}
    (hf : HasDerivAt f d x) :
    HasDerivAt (centerNormalized f) (d / f 0) x := by
  simpa only [centerNormalized] using hf.div_const (f 0)

/-- Scalar division preserves the divergence-form prolate equation.  This is
the only step where the equation is used, and it works because the equation is
homogeneous and linear. -/
theorem flux_centerNormalized {f df : ℝ → ℂ} {lambda theta x : ℝ}
    (hflux : HasDerivAt
      (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * df y))
      (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) * f x) x) :
    HasDerivAt
      (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * (df y / f 0)))
      (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) *
        centerNormalized f x) x := by
  have h := hflux.div_const (f 0)
  have hfun : (fun y : ℝ ↦
      (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * df y) / f 0) =
      fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * (df y / f 0)) := by
    funext y
    rw [mul_div_assoc]
  rw [hfun] at h
  simpa only [centerNormalized, mul_div_assoc] using h

/-- **The receiver.**  Two even solutions of the same divergence-form prolate
equation on the open window, neither vanishing at the centre, have equal
center-normalized views on that window.

Nothing in the statement refers to the project's modes or to any paper object:
both `f` and `g` are arguments. -/
theorem centerNormalized_eqOn_of_sameProlateODE
    (lambda theta : ℝ) (hlambda : 0 < lambda)
    (f df g dg : ℝ → ℂ)
    (hf : ∀ x ∈ Ioo (-lambda) lambda, HasDerivAt f (df x) x)
    (hg : ∀ x ∈ Ioo (-lambda) lambda, HasDerivAt g (dg x) x)
    (hfluxf : ∀ x ∈ Ioo (-lambda) lambda,
      HasDerivAt
        (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * df y))
        (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) * f x) x)
    (hfluxg : ∀ x ∈ Ioo (-lambda) lambda,
      HasDerivAt
        (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * dg y))
        (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) * g x) x)
    (hfEven : Function.Even f) (hgEven : Function.Even g)
    (hf0 : f 0 ≠ 0) (hg0 : g 0 ≠ 0) :
    EqOn (centerNormalized f) (centerNormalized g) (Ioo (-lambda) lambda) := by
  have hzeroMem : (0 : ℝ) ∈ Ioo (-lambda) lambda := by
    constructor <;> linarith
  -- the two centre data the uniqueness theorem needs
  have hcenter : centerNormalized f 0 = centerNormalized g 0 := by
    rw [centerNormalized_at_zero f hf0, centerNormalized_at_zero g hg0]
  have hdf0 : df 0 = 0 :=
    hasDerivAt_zero_of_even f (df 0) hfEven (hf 0 hzeroMem)
  have hdg0 : dg 0 = 0 :=
    hasDerivAt_zero_of_even g (dg 0) hgEven (hg 0 hzeroMem)
  have hderivCenter : df 0 / f 0 = dg 0 / g 0 := by
    rw [hdf0, hdg0, zero_div, zero_div]
  exact complex_prolate_divergence_solution_unique_of_center
    lambda theta hlambda
    (centerNormalized f) (fun x => df x / f 0)
    (centerNormalized g) (fun x => dg x / g 0)
    (fun x hx => hasDerivAt_centerNormalized (hf x hx))
    (fun x hx => hasDerivAt_centerNormalized (hg x hx))
    (fun x hx => flux_centerNormalized (hfluxf x hx))
    (fun x hx => flux_centerNormalized (hfluxg x hx))
    hcenter hderivCenter

/-- **Endpoint extension.**  Continuity ON THE CLOSED WINDOW carries the
equality from the open window to its endpoints.

⚠️ **CORRECTED 2026-08-21 after the Codex audit** (`CODEX_AUDIT_2026-08-21.md`,
finding `F72_0B2_GLOBAL_NORMALIZED_CONTINUITY_CONTRACT_GAP`). The first version
demanded global `Continuous`, while REQ-K specified `ContinuousOn` on the closed
window and the shelf supplies only that
(`physicalComplex_continuousOn_closed`).

The audit's point is sharper than a mismatch of strength, and this body
confirmed it from the source: the production `normalizedPhysicalMode` is an
`Icc.indicator` zero extension, and the mode does not vanish at the window
endpoints. So global continuity is not merely a stronger hypothesis, it is
**false for our own modes**, and the previous theorem — though correctly
proved — was vacuous exactly where it was meant to be used. The kernel could
not see this: the implication held, only its antecedent was unreachable. -/
theorem centerNormalized_eqOn_closed_of_continuousOn
    (lambda : ℝ) (hlambda : 0 < lambda) (f g : ℝ → ℂ)
    (hopen : EqOn (centerNormalized f) (centerNormalized g)
      (Ioo (-lambda) lambda))
    (hfc : ContinuousOn (centerNormalized f) (Icc (-lambda) lambda))
    (hgc : ContinuousOn (centerNormalized g) (Icc (-lambda) lambda)) :
    EqOn (centerNormalized f) (centerNormalized g) (Icc (-lambda) lambda) := by
  have hne : (-lambda : ℝ) ≠ lambda := by
    intro h; linarith
  have hclosure : closure (Ioo (-lambda) lambda) = Icc (-lambda) lambda :=
    closure_Ioo hne
  exact hopen.of_subset_closure hfc hgc Ioo_subset_Icc_self
    (by rw [hclosure])

#print axioms centerNormalized
#print axioms centerNormalized_even
#print axioms hasDerivAt_centerNormalized
#print axioms flux_centerNormalized
#print axioms centerNormalized_eqOn_of_sameProlateODE
#print axioms centerNormalized_eqOn_closed_of_continuousOn

end Q3.RouteB.D0Pstar
