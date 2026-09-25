import Mathlib

open Filter Set intervalIntegral
open scoped Topology

noncomputable section

namespace Q3.RouteB.JointGreen

/-- The Mellin test function v ↦ v^(s - 1), using the principal complex power
of the positive real variable. -/
def mellinTest (s : ℂ) (v : ℝ) : ℂ := (v : ℂ) ^ (s - 1)

/-- First derivative of the Mellin test function on the positive axis. -/
def mellinTestDeriv (s : ℂ) (v : ℝ) : ℂ :=
  (s - 1) * (v : ℂ) ^ (s - 2)

/-- Second derivative of the Mellin test function on the positive axis. -/
def mellinTestSecondDeriv (s : ℂ) (v : ℝ) : ℂ :=
  (s - 1) * (s - 2) * (v : ℂ) ^ (s - 3)

theorem mellinTest_hasDerivAt (s : ℂ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (mellinTest s) (mellinTestDeriv s v) v := by
  have h := HasDerivAt.cpow_const (c := s - 1) (hasDerivAt_id (v : ℂ))
    (Complex.ofReal_mem_slitPlane.2 hv)
  have hexp : s - 2 = (s - 1) - 1 := by ring
  convert h.comp_ofReal using 1
  simp [mellinTestDeriv, id_eq, hexp]

theorem mellinTestDeriv_hasDerivAt (s : ℂ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (mellinTestDeriv s) (mellinTestSecondDeriv s v) v := by
  have h := HasDerivAt.cpow_const (c := s - 2) (hasDerivAt_id (v : ℂ))
    (Complex.ofReal_mem_slitPlane.2 hv)
  have h' := h.comp_ofReal.const_mul (s - 1)
  have hexp : s - 3 = (s - 2) - 1 := by ring
  convert h' using 1
  simp [mellinTestSecondDeriv, id_eq, hexp]
  ring

/-- Weighted Wronskian. -/
def jointGreenWronskian (p u du phi dphi : ℝ → ℂ) (v : ℝ) : ℂ :=
  p v * (du v * phi v - u v * dphi v)

/-- The negative derivative of the weighted Wronskian, written without
suppressing either differentiated coefficient term. -/
def jointGreenIntegrand
    (p dp u du ddu phi dphi ddphi : ℝ → ℂ) (v : ℝ) : ℂ :=
  u v * (dp v * dphi v + p v * ddphi v) -
    phi v * (dp v * du v + p v * ddu v)

private theorem jointGreenWronskian_hasDerivAt
    (p dp u du ddu phi dphi ddphi : ℝ → ℂ) {v : ℝ}
    (hp : HasDerivAt p (dp v) v)
    (hu : HasDerivAt u (du v) v)
    (hdu : HasDerivAt du (ddu v) v)
    (hphi : HasDerivAt phi (dphi v) v)
    (hdphi : HasDerivAt dphi (ddphi v) v) :
    HasDerivAt (jointGreenWronskian p u du phi dphi)
      (-jointGreenIntegrand p dp u du ddu phi dphi ddphi v) v := by
  have hbracket : HasDerivAt
      (fun x : ℝ => du x * phi x - u x * dphi x)
      (ddu v * phi v + du v * dphi v - (du v * dphi v + u v * ddphi v)) v :=
    (hdu.mul hphi).sub (hu.mul hdphi)
  have h := hp.mul hbracket
  apply h.congr_deriv
  dsimp [jointGreenWronskian, jointGreenIntegrand]
  ring

/--
Exact Green integration identity on [t,1] for the complex Mellin test
phi(v) = v^(s-1). The endpoint at 1 is handled by an explicit zero limit
of the weighted Wronskian. The lower endpoint term is retained with its sign.

The hypotheses give pointwise derivatives of p, u, and u's first derivative
on (0,1), along with integrability of the Green integrand and zero upper
flux. The lower trace follows from interior differentiability at t.
-/
theorem mellin_joint_green_identity
    (s : ℂ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (p dp u du ddu : ℝ → ℂ)
    (hp : ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivAt p (dp v) v)
    (hu : ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivAt u (du v) v)
    (hdu : ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivAt du (ddu v) v)
    (hTop : Tendsto
      (jointGreenWronskian p u du (mellinTest s) (mellinTestDeriv s))
      (𝓝[<] (1 : ℝ)) (𝓝 0))
    (hInt : IntervalIntegrable
      (fun v : ℝ => jointGreenIntegrand p dp u du ddu
        (mellinTest s) (mellinTestDeriv s) (mellinTestSecondDeriv s) v)
      MeasureTheory.volume t 1) :
    (∫ v in t..1, jointGreenIntegrand p dp u du ddu
      (mellinTest s) (mellinTestDeriv s) (mellinTestSecondDeriv s) v) =
      p t * (du t * mellinTest s t - u t * mellinTestDeriv s t) := by
  let phi := mellinTest s
  let dphi := mellinTestDeriv s
  let ddphi := mellinTestSecondDeriv s
  have hphi : ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivAt phi (dphi v) v := by
    intro v hv
    exact mellinTest_hasDerivAt s hv.1
  have hdphi : ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivAt dphi (ddphi v) v := by
    intro v hv
    exact mellinTestDeriv_hasDerivAt s hv.1
  have hW : ∀ v ∈ Ioo (t : ℝ) 1,
      HasDerivAt (jointGreenWronskian p u du phi dphi)
        (-jointGreenIntegrand p dp u du ddu phi dphi ddphi v) v := by
    intro v hv
    have hv01 : v ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans ht0 hv.1, hv.2⟩
    exact jointGreenWronskian_hasDerivAt p dp u du ddu phi dphi ddphi
      (hp v hv01) (hu v hv01) (hdu v hv01) (hphi v hv01) (hdphi v hv01)
  have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have hWt := jointGreenWronskian_hasDerivAt p dp u du ddu phi dphi ddphi
    (hp t ht01) (hu t ht01) (hdu t ht01) (hphi t ht01) (hdphi t ht01)
  have hLower : Tendsto (jointGreenWronskian p u du phi dphi)
      (𝓝[>] t) (𝓝 (jointGreenWronskian p u du phi dphi t)) :=
    hWt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hInt' : IntervalIntegrable
      (fun v : ℝ => jointGreenIntegrand p dp u du ddu phi dphi ddphi v)
      MeasureTheory.volume t 1 := by
    simpa [phi, dphi, ddphi] using hInt
  have hIntNeg : IntervalIntegrable
      (fun v : ℝ => -jointGreenIntegrand p dp u du ddu phi dphi ddphi v)
      MeasureTheory.volume t 1 := by
    simpa only [Pi.neg_apply] using hInt'.neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := jointGreenWronskian p u du phi dphi)
    (f' := fun x : ℝ => -jointGreenIntegrand p dp u du ddu phi dphi ddphi x)
    (a := t) (b := (1 : ℝ)) ht1 hW hIntNeg hLower hTop
  simpa [phi, dphi, ddphi, jointGreenWronskian] using hFTC

#print axioms mellinTest_hasDerivAt
#print axioms mellinTestDeriv_hasDerivAt
#print axioms mellin_joint_green_identity

end Q3.RouteB.JointGreen
