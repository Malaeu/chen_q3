import Q3.Proofs.RouteB.SpheroidalSourceMain
import Q3.Proofs.RouteB.G6N1Satz9SourcePackageInterface

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set Complex

namespace Q3.RouteB

/-!
# The dimensionless-to-physical source lift

Floor `W13_8_9_DIMENSIONLESS_TO_PHYSICAL_SOURCE_LIFT` of verdict `5cb885c2`
(`REGULAR_EVEN_SPHEROIDAL_TO_SATZ9_SOURCE_DATA_PHYSICAL_LIFT`).

Every step is source-only: the eigenfunction comes from
`spheroidal_normalized_witness` alone, never from a project mode, the
finite-limit carrier, or any V3.2 theorem.  The physical rescaling
`x ↦ x / lambda` and the exact separation shift `theta = Lambda + gamma^2`
are the entire content; no new spectral or asymptotic fact is used.

The load-bearing algebraic identity, checked once and for all here, is
`gamma^2 * (x/lambda)^2 = (2*pi*lambda*x)^2` together with
`gamma^2 = (2*pi*lambda^2)^2`.  Replacing `theta` by `Lambda` (dropping the
`+ gamma^2` shift) is the planted wrong-unit failure this file must not
produce.

LEDGER:
  CLOSES: [W13_8_9_DIMENSIONLESS_TO_PHYSICAL_SOURCE_LIFT,
           SATZ9_SOURCE_DATA_PHYSICAL_REALIZATION]
  OPENS:  []
-/

/-- **The physical lift.**  A regular even spheroidal eigenvalue in
dimensionless coordinates at parameter `gamma^2 = (2*pi*lambda^2)^2` produces
a `Satz9SourceData` package on the physical window `(-lambda, lambda)` at the
shifted separation value `Lambda + gamma^2`. -/
theorem regularEvenSpheroidalEigenvalue_physicalSatz9SourceData
    {lambda Lambda : ℝ}
    (hlambda : 0 < lambda)
    (h : RegularEvenSpheroidalEigenvalue
      ((2 * Real.pi * lambda ^ 2) ^ 2) Lambda) :
    Nonempty
      (D0Pstar.Satz9SourceData lambda
        (Lambda + (2 * Real.pi * lambda ^ 2) ^ 2)) := by
  obtain ⟨f, f1, f2, hf0, hf1_0, hev, hfc, hfd, hode, hlim1, hlim2⟩ :=
    spheroidal_normalized_witness h
  set G : ℝ := (2 * Real.pi * lambda ^ 2) ^ 2 with hGdef
  set theta : ℝ := Lambda + G with hthetadef
  have hlambda_ne : lambda ≠ 0 := ne_of_gt hlambda
  have hmemOfMem : ∀ x : ℝ, x ∈ Ioo (-lambda) lambda → x / lambda ∈ Ioo (-1 : ℝ) 1 := by
    intro x hx
    constructor
    · rw [lt_div_iff₀ hlambda]
      nlinarith [hx.1]
    · rw [div_lt_iff₀ hlambda]
      nlinarith [hx.2]
  set p : ℝ → ℂ := fun x => ((f (x / lambda) : ℝ) : ℂ) with hpdef
  set dp : ℝ → ℂ := fun x => ((f1 (x / lambda) / lambda : ℝ) : ℂ) with hdpdef
  have hp0 : p 0 = 1 := by
    have : (0 : ℝ) / lambda = 0 := zero_div lambda
    rw [hpdef]; simp only []; rw [this, hf0]; norm_num
  refine ⟨{
      p := p
      dp := dp
      hasDeriv := ?_
      flux := ?_
      even := ?_
      center_ne := ?_
      normalized_continuousOn := ?_ }⟩
  · intro x hx
    have hz : x / lambda ∈ Ioo (-1 : ℝ) 1 := hmemOfMem x hx
    have hlin : HasDerivAt (fun t : ℝ => t / lambda) (1 / lambda) x := by
      simpa using (hasDerivAt_id x).div_const lambda
    have hq : HasDerivAt (fun t : ℝ => f (t / lambda)) (f1 (x / lambda) * (1 / lambda)) x :=
      (hfd (x / lambda) hz).1.comp x hlin
    have hg : HasDerivAt (⇑ofRealCLM) (ofRealCLM 1) (f (x / lambda)) := ofRealCLM.hasDerivAt
    have hlift0 := HasDerivAt.scomp x hg hq
    have heq1 : (⇑ofRealCLM ∘ fun t : ℝ => f (t / lambda))
        = fun t : ℝ => ((f (t / lambda) : ℝ) : ℂ) := by
      funext t; simp [ofRealCLM_apply]
    have heq2 : (f1 (x / lambda) * (1 / lambda) : ℝ) • ofRealCLM (1 : ℝ)
        = ((f1 (x / lambda) / lambda : ℝ) : ℂ) := by
      simp only [ofRealCLM_apply, Complex.real_smul]
      push_cast
      ring
    rw [heq1, heq2] at hlift0
    exact hlift0
  · intro x hx
    have hz : x / lambda ∈ Ioo (-1 : ℝ) 1 := hmemOfMem x hx
    have hodez := hode (x / lambda) hz
    have hf1deriv : HasDerivAt (fun y : ℝ => f1 (y / lambda))
        (f2 (x / lambda) * (1 / lambda)) x := by
      have hlin : HasDerivAt (fun t : ℝ => t / lambda) (1 / lambda) x := by
        simpa using (hasDerivAt_id x).div_const lambda
      exact (hfd (x / lambda) hz).2.comp x hlin
    have hpoly : HasDerivAt (fun y : ℝ => lambda ^ 2 - y ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_sub (lambda ^ 2)
    have hprod : HasDerivAt (fun y : ℝ => (lambda ^ 2 - y ^ 2) * f1 (y / lambda))
        (-(2 * x) * f1 (x / lambda) +
          (lambda ^ 2 - x ^ 2) * (f2 (x / lambda) * (1 / lambda))) x :=
      hpoly.mul hf1deriv
    have hW : HasDerivAt
        (fun y : ℝ => (lambda ^ 2 - y ^ 2) * f1 (y / lambda) / lambda)
        ((-(2 * x) * f1 (x / lambda) +
            (lambda ^ 2 - x ^ 2) * (f2 (x / lambda) * (1 / lambda))) / lambda) x :=
      hprod.div_const lambda
    set Wderiv : ℝ :=
      (-(2 * x) * f1 (x / lambda) +
          (lambda ^ 2 - x ^ 2) * (f2 (x / lambda) * (1 / lambda))) / lambda
      with hWderivdef
    have hS : Wderiv
        = -(2 * (x / lambda)) * f1 (x / lambda) + (1 - (x / lambda) ^ 2) * f2 (x / lambda) := by
      rw [hWderivdef]
      field_simp
    have hSode : -(2 * (x / lambda)) * f1 (x / lambda) + (1 - (x / lambda) ^ 2) * f2 (x / lambda)
        = G * (x / lambda) ^ 2 * f (x / lambda) - theta * f (x / lambda) := by
      linear_combination -hodez
    have hGz2 : G * (x / lambda) ^ 2 = (2 * Real.pi * lambda * x) ^ 2 := by
      rw [hGdef]
      have hlam2 : lambda ^ 2 ≠ 0 := pow_ne_zero 2 hlambda_ne
      field_simp
    have hWderiv_eq :
        Wderiv = ((2 * Real.pi * lambda * x) ^ 2 - theta) * f (x / lambda) := by
      rw [hS, hSode, hGz2]
      ring
    have hgW : HasDerivAt (⇑ofRealCLM) (ofRealCLM 1)
        ((lambda ^ 2 - x ^ 2) * f1 (x / lambda) / lambda) := ofRealCLM.hasDerivAt
    have hlift0 := HasDerivAt.scomp x hgW hW
    have heqW1 : (⇑ofRealCLM ∘ fun y : ℝ => (lambda ^ 2 - y ^ 2) * f1 (y / lambda) / lambda)
        = fun y : ℝ => ((((lambda ^ 2 - y ^ 2) * f1 (y / lambda) / lambda : ℝ)) : ℂ) := by
      funext y; simp [ofRealCLM_apply]
    have heqW2 : (Wderiv : ℝ) • ofRealCLM (1 : ℝ) = ((Wderiv : ℝ) : ℂ) := by
      simp only [ofRealCLM_apply, Complex.real_smul, Complex.ofReal_one, mul_one]
    rw [heqW1, heqW2] at hlift0
    have hlift := hlift0
    have hfun_eq : (fun y : ℝ => (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ)) * dp y)
        = fun y : ℝ => ((((lambda ^ 2 - y ^ 2) * f1 (y / lambda) / lambda : ℝ)) : ℂ) := by
      funext y
      rw [hdpdef]
      simp only []
      rw [← Complex.ofReal_mul]
      congr 1
      ring
    rw [hfun_eq]
    have htarget_eq :
        ((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) * p x
          = ((Wderiv : ℝ) : ℂ) := by
      rw [hWderiv_eq, hpdef]
      simp only []
      push_cast
      ring
    rw [htarget_eq]
    exact hlift
  · intro x
    show p (-x) = p x
    rw [hpdef]
    simp only []
    rw [neg_div, hev (x / lambda)]
  · rw [hp0]; exact one_ne_zero
  · have hcont : ContinuousOn p (Icc (-lambda) lambda) := by
      have hmapsto : MapsTo (fun x : ℝ => x / lambda) (Icc (-lambda) lambda) (Icc (-1 : ℝ) 1) := by
        intro x hx
        constructor
        · rw [le_div_iff₀ hlambda]; nlinarith [hx.1]
        · rw [div_le_iff₀ hlambda]; nlinarith [hx.2]
      have hcontDiv : ContinuousOn (fun x : ℝ => x / lambda) (Icc (-lambda) lambda) :=
        (continuous_id.div_const lambda).continuousOn
      have hcompose : ContinuousOn (fun x : ℝ => f (x / lambda)) (Icc (-lambda) lambda) :=
        hfc.comp hcontDiv hmapsto
      exact continuous_ofReal.comp_continuousOn hcompose
    have heq : D0Pstar.centerNormalized p = p := by
      funext x
      rw [D0Pstar.centerNormalized, hp0, div_one]
    rw [heq]
    exact hcont

#print axioms regularEvenSpheroidalEigenvalue_physicalSatz9SourceData

end Q3.RouteB
