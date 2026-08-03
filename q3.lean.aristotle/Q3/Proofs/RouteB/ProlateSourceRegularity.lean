import Mathlib
import Q3.Proofs.RouteB.ProlateLayer

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- The source Fourier kernel with the repository convention
`exp (2 * pi * I * x * y)`.

Source lock:
`docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:19-23` and
`ACTIVE/requests/routeB_lamport_rh_closure/
D0_3F_PROLATE_SELFADJOINT_REALIZATION.md:137-151`. -/
def finiteFourierKernel (x y : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((2 * Real.pi * x * y : ℝ) : ℂ))

/-- The finite Fourier action on the source time window.  This is an analytic
definition only; it does not assert a PSWF eigenfunction or construct a mode.
The relevant source relations are `h0 <-> chi0` and `h4 <-> chi2`, never
`h4 <-> chi4`; see `docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:58-75`. -/
def finiteFourierAction (lambda : ℝ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in Icc (-lambda) lambda, finiteFourierKernel x y * h y

/-- At frequency zero the source finite-Fourier action is the interval mass. -/
@[simp]
theorem finiteFourierAction_zero (lambda : ℝ) (h : ℝ → ℂ) :
    finiteFourierAction lambda h 0 =
      ∫ y in Icc (-lambda) lambda, h y := by
  simp [finiteFourierAction, finiteFourierKernel]

/-- Symmetric support and the zero-frequency eigen-equation imply the existing
`ProlatePair` Fourier-center field; it need not be assumed independently in a
future source constructor. -/
theorem integral_eq_chi_mul_zero_of_finiteFourier_eigenrelation
    (lambda : ℝ) (h : ℝ → ℂ) (chi : ℂ)
    (hsupp : Function.support h ⊆ Icc (-lambda) lambda)
    (heigen_zero : finiteFourierAction lambda h 0 = chi * h 0) :
    (∫ y : ℝ, h y) = chi * h 0 := by
  have hzero : ∀ y, y ∉ Icc (-lambda) lambda → h y = 0 := by
    intro y hy
    by_contra hne
    exact hy (hsupp hne)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← finiteFourierAction_zero]
  exact heigen_zero

/-- Unit-circle exponentials are Lipschitz in their real phase. -/
private theorem norm_exp_I_mul_sub_exp_I_mul_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) -
        Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have hfactor :
      Complex.exp (Complex.I * (a : ℂ)) -
          Complex.exp (Complex.I * (b : ℂ)) =
        Complex.exp (Complex.I * (b : ℂ)) *
          (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [hfactor, norm_mul]
  simpa [Complex.norm_exp] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

/-- The finite Fourier kernel is globally Lipschitz in its first variable,
with the exact pointwise weight `2*pi*|y|`. -/
theorem norm_finiteFourierKernel_sub_le (x z y : ℝ) :
    ‖finiteFourierKernel x y - finiteFourierKernel z y‖ ≤
      (2 * Real.pi * |y|) * dist x z := by
  calc
    ‖finiteFourierKernel x y - finiteFourierKernel z y‖ ≤
        |(2 * Real.pi * x * y) - (2 * Real.pi * z * y)| := by
          exact norm_exp_I_mul_sub_exp_I_mul_le _ _
    _ = (2 * Real.pi * |y|) * dist x z := by
      rw [Real.dist_eq]
      have hpi : 0 ≤ (2 * Real.pi : ℝ) := by positivity
      rw [show (2 * Real.pi * x * y) - (2 * Real.pi * z * y) =
          (2 * Real.pi) * (x - z) * y by ring, abs_mul, abs_mul,
        abs_of_nonneg hpi]
      ring

/-- The finite Fourier action of an `L1` function on a nonnegative symmetric
window is globally Lipschitz.  This is the analytic regularity input needed
after a genuine source PSWF eigenmode has been constructed. -/
theorem finiteFourierAction_lipschitzWith
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (h : ℝ → ℂ)
    (hint : IntegrableOn h (Icc (-lambda) lambda)) :
    ∃ K : NNReal, LipschitzWith K (finiteFourierAction lambda h) := by
  let mass : ℝ := ∫ y in Icc (-lambda) lambda, ‖h y‖
  have hmass : 0 ≤ mass := by
    exact integral_nonneg fun _ => norm_nonneg _
  let K : NNReal :=
    ⟨(2 * Real.pi * lambda) * mass, mul_nonneg (by positivity) hmass⟩
  refine ⟨K, LipschitzWith.of_dist_le_mul fun x z => ?_⟩
  have hkernel_cont : ∀ w : ℝ,
      ContinuousOn (fun y : ℝ => finiteFourierKernel w y)
        (Icc (-lambda) lambda) := by
    intro w
    unfold finiteFourierKernel
    fun_prop
  have hxint : IntegrableOn
      (fun y : ℝ => finiteFourierKernel x y * h y)
      (Icc (-lambda) lambda) := by
    simpa only [mul_comm] using
      hint.mul_continuousOn (hkernel_cont x) isCompact_Icc
  have hzint : IntegrableOn
      (fun y : ℝ => finiteFourierKernel z y * h y)
      (Icc (-lambda) lambda) := by
    simpa only [mul_comm] using
      hint.mul_continuousOn (hkernel_cont z) isCompact_Icc
  rw [dist_eq_norm, finiteFourierAction, finiteFourierAction,
    ← integral_sub hxint hzint]
  calc
    ‖∫ y in Icc (-lambda) lambda,
          (finiteFourierKernel x y * h y -
            finiteFourierKernel z y * h y)‖ ≤
        ∫ y in Icc (-lambda) lambda,
          ((2 * Real.pi * lambda) * dist x z) * ‖h y‖ := by
      apply norm_integral_le_of_norm_le
      · exact hint.norm.const_mul _
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        calc
          ‖finiteFourierKernel x y * h y -
              finiteFourierKernel z y * h y‖ =
              ‖finiteFourierKernel x y - finiteFourierKernel z y‖ *
                ‖h y‖ := by
                  rw [← sub_mul, norm_mul]
          _ ≤ ((2 * Real.pi * |y|) * dist x z) * ‖h y‖ := by
                gcongr
                exact norm_finiteFourierKernel_sub_le x z y
          _ ≤ ((2 * Real.pi * lambda) * dist x z) * ‖h y‖ := by
                gcongr
                exact abs_le.mpr hy
    _ = (K : ℝ) * dist x z := by
      rw [integral_const_mul]
      simp only [K, NNReal.coe_mk, mass]
      ring

/-- A nonzero finite-Fourier eigenvalue transfers the kernel regularity to the
exact eigenfunction on the positive source window.  Unlike the old receiver,
this theorem does not assume mode Lipschitz regularity: it derives it from the
source eigen-equation.  It still does not assert that such an eigenfunction
exists. -/
theorem positiveHalfLipschitz_of_finiteFourier_eigenrelation
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (h : ℝ → ℂ) (chi : ℂ)
    (hchi : chi ≠ 0)
    (hint : IntegrableOn h (Icc (-lambda) lambda))
    (heigen : ∀ x ∈ Ico (0 : ℝ) lambda,
      finiteFourierAction lambda h x = chi * h x) :
    ∃ K : NNReal, LipschitzOnWith K h (Ico (0 : ℝ) lambda) := by
  obtain ⟨K, hK⟩ := finiteFourierAction_lipschitzWith lambda hlambda h hint
  let Kh : NNReal := ‖chi⁻¹‖₊ * K
  refine ⟨Kh, LipschitzOnWith.of_dist_le_mul fun x hx z hz => ?_⟩
  have hxformula : h x = chi⁻¹ * finiteFourierAction lambda h x := by
    rw [heigen x hx]
    simp [hchi]
  have hzformula : h z = chi⁻¹ * finiteFourierAction lambda h z := by
    rw [heigen z hz]
    simp [hchi]
  calc
    dist (h x) (h z) =
        ‖chi⁻¹‖ * dist (finiteFourierAction lambda h x)
          (finiteFourierAction lambda h z) := by
      rw [hxformula, hzformula, dist_eq_norm, dist_eq_norm, ← mul_sub,
        norm_mul]
    _ ≤ ‖chi⁻¹‖ * ((K : ℝ) * dist x z) := by
      gcongr
      exact hK.dist_le_mul x z
    _ = (Kh : ℝ) * dist x z := by
      simp only [Kh, NNReal.coe_mul, coe_nnnorm]
      ring

#print axioms finiteFourierKernel
#print axioms finiteFourierAction
#print axioms finiteFourierAction_zero
#print axioms integral_eq_chi_mul_zero_of_finiteFourier_eigenrelation
#print axioms norm_finiteFourierKernel_sub_le
#print axioms finiteFourierAction_lipschitzWith
#print axioms positiveHalfLipschitz_of_finiteFourier_eigenrelation

end Q3.RouteB.D0Pstar
