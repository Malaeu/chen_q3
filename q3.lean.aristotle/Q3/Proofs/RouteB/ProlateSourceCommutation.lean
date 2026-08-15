import Mathlib
import Q3.Proofs.RouteB.ProlateSourceRegularity

set_option linter.mathlibStandardSet false

open Complex Filter MeasureTheory Metric Set
open scoped ContDiff ENat Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- The first derivative of the finite-Fourier kernel in its first real
variable. -/
private theorem hasDerivAt_finiteFourierKernel_left (x y : ℝ) :
    HasDerivAt (fun z : ℝ => finiteFourierKernel z y)
      (finiteFourierKernel x y *
        (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ))) x := by
  have hlin :
      HasDerivAt
        (fun z : ℝ => Complex.I * ((2 * Real.pi * z * y : ℝ) : ℂ))
        (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)) x := by
    convert
      (ofRealCLM.hasDerivAt (x := x)).const_mul
        (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)) using 1
    · funext z
      simp only [ofRealCLM_apply]
      push_cast
      ring
    · simp only [ofRealCLM_apply, ofReal_one]
      push_cast
      ring
  exact hlin.cexp

/-- The first derivative of the finite-Fourier kernel in its second real
variable. -/
private theorem hasDerivAt_finiteFourierKernel_right (x y : ℝ) :
    HasDerivAt (fun z : ℝ => finiteFourierKernel x z)
      (finiteFourierKernel x y *
        (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ))) y := by
  have hlin :
      HasDerivAt
        (fun z : ℝ => Complex.I * ((2 * Real.pi * x * z : ℝ) : ℂ))
        (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) y := by
    convert
      (ofRealCLM.hasDerivAt (x := y)).const_mul
        (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) using 1
    · funext z
      simp only [ofRealCLM_apply]
      push_cast
      ring
    · simp only [ofRealCLM_apply, ofReal_one]
      push_cast
      ring
  exact hlin.cexp

private theorem hasDerivAt_prolateCoefficient (lambda x : ℝ) :
    HasDerivAt
      (fun y : ℝ => (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ)))
      (((-2 * x : ℝ) : ℂ)) x := by
  convert
    ((hasDerivAt_const x (lambda ^ 2)).sub (hasDerivAt_pow 2 x)).ofReal_comp using 1
  all_goals norm_num

private theorem finiteFourierKernel_comm (x y : ℝ) :
    finiteFourierKernel x y = finiteFourierKernel y x := by
  unfold finiteFourierKernel
  congr 2
  push_cast
  ring

@[simp]
private theorem norm_finiteFourierKernel (x y : ℝ) :
    ‖finiteFourierKernel x y‖ = 1 := by
  unfold finiteFourierKernel
  rw [Complex.norm_exp]
  simp

private theorem hasDerivAt_finiteFourierAction
    (lambda : ℝ) (φ : ℝ → ℂ) (hφ : Continuous φ) (x : ℝ) :
    HasDerivAt (finiteFourierAction lambda φ)
      (∫ y in Icc (-lambda) lambda,
        (finiteFourierKernel x y *
          (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ))) * φ y) x := by
  let μ : Measure ℝ := volume.restrict (Icc (-lambda) lambda)
  let F : ℝ → ℝ → ℂ := fun z y => finiteFourierKernel z y * φ y
  let F' : ℝ → ℝ → ℂ := fun z y =>
    (finiteFourierKernel z y *
      (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ))) * φ y
  let bound : ℝ → ℝ := fun y =>
    ‖Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)‖ * ‖φ y‖
  have hF_cont (z : ℝ) : Continuous (F z) := by
    dsimp only [F]
    unfold finiteFourierKernel
    fun_prop
  have hF'_cont (z : ℝ) : Continuous (F' z) := by
    dsimp only [F']
    unfold finiteFourierKernel
    fun_prop
  have hbound_cont : Continuous bound := by
    dsimp only [bound]
    fun_prop
  have hF_meas : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (F z) μ :=
    Filter.Eventually.of_forall fun z => (hF_cont z).aestronglyMeasurable
  have hF_int : Integrable (F x) μ := by
    simpa only [μ] using
      (hF_cont x).continuousOn.integrableOn_compact isCompact_Icc
  have hF'_meas : AEStronglyMeasurable (F' x) μ :=
    (hF'_cont x).aestronglyMeasurable
  have hbound_int : Integrable bound μ := by
    simpa only [μ] using
      hbound_cont.continuousOn.integrableOn_compact isCompact_Icc
  have hbound : ∀ᵐ y ∂μ, ∀ z ∈ ball x 1, ‖F' z y‖ ≤ bound y := by
    filter_upwards [] with y
    intro z _
    simp only [F', bound, norm_mul, norm_finiteFourierKernel, one_mul, le_refl]
  have hdiff : ∀ᵐ y ∂μ, ∀ z ∈ ball x 1,
      HasDerivAt (F · y) (F' z y) z := by
    filter_upwards [] with y
    intro z _
    simpa only [F, F'] using
      (hasDerivAt_finiteFourierKernel_left z y).mul_const (φ y)
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := F) (F' := F') (bound := bound)
      (x₀ := x) (ε := 1) one_pos hF_meas hF_int hF'_meas
      hbound hbound_int hdiff
  simpa only [finiteFourierAction, μ, F, F'] using hmain.2

private theorem prolateWaveExpression_finiteFourierKernel_left_formula
    (lambda x y : ℝ) :
    prolateWaveExpression lambda (fun z : ℝ => finiteFourierKernel z y) x =
      -(((-2 * x : ℝ) : ℂ) *
          (finiteFourierKernel x y *
            (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ))) +
        (((lambda ^ 2 - x ^ 2 : ℝ) : ℂ) *
          ((finiteFourierKernel x y *
              (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ))) *
            (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ))))) +
        (((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) *
          finiteFourierKernel x y := by
  let a : ℂ := Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)
  have hk := hasDerivAt_finiteFourierKernel_left x y
  have hka : HasDerivAt
      (fun z : ℝ => finiteFourierKernel z y * a)
      ((finiteFourierKernel x y * a) * a) x := hk.mul_const a
  have hp := hasDerivAt_prolateCoefficient lambda x
  have houter := hp.mul hka
  have houter' :
      HasDerivAt
        (fun z : ℝ => (((lambda ^ 2 - z ^ 2 : ℝ) : ℂ) *
          (finiteFourierKernel z y * a)))
        ((((-2 * x : ℝ) : ℂ) * (finiteFourierKernel x y * a)) +
          (((lambda ^ 2 - x ^ 2 : ℝ) : ℂ) *
            ((finiteFourierKernel x y * a) * a))) x := by
    simpa only [Pi.mul_apply] using houter
  have hkderiv (z : ℝ) :
      deriv (fun w : ℝ => finiteFourierKernel w y) z =
        finiteFourierKernel z y * a :=
    (hasDerivAt_finiteFourierKernel_left z y).deriv
  unfold prolateWaveExpression
  simp only [fderiv_deriv]
  simp_rw [hkderiv]
  change
    -deriv
        (fun z : ℝ => (((lambda ^ 2 - z ^ 2 : ℝ) : ℂ) *
          (finiteFourierKernel z y * a))) x +
        (((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) *
          finiteFourierKernel x y = _
  rw [houter'.deriv]

/-- The prolate differential expression acts symmetrically on the source
finite-Fourier kernel.  This is the algebraic heart of the intertwining
identity; the remaining analytic step is integration by parts. -/
theorem prolateWaveExpression_finiteFourierKernel_swap
    (lambda x y : ℝ) :
    prolateWaveExpression lambda (fun z : ℝ => finiteFourierKernel z y) x =
      prolateWaveExpression lambda (fun z : ℝ => finiteFourierKernel x z) y := by
  have hfun :
      (fun z : ℝ => finiteFourierKernel x z) =
        (fun z : ℝ => finiteFourierKernel z x) := by
    funext z
    exact finiteFourierKernel_comm x z
  rw [hfun, prolateWaveExpression_finiteFourierKernel_left_formula,
    prolateWaveExpression_finiteFourierKernel_left_formula,
    finiteFourierKernel_comm y x]
  push_cast
  ring_nf
  rw [I_sq]
  ring

private theorem prolateWaveExpression_finiteFourierAction_eq_kernel
    (lambda : ℝ) (φ : ℝ → ℂ) (hφ : Continuous φ) (x : ℝ) :
    prolateWaveExpression lambda (finiteFourierAction lambda φ) x =
      ∫ y in Icc (-lambda) lambda,
        prolateWaveExpression lambda
          (fun z : ℝ => finiteFourierKernel z y) x * φ y := by
  let a : ℝ → ℂ := fun y =>
    Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)
  let ψ : ℝ → ℂ := fun y => a y * φ y
  have hψ : Continuous ψ := by
    dsimp only [ψ, a]
    fun_prop
  have hderiv (z : ℝ) :
      deriv (finiteFourierAction lambda φ) z =
        finiteFourierAction lambda ψ z := by
    rw [(hasDerivAt_finiteFourierAction lambda φ hφ z).deriv]
    unfold finiteFourierAction
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [ψ, a]
    ring
  have hp := hasDerivAt_prolateCoefficient lambda x
  have hFψ := hasDerivAt_finiteFourierAction lambda ψ hψ x
  have houter := hp.mul hFψ
  have houter' :
      HasDerivAt
        (fun z : ℝ => (((lambda ^ 2 - z ^ 2 : ℝ) : ℂ) *
          finiteFourierAction lambda ψ z))
        ((((-2 * x : ℝ) : ℂ) * finiteFourierAction lambda ψ x) +
          (((lambda ^ 2 - x ^ 2 : ℝ) : ℂ) *
            (∫ y in Icc (-lambda) lambda,
              (finiteFourierKernel x y * a y) * ψ y))) x := by
    simpa only [Pi.mul_apply, a] using houter
  unfold prolateWaveExpression
  simp only [fderiv_deriv]
  simp_rw [hderiv]
  rw [houter'.deriv]
  let c1 : ℂ := ((-2 * x : ℝ) : ℂ)
  let c2 : ℂ := ((lambda ^ 2 - x ^ 2 : ℝ) : ℂ)
  let c3 : ℂ := (((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ)
  let f1 : ℝ → ℂ := fun y => (finiteFourierKernel x y * a y) * φ y
  let f2 : ℝ → ℂ := fun y => ((finiteFourierKernel x y * a y) * a y) * φ y
  let f3 : ℝ → ℂ := fun y => finiteFourierKernel x y * φ y
  have hf1 : IntegrableOn f1 (Icc (-lambda) lambda) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    dsimp only [f1, a]
    unfold finiteFourierKernel
    fun_prop
  have hf2 : IntegrableOn f2 (Icc (-lambda) lambda) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    dsimp only [f2, a]
    unfold finiteFourierKernel
    fun_prop
  have hf3 : IntegrableOn f3 (Icc (-lambda) lambda) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    dsimp only [f3]
    unfold finiteFourierKernel
    fun_prop
  have hpoint (y : ℝ) :
      -(c1 * f1 y + c2 * f2 y) + c3 * f3 y =
        prolateWaveExpression lambda
          (fun z : ℝ => finiteFourierKernel z y) x * φ y := by
    rw [prolateWaveExpression_finiteFourierKernel_left_formula]
    dsimp only [c1, c2, c3, f1, f2, f3, ψ, a]
    ring
  have hψint :
      finiteFourierAction lambda ψ x =
        ∫ y in Icc (-lambda) lambda, f1 y := by
    unfold finiteFourierAction
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [ψ, f1]
    ring
  have hsecond :
      (∫ y in Icc (-lambda) lambda,
        (finiteFourierKernel x y * a y) * ψ y) =
        ∫ y in Icc (-lambda) lambda, f2 y := by
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [ψ, f2]
    ring
  have hφint :
      finiteFourierAction lambda φ x =
        ∫ y in Icc (-lambda) lambda, f3 y := by
    rfl
  rw [hψint, hsecond, hφint]
  change
    -(c1 * (∫ y in Icc (-lambda) lambda, f1 y) +
        c2 * (∫ y in Icc (-lambda) lambda, f2 y)) +
      c3 * (∫ y in Icc (-lambda) lambda, f3 y) = _
  calc
    -(c1 * (∫ y in Icc (-lambda) lambda, f1 y) +
        c2 * (∫ y in Icc (-lambda) lambda, f2 y)) +
        c3 * (∫ y in Icc (-lambda) lambda, f3 y) =
        ∫ y in Icc (-lambda) lambda,
          (-(c1 * f1 y + c2 * f2 y) + c3 * f3 y) := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add (hf1.const_mul c1) (hf2.const_mul c2),
        ← integral_neg, ← integral_const_mul]
      change
        (∫ y in Icc (-lambda) lambda,
            (fun y => -(c1 * f1 y + c2 * f2 y)) y) +
          (∫ y in Icc (-lambda) lambda,
            (fun y => c3 * f3 y) y) =
          ∫ y in Icc (-lambda) lambda,
            ((fun y => -(c1 * f1 y + c2 * f2 y)) +
              (fun y => c3 * f3 y)) y
      exact
        (integral_add ((hf1.const_mul c1).add (hf2.const_mul c2)).neg
          (hf3.const_mul c3)).symm
    _ = ∫ y in Icc (-lambda) lambda,
        prolateWaveExpression lambda
          (fun z : ℝ => finiteFourierKernel z y) x * φ y := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact hpoint y

private theorem interval_prolate_differential_green_identity
    (lambda x : ℝ) (φ : ℝ → ℂ) (hφ : ContDiff ℝ 2 φ) :
    (∫ y in (-lambda)..lambda,
        (-deriv
          (fun z : ℝ => (((lambda ^ 2 - z ^ 2 : ℝ) : ℂ) *
            deriv (fun w : ℝ => finiteFourierKernel x w) z)) y) * φ y) =
      ∫ y in (-lambda)..lambda,
        finiteFourierKernel x y *
          (-deriv
            (fun z : ℝ => (((lambda ^ 2 - z ^ 2 : ℝ) : ℂ) *
              deriv φ z)) y) := by
  let p : ℝ → ℂ := fun y => (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ))
  let k : ℝ → ℂ := fun y => finiteFourierKernel x y
  let uk : ℝ → ℂ := fun y => p y * deriv k y
  let uφ : ℝ → ℂ := fun y => p y * deriv φ y
  have hp : ContDiff ℝ ∞ p := by
    dsimp only [p]
    exact ofRealCLM.contDiff.comp
      (contDiff_const.sub (contDiff_id.pow 2))
  have hk : ContDiff ℝ ∞ k := by
    dsimp only [k]
    unfold finiteFourierKernel
    apply ContDiff.cexp
    apply ContDiff.mul contDiff_const
    exact ofRealCLM.contDiff.comp
      (contDiff_const.mul contDiff_id)
  have hdk : ContDiff ℝ ∞ (deriv k) :=
    (contDiff_infty_iff_deriv.mp hk).2
  have hdφ : ContDiff ℝ 1 (deriv φ) := by
    exact hφ.deriv'
  have huk : ContDiff ℝ 1 uk := by
    exact (hp.mul hdk).of_le (by simp)
  have huφ : ContDiff ℝ 1 uφ := by
    exact (hp.of_le (by simp)).mul hdφ
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by simp)
  have hparts_k :=
    intervalIntegral.integral_deriv_mul_eq_sub
      (a := -lambda) (b := lambda)
      (u := uk) (u' := deriv uk) (v := φ) (v' := deriv φ)
      (fun y _ => (huk.differentiable_one y).hasDerivAt)
      (fun y _ => (hφ1.differentiable_one y).hasDerivAt)
      (huk.continuous_deriv_one.intervalIntegrable (-lambda) lambda)
      (hφ1.continuous_deriv_one.intervalIntegrable (-lambda) lambda)
  have hA_k : IntervalIntegrable (fun y => deriv uk y * φ y)
      volume (-lambda) lambda :=
    (huk.continuous_deriv_one.mul hφ.continuous).intervalIntegrable
      (-lambda) lambda
  have hB_k : IntervalIntegrable (fun y => uk y * deriv φ y)
      volume (-lambda) lambda :=
    (huk.continuous.mul hφ1.continuous_deriv_one).intervalIntegrable
      (-lambda) lambda
  rw [intervalIntegral.integral_add hA_k hB_k] at hparts_k
  have hparts_k_zero :
      (∫ y in (-lambda)..lambda, deriv uk y * φ y) +
        (∫ y in (-lambda)..lambda, uk y * deriv φ y) = 0 := by
    simpa [uk, p] using hparts_k
  have hk_step :
      (∫ y in (-lambda)..lambda, (-deriv uk y) * φ y) =
        ∫ y in (-lambda)..lambda, uk y * deriv φ y := by
    rw [show (fun y => (-deriv uk y) * φ y) =
        fun y => -(deriv uk y * φ y) by funext y; ring,
      intervalIntegral.integral_neg]
    linear_combination -hparts_k_zero
  have hparts_φ :=
    intervalIntegral.integral_deriv_mul_eq_sub
      (a := -lambda) (b := lambda)
      (u := k) (u' := deriv k) (v := uφ) (v' := deriv uφ)
      (fun y _ => (hk1.differentiable_one y).hasDerivAt)
      (fun y _ => (huφ.differentiable_one y).hasDerivAt)
      (hk1.continuous_deriv_one.intervalIntegrable (-lambda) lambda)
      (huφ.continuous_deriv_one.intervalIntegrable (-lambda) lambda)
  have hA_φ : IntervalIntegrable (fun y => deriv k y * uφ y)
      volume (-lambda) lambda :=
    (hk1.continuous_deriv_one.mul huφ.continuous).intervalIntegrable
      (-lambda) lambda
  have hB_φ : IntervalIntegrable (fun y => k y * deriv uφ y)
      volume (-lambda) lambda :=
    (hk.continuous.mul huφ.continuous_deriv_one).intervalIntegrable
      (-lambda) lambda
  rw [intervalIntegral.integral_add hA_φ hB_φ] at hparts_φ
  have hparts_φ_zero :
      (∫ y in (-lambda)..lambda, deriv k y * uφ y) +
        (∫ y in (-lambda)..lambda, k y * deriv uφ y) = 0 := by
    simpa [uφ, p] using hparts_φ
  have hφ_step :
      (∫ y in (-lambda)..lambda, k y * (-deriv uφ y)) =
        ∫ y in (-lambda)..lambda, deriv k y * uφ y := by
    rw [show (fun y => k y * (-deriv uφ y)) =
        fun y => -(k y * deriv uφ y) by funext y; ring,
      intervalIntegral.integral_neg]
    linear_combination -hparts_φ_zero
  change
    (∫ y in (-lambda)..lambda, (-deriv uk y) * φ y) =
      ∫ y in (-lambda)..lambda, k y * (-deriv uφ y)
  rw [hk_step, hφ_step]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only [uk, uφ]
  ring

private theorem interval_prolate_green_identity
    (lambda x : ℝ) (φ : ℝ → ℂ) (hφ : ContDiff ℝ 2 φ) :
    (∫ y in (-lambda)..lambda,
        prolateWaveExpression lambda
          (fun z : ℝ => finiteFourierKernel x z) y * φ y) =
      ∫ y in (-lambda)..lambda,
        finiteFourierKernel x y * prolateWaveExpression lambda φ y := by
  let p : ℝ → ℂ := fun y => (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ))
  let k : ℝ → ℂ := fun y => finiteFourierKernel x y
  let q : ℝ → ℂ := fun y => (((2 * Real.pi * lambda * y) ^ 2 : ℝ) : ℂ)
  let dk : ℝ → ℂ := fun y => -deriv (fun z => p z * deriv k z) y
  let dφ : ℝ → ℂ := fun y => -deriv (fun z => p z * deriv φ z) y
  have hp : ContDiff ℝ ∞ p := by
    dsimp only [p]
    exact ofRealCLM.contDiff.comp
      (contDiff_const.sub (contDiff_id.pow 2))
  have hk : ContDiff ℝ ∞ k := by
    dsimp only [k]
    unfold finiteFourierKernel
    apply ContDiff.cexp
    apply ContDiff.mul contDiff_const
    exact ofRealCLM.contDiff.comp
      (contDiff_const.mul contDiff_id)
  have hq : ContDiff ℝ ∞ q := by
    dsimp only [q]
    exact ofRealCLM.contDiff.comp
      ((contDiff_const.mul contDiff_id).pow 2)
  have hdk0 : ContDiff ℝ ∞ (deriv k) :=
    (contDiff_infty_iff_deriv.mp hk).2
  have huk : ContDiff ℝ 1 (fun y => p y * deriv k y) :=
    (hp.mul hdk0).of_le (by simp)
  have hdφ0 : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have huφ : ContDiff ℝ 1 (fun y => p y * deriv φ y) :=
    (hp.of_le (by simp)).mul hdφ0
  have hdk : Continuous dk := by
    exact huk.continuous_deriv_one.neg
  have hdφ : Continuous dφ := by
    exact huφ.continuous_deriv_one.neg
  have hk0 : Continuous k := hk.continuous
  have hq0 : Continuous q := hq.continuous
  have hleftD : IntervalIntegrable (fun y => dk y * φ y)
      volume (-lambda) lambda :=
    (hdk.mul hφ.continuous).intervalIntegrable (-lambda) lambda
  have hleftQ : IntervalIntegrable (fun y => q y * k y * φ y)
      volume (-lambda) lambda :=
    ((hq0.mul hk0).mul hφ.continuous).intervalIntegrable (-lambda) lambda
  have hrightD : IntervalIntegrable (fun y => k y * dφ y)
      volume (-lambda) lambda :=
    (hk0.mul hdφ).intervalIntegrable (-lambda) lambda
  have hrightQ : IntervalIntegrable (fun y => k y * (q y * φ y))
      volume (-lambda) lambda :=
    (hk0.mul (hq0.mul hφ.continuous)).intervalIntegrable (-lambda) lambda
  have hdiff :
      (∫ y in (-lambda)..lambda, dk y * φ y) =
        ∫ y in (-lambda)..lambda, k y * dφ y := by
    simpa only [dk, dφ, p, k] using
      interval_prolate_differential_green_identity lambda x φ hφ
  have hpotential :
      (∫ y in (-lambda)..lambda, q y * k y * φ y) =
        ∫ y in (-lambda)..lambda, k y * (q y * φ y) := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  calc
    (∫ y in (-lambda)..lambda,
        prolateWaveExpression lambda
          (fun z : ℝ => finiteFourierKernel x z) y * φ y) =
        ∫ y in (-lambda)..lambda,
          (dk y * φ y + q y * k y * φ y) := by
      apply intervalIntegral.integral_congr
      intro y _
      simp only [prolateWaveExpression, fderiv_deriv, dk, q, p, k]
      ring
    _ = (∫ y in (-lambda)..lambda, dk y * φ y) +
        ∫ y in (-lambda)..lambda, q y * k y * φ y := by
      exact intervalIntegral.integral_add hleftD hleftQ
    _ = (∫ y in (-lambda)..lambda, k y * dφ y) +
        ∫ y in (-lambda)..lambda, k y * (q y * φ y) := by
      rw [hdiff, hpotential]
    _ = ∫ y in (-lambda)..lambda,
        (k y * dφ y + k y * (q y * φ y)) := by
      exact (intervalIntegral.integral_add hrightD hrightQ).symm
    _ = ∫ y in (-lambda)..lambda,
        finiteFourierKernel x y * prolateWaveExpression lambda φ y := by
      apply intervalIntegral.integral_congr
      intro y _
      simp only [prolateWaveExpression, fderiv_deriv, dφ, q, p, k]
      ring

private theorem prolate_green_identity
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : ℝ) (φ : ℝ → ℂ) (hφ : ContDiff ℝ 2 φ) :
    (∫ y in Icc (-lambda) lambda,
        prolateWaveExpression lambda
          (fun z : ℝ => finiteFourierKernel x z) y * φ y) =
      ∫ y in Icc (-lambda) lambda,
        finiteFourierKernel x y * prolateWaveExpression lambda φ y := by
  have hle : -lambda ≤ lambda := by linarith
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle,
    ← intervalIntegral.integral_of_le hle]
  exact interval_prolate_green_identity lambda x φ hφ

/-- The exact finite-Fourier action commutes with the source-locked prolate
differential expression on globally `C²` test functions.  The proof uses the
kernel differential identity, differentiation under the compact integral, and
two integrations by parts; the factor `lambda^2-y^2` kills both endpoint
terms.  This is a conditional analytic intertwining theorem only: it does not
construct or select any PSWF mode. -/
theorem finiteFourierAction_intertwines_prolateWaveExpression
    (lambda : ℝ) (hlambda : 0 < lambda)
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ 2 φ) :
    ∀ x : ℝ,
      prolateWaveExpression lambda
          (finiteFourierAction lambda φ) x =
        finiteFourierAction lambda
          (prolateWaveExpression lambda φ) x := by
  intro x
  rw [prolateWaveExpression_finiteFourierAction_eq_kernel
    lambda φ hφ.continuous x]
  calc
    (∫ y in Icc (-lambda) lambda,
        prolateWaveExpression lambda
          (fun z : ℝ => finiteFourierKernel z y) x * φ y) =
        ∫ y in Icc (-lambda) lambda,
          prolateWaveExpression lambda
            (fun z : ℝ => finiteFourierKernel x z) y * φ y := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [prolateWaveExpression_finiteFourierKernel_swap]
    _ = ∫ y in Icc (-lambda) lambda,
        finiteFourierKernel x y * prolateWaveExpression lambda φ y :=
      prolate_green_identity lambda hlambda x φ hφ
    _ = finiteFourierAction lambda
        (prolateWaveExpression lambda φ) x := rfl

/-- The finite-Fourier action preserves a prolate eigenrelation on the natural
singular endpoint domain.  Unlike
`finiteFourierAction_intertwines_prolateWaveExpression`, this theorem does not
assume that the source is globally `C²`.  It asks only for continuity on the
closed source window, a first derivative in the interior, the divergence-form
ODE for the weighted derivative, and the two natural zero-flux limits.

The proof uses FTC on the products `p * k' * φ` and `k * p * φ'`, where
`p y = lambda^2 - y^2`.  A Tietze extension is used only to reuse the already
proved differentiation-under-the-integral identity; the extension disappears
from the public interface and from the final integral.  This theorem still
proves only preservation of the differential eigenspace.  It does not prove
that the Fourier image is a scalar multiple of the source mode. -/
theorem finiteFourierAction_preserves_prolateWaveEigenrelation_of_endpointFlux
    (lambda theta : ℝ) (hlambda : 0 < lambda)
    (φ dφ : ℝ → ℂ)
    (hφ : ContinuousOn φ (Icc (-lambda) lambda))
    (hφ' : ∀ y ∈ Ioo (-lambda) lambda, HasDerivAt φ (dφ y) y)
    (hflux' : ∀ y ∈ Ioo (-lambda) lambda,
      HasDerivAt
        (fun z : ℝ ↦ (((lambda ^ 2 - z ^ 2 : ℝ) : ℂ) * dφ z))
        (((((2 * Real.pi * lambda * y) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) *
          φ y) y)
    (hfluxPlus :
      Tendsto
        (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * dφ y))
        (nhdsWithin lambda (Iio lambda)) (nhds 0))
    (hfluxMinus :
      Tendsto
        (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * dφ y))
        (nhdsWithin (-lambda) (Ioi (-lambda))) (nhds 0)) :
    ∀ x : ℝ,
      prolateWaveExpression lambda (finiteFourierAction lambda φ) x =
        (theta : ℂ) * finiteFourierAction lambda φ x := by
  have hspan : -lambda < lambda := by linarith
  have hle : -lambda ≤ lambda := hspan.le
  let s : Set ℝ := Icc (-lambda) lambda
  let φs : C(s, ℂ) :=
    ⟨fun y ↦ φ y, continuousOn_iff_continuous_restrict.mp hφ⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq isClosed_Icc φs
  have hgφ : Set.EqOn (g : ℝ → ℂ) φ s := by
    intro y hy
    have h := DFunLike.congr_fun hg ⟨y, hy⟩
    exact h
  have haction :
      finiteFourierAction lambda (g : ℝ → ℂ) =
        finiteFourierAction lambda φ := by
    funext x
    unfold finiteFourierAction
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    rw [hgφ hy]
  intro x
  let p : ℝ → ℂ := fun y ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ))
  let k : ℝ → ℂ := fun y ↦ finiteFourierKernel x y
  let q : ℝ → ℂ :=
    fun y ↦ ((((2 * Real.pi * lambda * y) ^ 2 : ℝ) : ℂ))
  let uk : ℝ → ℂ := fun y ↦ p y * deriv k y
  let uφ : ℝ → ℂ := fun y ↦ p y * dφ y
  let fluxDeriv : ℝ → ℂ := fun y ↦ (q y - (theta : ℂ)) * φ y
  have hp : ContDiff ℝ ∞ p := by
    dsimp only [p]
    exact ofRealCLM.contDiff.comp
      (contDiff_const.sub (contDiff_id.pow 2))
  have hk : ContDiff ℝ ∞ k := by
    dsimp only [k]
    unfold finiteFourierKernel
    apply ContDiff.cexp
    apply ContDiff.mul contDiff_const
    exact ofRealCLM.contDiff.comp
      (contDiff_const.mul contDiff_id)
  have hq : ContDiff ℝ ∞ q := by
    dsimp only [q]
    exact ofRealCLM.contDiff.comp
      ((contDiff_const.mul contDiff_id).pow 2)
  have hdk : ContDiff ℝ ∞ (deriv k) :=
    (contDiff_infty_iff_deriv.mp hk).2
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by simp)
  have huk : ContDiff ℝ 1 uk :=
    (hp.mul hdk).of_le (by simp)
  have huφPlusValue : uφ lambda = 0 := by
    simp [uφ, p]
  have huφMinusValue : uφ (-lambda) = 0 := by
    simp [uφ, p]
  have huφPlus : ContinuousWithinAt uφ (Icc (-lambda) lambda) lambda := by
    rw [continuousWithinAt_Icc_iff_Iic hspan]
    rw [← continuousWithinAt_Iio_iff_Iic]
    change Tendsto uφ (nhdsWithin lambda (Iio lambda)) (nhds (uφ lambda))
    rw [huφPlusValue]
    exact hfluxPlus
  have huφMinus : ContinuousWithinAt uφ (Icc (-lambda) lambda) (-lambda) := by
    rw [continuousWithinAt_Icc_iff_Ici hspan]
    rw [← continuousWithinAt_Ioi_iff_Ici]
    change Tendsto uφ (nhdsWithin (-lambda) (Ioi (-lambda))) (nhds (uφ (-lambda)))
    rw [huφMinusValue]
    exact hfluxMinus
  have huφ : ContinuousOn uφ (Icc (-lambda) lambda) := by
    intro y hy
    by_cases hyMinus : y = -lambda
    · simpa [hyMinus] using huφMinus
    by_cases hyPlus : y = lambda
    · simpa [hyPlus] using huφPlus
    have hyOpen : y ∈ Ioo (-lambda) lambda :=
      ⟨lt_of_le_of_ne hy.1 (Ne.symm hyMinus), lt_of_le_of_ne hy.2 hyPlus⟩
    exact (hflux' y hyOpen).continuousAt.continuousWithinAt
  have hfluxDeriv : ∀ y ∈ Ioo (-lambda) lambda,
      HasDerivAt uφ (fluxDeriv y) y := by
    intro y hy
    simpa only [uφ, p, fluxDeriv, q] using hflux' y hy
  have hfluxDerivCont : ContinuousOn fluxDeriv (Icc (-lambda) lambda) := by
    dsimp only [fluxDeriv]
    exact (hq.continuous.continuousOn.sub continuousOn_const).mul hφ
  let firstProductDeriv : ℝ → ℂ := fun y ↦
    deriv uk y * φ y + deriv k y * uφ y
  have hfirstProductCont :
      ContinuousOn (fun y ↦ uk y * φ y) (Icc (-lambda) lambda) :=
    huk.continuous.continuousOn.mul hφ
  have hfirstProductDeriv : ∀ y ∈ Ioo (-lambda) lambda,
      HasDerivAt (fun z ↦ uk z * φ z) (firstProductDeriv y) y := by
    intro y hy
    have hprod := (huk.differentiable_one y).hasDerivAt.mul (hφ' y hy)
    convert hprod using 1
    dsimp only [firstProductDeriv, uk, uφ]
    ring
  have hfirstProductDerivCont :
      ContinuousOn firstProductDeriv (Icc (-lambda) lambda) := by
    dsimp only [firstProductDeriv]
    exact
      (huk.continuous_deriv_one.continuousOn.mul hφ).add
        (hdk.continuous.continuousOn.mul huφ)
  have hfirstFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hle hfirstProductCont hfirstProductDeriv
      (hfirstProductDerivCont.intervalIntegrable_of_Icc hle)
  have hukPlusValue : uk lambda = 0 := by
    simp [uk, p]
  have hukMinusValue : uk (-lambda) = 0 := by
    simp [uk, p]
  have hfirstFTCZero :
      (∫ y in (-lambda)..lambda, firstProductDeriv y) = 0 := by
    simpa only [hukPlusValue, hukMinusValue, zero_mul, sub_self] using hfirstFTC
  have hA1 : IntervalIntegrable (fun y ↦ deriv uk y * φ y)
      volume (-lambda) lambda :=
    (huk.continuous_deriv_one.continuousOn.mul hφ).intervalIntegrable_of_Icc hle
  have hB1 : IntervalIntegrable (fun y ↦ deriv k y * uφ y)
      volume (-lambda) lambda :=
    (hdk.continuous.continuousOn.mul huφ).intervalIntegrable_of_Icc hle
  have hfirstSplit :
      (∫ y in (-lambda)..lambda, deriv uk y * φ y) +
          (∫ y in (-lambda)..lambda, deriv k y * uφ y) = 0 := by
    rw [← intervalIntegral.integral_add hA1 hB1]
    exact hfirstFTCZero
  have hfirstStep :
      (∫ y in (-lambda)..lambda, (-deriv uk y) * φ y) =
        ∫ y in (-lambda)..lambda, deriv k y * uφ y := by
    rw [show (fun y ↦ (-deriv uk y) * φ y) =
        fun y ↦ -(deriv uk y * φ y) by funext y; ring,
      intervalIntegral.integral_neg]
    linear_combination -hfirstSplit
  let secondProductDeriv : ℝ → ℂ := fun y ↦
    deriv k y * uφ y + k y * fluxDeriv y
  have hsecondProductCont :
      ContinuousOn (fun y ↦ k y * uφ y) (Icc (-lambda) lambda) :=
    hk.continuous.continuousOn.mul huφ
  have hsecondProductDeriv : ∀ y ∈ Ioo (-lambda) lambda,
      HasDerivAt (fun z ↦ k z * uφ z) (secondProductDeriv y) y := by
    intro y hy
    have hprod := (hk1.differentiable_one y).hasDerivAt.mul (hfluxDeriv y hy)
    simpa only [secondProductDeriv] using hprod
  have hsecondProductDerivCont :
      ContinuousOn secondProductDeriv (Icc (-lambda) lambda) := by
    dsimp only [secondProductDeriv]
    exact
      (hdk.continuous.continuousOn.mul huφ).add
        (hk.continuous.continuousOn.mul hfluxDerivCont)
  have hsecondFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hle hsecondProductCont hsecondProductDeriv
      (hsecondProductDerivCont.intervalIntegrable_of_Icc hle)
  have hsecondFTCZero :
      (∫ y in (-lambda)..lambda, secondProductDeriv y) = 0 := by
    simpa only [huφPlusValue, huφMinusValue, mul_zero, sub_self] using hsecondFTC
  have hA2 : IntervalIntegrable (fun y ↦ deriv k y * uφ y)
      volume (-lambda) lambda := hB1
  have hB2 : IntervalIntegrable (fun y ↦ k y * fluxDeriv y)
      volume (-lambda) lambda :=
    (hk.continuous.continuousOn.mul hfluxDerivCont).intervalIntegrable_of_Icc hle
  have hsecondSplit :
      (∫ y in (-lambda)..lambda, deriv k y * uφ y) +
          (∫ y in (-lambda)..lambda, k y * fluxDeriv y) = 0 := by
    rw [← intervalIntegral.integral_add hA2 hB2]
    exact hsecondFTCZero
  have hsecondStep :
      (∫ y in (-lambda)..lambda, deriv k y * uφ y) =
        ∫ y in (-lambda)..lambda, k y * (-fluxDeriv y) := by
    rw [show (fun y ↦ k y * (-fluxDeriv y)) =
        fun y ↦ -(k y * fluxDeriv y) by funext y; ring,
      intervalIntegral.integral_neg]
    linear_combination hsecondSplit
  have hleftFormula :
      prolateWaveExpression lambda (finiteFourierAction lambda φ) x =
        ∫ y in Icc (-lambda) lambda,
          prolateWaveExpression lambda
            (fun z : ℝ ↦ finiteFourierKernel z y) x * φ y := by
    rw [← haction]
    calc
      prolateWaveExpression lambda
          (finiteFourierAction lambda (g : ℝ → ℂ)) x =
          ∫ y in Icc (-lambda) lambda,
            prolateWaveExpression lambda
              (fun z : ℝ ↦ finiteFourierKernel z y) x * g y :=
        prolateWaveExpression_finiteFourierAction_eq_kernel
          lambda (g : ℝ → ℂ) g.continuous x
      _ = ∫ y in Icc (-lambda) lambda,
            prolateWaveExpression lambda
              (fun z : ℝ ↦ finiteFourierKernel z y) x * φ y := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        rw [hgφ hy]
  rw [hleftFormula]
  have hgreenInterval :
      (∫ y in (-lambda)..lambda,
          prolateWaveExpression lambda (fun z : ℝ ↦ finiteFourierKernel x z) y * φ y) =
        (theta : ℂ) *
          ∫ y in (-lambda)..lambda, finiteFourierKernel x y * φ y := by
    have hQ : IntervalIntegrable (fun y ↦ q y * k y * φ y)
        volume (-lambda) lambda :=
      ContinuousOn.intervalIntegrable_of_Icc hle
        ((hq.continuous.continuousOn.mul hk.continuous.continuousOn).mul hφ)
    calc
      (∫ y in (-lambda)..lambda,
          prolateWaveExpression lambda (fun z : ℝ ↦ finiteFourierKernel x z) y * φ y) =
          ∫ y in (-lambda)..lambda,
            ((-deriv uk y) * φ y + q y * k y * φ y) := by
        apply intervalIntegral.integral_congr
        intro y _
        simp only [prolateWaveExpression, fderiv_deriv, uk, p, q, k]
        ring
      _ = (∫ y in (-lambda)..lambda, (-deriv uk y) * φ y) +
          ∫ y in (-lambda)..lambda, q y * k y * φ y := by
        exact intervalIntegral.integral_add
          (hA1.neg.congr (fun y _ ↦ by simp)) hQ
      _ = (∫ y in (-lambda)..lambda, deriv k y * uφ y) +
          ∫ y in (-lambda)..lambda, q y * k y * φ y := by
        rw [hfirstStep]
      _ = (∫ y in (-lambda)..lambda, k y * (-fluxDeriv y)) +
          ∫ y in (-lambda)..lambda, q y * k y * φ y := by
        rw [hsecondStep]
      _ = ∫ y in (-lambda)..lambda,
          (theta : ℂ) * (k y * φ y) := by
        rw [← intervalIntegral.integral_add
          (hB2.neg.congr (fun y _ ↦ by simp)) hQ]
        apply intervalIntegral.integral_congr
        intro y _
        dsimp only [fluxDeriv]
        ring
      _ = (theta : ℂ) *
          ∫ y in (-lambda)..lambda, finiteFourierKernel x y * φ y := by
        rw [intervalIntegral.integral_const_mul]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  calc
    (∫ y in (-lambda)..lambda,
        prolateWaveExpression lambda
          (fun z : ℝ ↦ finiteFourierKernel z y) x * φ y) =
        ∫ y in (-lambda)..lambda,
          prolateWaveExpression lambda
            (fun z : ℝ ↦ finiteFourierKernel x z) y * φ y := by
      apply intervalIntegral.integral_congr
      intro y _
      change
        prolateWaveExpression lambda
              (fun z : ℝ ↦ finiteFourierKernel z y) x * φ y =
          prolateWaveExpression lambda
              (fun z : ℝ ↦ finiteFourierKernel x z) y * φ y
      rw [prolateWaveExpression_finiteFourierKernel_swap]
    _ = (theta : ℂ) *
        ∫ y in (-lambda)..lambda, finiteFourierKernel x y * φ y :=
      hgreenInterval
    _ = (theta : ℂ) * finiteFourierAction lambda φ x := by
      unfold finiteFourierAction
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hle]

#print axioms prolateWaveExpression_finiteFourierKernel_swap
#print axioms finiteFourierAction_intertwines_prolateWaveExpression
#print axioms
  finiteFourierAction_preserves_prolateWaveEigenrelation_of_endpointFlux

end Q3.RouteB.D0Pstar
