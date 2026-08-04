import Q3.Proofs.RouteB.D0PostAnchorMontel
import Q3.Proofs.RouteB.D0CenteredCriticalMoment

set_option linter.mathlibStandardSet false

open Complex Filter MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

open CanonicalRHRoute

private theorem exp_mode_half_shift
    (i : PairIndex) (n : ℤ) :
    Complex.exp
        (((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (L_m i : ℂ)) *
          ((L_m i : ℂ) / 2)) =
      (-1 : ℂ) ^ n := by
  have hL : (L_m i : ℂ) ≠ 0 := by
    exact_mod_cast (logLength_pos i).ne'
  have harg :
      ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (L_m i : ℂ)) *
          ((L_m i : ℂ) / 2) =
        (n : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    field_simp [hL]
  rw [harg, Complex.exp_int_mul, Complex.exp_pi_mul_I]

private theorem finiteLogFourierTrial_add_half_eq_centeredTrialDensity
    (D : CoefficientFamily) (i : PairIndex) (t : ℝ) :
    finiteLogFourierTrial
        (L_m i) (modeSet i) (D.kTrial i) (t + L_m i / 2) =
      centeredTrialDensity D i t := by
  unfold finiteLogFourierTrial centeredTrialDensity
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [show ((t + L_m i / 2 : ℝ) : ℂ) =
      (t : ℂ) + (L_m i : ℂ) / 2 by norm_num]
  rw [mul_add, Complex.exp_add, exp_mode_half_shift]
  ring

private theorem centered_integrand_shift
    (D : CoefficientFamily) (i : PairIndex) (z : ℂ) (t : ℝ) :
    Complex.exp (-Complex.I * z * (L_m i : ℂ) / 2) *
        (finiteLogFourierTrial
            (L_m i) (modeSet i) (D.kTrial i) (t + L_m i / 2) *
          Complex.exp (Complex.I * z * ((t + L_m i / 2 : ℝ) : ℂ))) =
      centeredTrialDensity D i t *
        Complex.exp (Complex.I * z * (t : ℂ)) := by
  rw [finiteLogFourierTrial_add_half_eq_centeredTrialDensity]
  rw [show ((t + L_m i / 2 : ℝ) : ℂ) =
      (t : ℂ) + (L_m i : ℂ) / 2 by norm_num]
  rw [mul_add, Complex.exp_add]
  have hcancel :
      Complex.exp (-Complex.I * (z * (L_m i : ℂ)) / 2) *
          Complex.exp (Complex.I * z * ((L_m i : ℂ) / 2)) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  calc
    _ =
        (Complex.exp (-Complex.I * (z * (L_m i : ℂ)) / 2) *
            Complex.exp (Complex.I * z * ((L_m i : ℂ) / 2))) *
          (centeredTrialDensity D i t *
            Complex.exp (Complex.I * z * (t : ℂ))) := by ring_nf
    _ = _ := by rw [hcancel, one_mul]

/-- The source-locked raw transform is exactly the Fourier transform of the
centered trial density on the centered logarithmic window. -/
theorem rawFplus_eq_centeredTrialDensity_transform
    (D : CoefficientFamily)
    (i : PairIndex)
    (z : ℂ) :
    rawFplus D i z =
      ∫ t in Set.Icc (-(L_m i) / 2) (L_m i / 2),
        centeredTrialDensity D i t *
          Complex.exp (Complex.I * z * (t : ℂ)) := by
  rw [← rawFplus_eq_D0_integral]
  unfold finiteFplusCenteredIntegral
  have hshift :
      (∫ t : ℝ in -(L_m i) / 2..L_m i / 2,
        finiteLogFourierTrial
            (L_m i) (modeSet i) (D.kTrial i) (t + L_m i / 2) *
          Complex.exp (Complex.I * z * ((t + L_m i / 2 : ℝ) : ℂ))) =
        ∫ x : ℝ in 0..L_m i,
          finiteLogFourierTrial (L_m i) (modeSet i) (D.kTrial i) x *
            Complex.exp (Complex.I * z * (x : ℂ)) := by
    convert intervalIntegral.integral_comp_add_right
      (a := -(L_m i) / 2) (b := L_m i / 2)
      (fun x : ℝ =>
        finiteLogFourierTrial (L_m i) (modeSet i) (D.kTrial i) x *
          Complex.exp (Complex.I * z * (x : ℂ)))
      (L_m i / 2) using 1
    all_goals ring_nf
  rw [← hshift]
  rw [← intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_congr
    (fun t _ht => centered_integrand_shift D i z t)]
  have hwindow : -(L_m i) / 2 ≤ L_m i / 2 := by
    linarith [logLength_pos i]
  rw [intervalIntegral.integral_of_le hwindow]
  rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- On a closed centered substrip, the exact centered transform is dominated
by the corresponding weighted critical moment. -/
theorem rawFplus_norm_le_centeredCriticalMoment
    (D : CoefficientFamily)
    (i : PairIndex)
    (σ : ℝ)
    (hσ : 0 ≤ σ)
    (z : ℂ)
    (hz : |z.im| ≤ σ) :
    ‖rawFplus D i z‖ ≤
      centeredCriticalMoment D i σ := by
  have _hσ : 0 ≤ σ := hσ
  rw [rawFplus_eq_centeredTrialDensity_transform]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  unfold centeredCriticalMoment
  have hupper :
      IntegrableOn
        (fun t : ℝ =>
          ‖centeredTrialDensity D i t‖ * Real.exp (σ * |t|))
        (Set.Icc (-(L_m i) / 2) (L_m i / 2)) := by
    apply Continuous.integrableOn_Icc
    unfold centeredTrialDensity
    fun_prop
  apply MeasureTheory.integral_mono_of_nonneg
  · exact Eventually.of_forall (fun _ => norm_nonneg _)
  · exact hupper
  · exact Eventually.of_forall (fun t => by
      dsimp
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hraw :
          -z.im * t ≤ |z.im| * |t| := by
        calc
          -z.im * t ≤ |-z.im * t| := le_abs_self _
          _ = |z.im| * |t| := by rw [abs_mul, abs_neg]
      have hstrip : |z.im| * |t| ≤ σ * |t| :=
        mul_le_mul_of_nonneg_right hz (abs_nonneg t)
      simpa [Complex.mul_re] using hraw.trans hstrip)

/-- Uniform boundedness of the normalized selected family on every strict
closed substrip of the centered critical strip.  This is deliberately weaker
than whole-plane local boundedness of the unnormalized raw family. -/
def SelectedPostAnchorClosedSubstripBounded
    (D : CanonicalData) : Prop :=
  ∀ σ : ℝ, 0 ≤ σ → σ < 1 / 2 →
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ k : ℕ, ∀ z : ℂ, |z.im| ≤ σ →
        ‖selectedFamily
          (canonicalApproximation D) k z‖ ≤ M

/-- The selected critical-moment ratio cancels the exact central normalization
denominator and leaves a uniform post-anchor bound on each strict closed
substrip. -/
theorem selectedPostAnchorClosedSubstripBounded_of_criticalMomentRatio
    (D : CanonicalData)
    (hRatio :
      CenteredTrialCriticalMomentRatio D.kTrial D.parent) :
    SelectedPostAnchorClosedSubstripBounded D := by
  intro σ hσ hσhalf
  obtain ⟨Cσ, hCσ, hmoment⟩ := hRatio.2 σ hσ hσhalf
  refine ⟨‖centeredXi 0‖ * Cσ,
    mul_nonneg (norm_nonneg _) hCσ, ?_⟩
  intro k z hz
  let i : CentralIndex D.kTrial := D.parent (D.extract k)
  have hraw :
      ‖rawFplus D.kTrial i.1 z‖ ≤
        centeredCriticalMoment D.kTrial i.1 σ :=
    rawFplus_norm_le_centeredCriticalMoment
      D.kTrial i.1 σ hσ z hz
  have hratioAt :
      centeredCriticalMoment D.kTrial i.1 σ ≤
        Cσ * ‖rawFplus D.kTrial i.1 0‖ := by
    simpa [i] using hmoment (D.extract k)
  have hrawBound :
      ‖rawFplus D.kTrial i.1 z‖ ≤
        Cσ * ‖rawFplus D.kTrial i.1 0‖ :=
    hraw.trans hratioAt
  have hden : 0 < ‖rawFplus D.kTrial i.1 0‖ :=
    norm_pos_iff.mpr (rawFplus_zero_ne D.kTrial i)
  change ‖centeredPstarFamily D.kTrial i z‖ ≤
    ‖centeredXi 0‖ * Cσ
  unfold centeredPstarFamily
  rw [norm_mul, norm_div]
  calc
    ‖centeredXi 0‖ / ‖rawFplus D.kTrial i.1 0‖ *
          ‖rawFplus D.kTrial i.1 z‖
        ≤
      ‖centeredXi 0‖ / ‖rawFplus D.kTrial i.1 0‖ *
          (Cσ * ‖rawFplus D.kTrial i.1 0‖) := by
            exact mul_le_mul_of_nonneg_left hrawBound
              (div_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖centeredXi 0‖ * Cσ := by
      field_simp [hden.ne']

#print axioms rawFplus_norm_le_centeredCriticalMoment
#print axioms selectedPostAnchorClosedSubstripBounded_of_criticalMomentRatio

end Q3.RouteB.D0Pstar
