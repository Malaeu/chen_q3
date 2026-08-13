import Q3.Proofs.RouteB.D0LogWindowMeasureTransport
import Q3.Proofs.RouteB.D0PstarSourceCCMOddMassReflectionDefect
import Q3.Proofs.RouteB.D0AnchorFloor

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Inversion symmetry to production coefficient reflection

This file transports multiplicative inversion symmetry of an actual pointwise
comparison packet to exact reflection symmetry of the production logarithmic
Fourier coefficients.  The proof uses the existing source-locked
`du/u -> dx` transport and the exact phase identity `exp (2*pi*I*n) = 1`.

It does not assert that the finite prolate source trial is inversion even.
Instead, its final theorem supplies the non-circular comparison packet needed
by the exact odd-mass receiver.
-/

private theorem lambda_m_pos_local (i : PairIndex) :
    0 < lambda_m i := by
  rw [lambda_m]
  exact Real.sqrt_pos.2 (by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm))

private theorem lambda_m_sq_local (i : PairIndex) :
    lambda_m i * lambda_m i = (i.m : ℝ) := by
  rw [lambda_m, Real.mul_self_sqrt]
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm).le

private theorem exp_logWindow_reflection_div_lambda
    (i : PairIndex) (x : ℝ) :
    Real.exp (L_m i - x) / lambda_m i =
      (Real.exp x / lambda_m i)⁻¹ := by
  have hlam : 0 < lambda_m i := lambda_m_pos_local i
  have hlog : Real.exp (L_m i) = (i.m : ℝ) := by
    rw [L_m, logLength, Real.exp_log]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm)
  rw [Real.exp_sub, hlog, ← lambda_m_sq_local i]
  field_simp

private theorem reflected_mode_inner
    (i : PairIndex) (n : ℤ) (g : ℝ → ℂ) (x : ℝ)
    (heven : g ((Real.exp x / lambda_m i)⁻¹) =
      g (Real.exp x / lambda_m i)) :
    inner ℂ
        (((Real.sqrt (L_m i))⁻¹ : ℂ) *
          Complex.exp
            (2 * Real.pi * Complex.I * (-n) *
              ((L_m i - x) / L_m i)))
        (g (Real.exp (L_m i - x) / lambda_m i)) =
      inner ℂ
        (((Real.sqrt (L_m i))⁻¹ : ℂ) *
          Complex.exp
            (2 * Real.pi * Complex.I * n * (x / L_m i)))
        (g (Real.exp x / lambda_m i)) := by
  rw [exp_logWindow_reflection_div_lambda i x, heven]
  rw [RCLike.inner_apply', RCLike.inner_apply']
  congr 1
  rw [map_mul, map_mul, ← Complex.exp_conj, ← Complex.exp_conj]
  congr 1
  simp only [Complex.conj_ofReal, map_mul, map_ofNat,
    Complex.conj_I, map_neg, map_intCast, map_div₀, map_sub]
  rw [show
      Complex.exp
          (2 * Real.pi * -Complex.I * (-n : ℂ) *
            (((L_m i : ℂ) - x) / L_m i)) =
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) *
          Complex.exp
            (2 * Real.pi * -Complex.I * (n : ℂ) *
              ((x : ℂ) / L_m i)) by
    rw [← Complex.exp_add]
    congr 1
    field_simp [(show (L_m i : ℂ) ≠ 0 by
      exact_mod_cast (logLength_pos i).ne')]
    ring]
  have hphase :
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by
    rw [show 2 * Real.pi * Complex.I * (n : ℂ) =
      (n : ℂ) * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  rw [hphase, one_mul]

/-- Multiplicative inversion symmetry on the literal source window implies
exact reflection symmetry of every production logarithmic Fourier
coefficient.  The hypothesis is on the physical function, not on its
coefficients. -/
theorem inner_V_neg_eq_inner_V_of_inversion_even
    (i : PairIndex) (n : ℤ) (g : ℝ → ℂ)
    (hg : MemLp g 2 (dStar.restrict (I_m i)))
    (heven : ∀ u ∈ I_m i, g u⁻¹ = g u) :
    inner ℂ (V_n_m i (-n)) (MemLp.toLp g hg) =
      inner ℂ (V_n_m i n) (MemLp.toLp g hg) := by
  have hlam : 0 < lambda_m i := lambda_m_pos_local i
  have hv (r : ℤ) :
      (V_n_m i r : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)]
        (fun u : ℝ =>
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * r *
                (Real.log (lambda_m i * u) / L_m i))) := by
    unfold V_n_m
    apply MemLp.coeFn_toLp
  have hvneg := hv (-n)
  have hvpos := hv n
  have hgcoe :
      (MemLp.toLp g hg : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)] g := by
    apply MemLp.coeFn_toLp
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc
    _ = ∫ u : ℝ,
          inner ℂ
            (((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * (-n) *
                  (Real.log (lambda_m i * u) / L_m i)))
            (g u) ∂(dStar.restrict (I_m i)) := by
      apply integral_congr_ae
      filter_upwards [hvneg, hgcoe] with u hvu hgu
      rw [hvu, hgu]
      simp only [Int.cast_neg]
    _ = ∫ x : ℝ in Set.Icc 0 (L_m i),
          inner ℂ
            (((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * (-n) * (x / L_m i)))
            (g (Real.exp x / lambda_m i)) := by
      rw [← integral_comp_logWindow_dStar i]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        (measurableSet_Icc : MeasurableSet (I_m i))] with u hu
      have hu_pos : 0 < u := (inv_pos.mpr hlam).trans_le hu.1
      rw [Real.exp_log (mul_pos hlam hu_pos)]
      field_simp
    _ = ∫ x : ℝ in Set.Icc 0 (L_m i),
          inner ℂ
            (((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * n * (x / L_m i)))
            (g (Real.exp x / lambda_m i)) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le (logLength_pos i).le,
        ← intervalIntegral.integral_of_le (logLength_pos i).le]
      let f : ℝ → ℂ := fun x =>
        inner ℂ
          (((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * (-n) * (x / L_m i)))
          (g (Real.exp x / lambda_m i))
      have hreflect :
          (∫ x : ℝ in (0 : ℝ)..L_m i, f (L_m i - x)) =
            ∫ x : ℝ in (0 : ℝ)..L_m i, f x := by
        simpa only [sub_self, sub_zero] using
          (intervalIntegral.integral_comp_sub_left
            (a := (0 : ℝ)) (b := L_m i) f (L_m i))
      change (∫ x : ℝ in (0 : ℝ)..L_m i, f x) = _
      rw [← hreflect]
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) (L_m i) := by
        simpa [uIcc_of_le (logLength_pos i).le] using hx
      have hu_mem : Real.exp x / lambda_m i ∈ I_m i := by
        rw [I_m]
        constructor
        · rw [inv_eq_one_div]
          exact (div_le_div_iff_of_pos_right hlam).2 (by
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr hx'.1)
        · exact (div_le_iff₀ hlam).2 (by
            calc
              Real.exp x ≤ Real.exp (L_m i) :=
                Real.exp_le_exp.mpr hx'.2
              _ = (i.m : ℝ) := by
                rw [L_m, logLength, Real.exp_log]
                exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm)
              _ = lambda_m i * lambda_m i :=
                (lambda_m_sq_local i).symm)
      simpa only [f, Complex.ofReal_sub] using
        reflected_mode_inner i n g x (heven _ hu_mem)
    _ = ∫ u : ℝ,
          inner ℂ
            (((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * n *
                  (Real.log (lambda_m i * u) / L_m i)))
            (g u) ∂(dStar.restrict (I_m i)) := by
      rw [← integral_comp_logWindow_dStar i]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        (measurableSet_Icc : MeasurableSet (I_m i))] with u hu
      have hu_pos : 0 < u := (inv_pos.mpr hlam).trans_le hu.1
      rw [Real.exp_log (mul_pos hlam hu_pos)]
      field_simp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hvpos, hgcoe] with u hvu hgu
      rw [hvu, hgu]

/-- Direct production corollary: an actual inversion-even ambient packet
controls the exact literal source-row odd mass by its squared approximation
error.  No coefficient symmetry is assumed. -/
theorem sourceCCMComplexOddMass_le_norm_sub_sq_of_inversion_even
    (S : ProlateCanonicalSourceData)
    (i : PairIndex)
    (g : ℝ → ℂ)
    (hg : MemLp g 2 (dStar.restrict (I_m i)))
    (heven : ∀ u ∈ I_m i, g u⁻¹ = g u) :
    sourceCCMComplexOddMass S i ≤
      ‖(kTrial_m_N
          i
          (prolateCombination (S.source.pair i))
          (S.source.eStar_memLp i)
          (S.source.trialNonzero i) : H_m i) - MemLp.toLp g hg‖ ^ 2 := by
  apply sourceCCMComplexOddMass_le_norm_sub_sq_of_even_coefficients
  intro j
  rw [ccmModeFinite_neg]
  exact inner_V_neg_eq_inner_V_of_inversion_even
    i (ccmModeFinite i.N j) g hg heven

/-- The zero production mode turns approximation to a concrete ambient packet
into a quantitative lower bound for the unnormalized projected source trial.
The right side is the denominator used by `kTrial_m_N`; no denominator floor
is assumed. -/
theorem norm_inner_V0_sub_approximation_error_le_projected_trial_norm
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i)))
    (f : H_m i) :
    ‖inner ℂ (V_n_m i 0) f‖ -
        ‖gTrial_m i hTrial_m hE_star - f‖ ≤
      ‖gTrial_m_N i hTrial_m hE_star‖ := by
  have hv0 : ‖V_n_m i 0‖ = 1 :=
    (V_n_m_orthonormal i).norm_eq_one 0
  have hsplit :
      inner ℂ (V_n_m i 0) f =
        inner ℂ (V_n_m i 0) (gTrial_m i hTrial_m hE_star) +
          inner ℂ (V_n_m i 0)
            (f - gTrial_m i hTrial_m hE_star) := by
    rw [inner_sub_right]
    ring
  have herror :
      ‖inner ℂ (V_n_m i 0)
          (f - gTrial_m i hTrial_m hE_star)‖ ≤
        ‖gTrial_m i hTrial_m hE_star - f‖ := by
    calc
      _ ≤ ‖V_n_m i 0‖ *
          ‖f - gTrial_m i hTrial_m hE_star‖ :=
        norm_inner_le_norm _ _
      _ = ‖gTrial_m i hTrial_m hE_star - f‖ := by
        rw [hv0, one_mul, norm_sub_rev]
  have hprojected :
      ‖inner ℂ (V_n_m i 0)
          (gTrial_m i hTrial_m hE_star)‖ ≤
        ‖gTrial_m_N i hTrial_m hE_star‖ := by
    rw [← inner_V0_gTrial_m_N_eq i hTrial_m hE_star]
    calc
      _ ≤ ‖V_n_m i 0‖ *
          ‖(gTrial_m_N i hTrial_m hE_star : H_m i)‖ :=
        norm_inner_le_norm _ _
      _ = ‖gTrial_m_N i hTrial_m hE_star‖ := by
        rw [hv0, one_mul, Submodule.coe_norm]
  rw [hsplit]
  calc
    ‖inner ℂ (V_n_m i 0)
          (gTrial_m i hTrial_m hE_star) +
        inner ℂ (V_n_m i 0)
          (f - gTrial_m i hTrial_m hE_star)‖ -
          ‖gTrial_m i hTrial_m hE_star - f‖ ≤
        ‖inner ℂ (V_n_m i 0)
          (gTrial_m i hTrial_m hE_star)‖ := by
      linarith [norm_add_le
        (inner ℂ (V_n_m i 0) (gTrial_m i hTrial_m hE_star))
        (inner ℂ (V_n_m i 0)
          (f - gTrial_m i hTrial_m hE_star))]
    _ ≤ _ := hprojected

#print axioms inner_V_neg_eq_inner_V_of_inversion_even
#print axioms sourceCCMComplexOddMass_le_norm_sub_sq_of_inversion_even
#print axioms norm_inner_V0_sub_approximation_error_le_projected_trial_norm

end Q3.RouteB.D0Pstar
