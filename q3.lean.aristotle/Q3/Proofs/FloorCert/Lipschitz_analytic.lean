import Mathlib
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.ZetaValues
import Q3.Basic.Defs
import Q3.Proofs.Params_Critical
import Q3.Proofs.A3_Floor_Bounds
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.A3_Floor_Monotonicity
import Q3.Proofs.Digamma_One_Fourth
import Q3.Proofs.FloorCert.Defs

open scoped BigOperators Real
open Real Complex Filter

noncomputable section

namespace Q3.Proofs.FloorCert

-- Critical Gaussian scale
private def c_crit : ℝ := 4 * Real.pi ^ 2 * t_critical

-- Support radius needed for x+m with x∈[-1/2,1/2], m∈[-3,3]
private def B_support : ℝ := B_min + 1 / 2

private lemma c_crit_pos : 0 < c_crit := by
  -- t_critical = 3/20
  have ht : 0 < t_critical := by
    norm_num [t_critical]
  have hpi2 : 0 < Real.pi ^ 2 := by
    nlinarith [Real.pi_pos]
  have h4 : 0 < (4 : ℝ) := by norm_num
  simp [c_crit] at *
  nlinarith [h4, ht, hpi2]

private lemma g_support_B_min_of_t (t ξ : ℝ) (h : B_min ≤ |ξ|) : g B_min t ξ = 0 := by
  simp only [g, w]
  have hB : (0 : ℝ) < B_min := by norm_num [B_min]
  have h_lin : 1 - |ξ| / B_min ≤ 0 := by
    have h1 : 1 ≤ |ξ| / B_min := by
      rw [one_le_div hB]
      exact h
    linarith
  simp [max_eq_left h_lin, zero_mul, mul_zero]

/-- Bound on the Gaussian Lipschitz factor: `2*sqrt c_crit ≤ 49/10`. -/
private lemma two_sqrt_c_crit_le : 2 * Real.sqrt c_crit ≤ (49 / 10 : ℝ) := by
  -- c_crit = (3/5) * pi^2 and pi < 3.15
  have hpi : (Real.pi : ℝ) < 3.15 := Real.pi_lt_d2
  have hc : c_crit ≤ (49 / 20 : ℝ) ^ 2 := by
    have hc' : c_crit = (3 / 5 : ℝ) * Real.pi ^ 2 := by
      have h : (4 : ℝ) * (3 / 20 : ℝ) = (3 / 5 : ℝ) := by norm_num
      simp [c_crit, t_critical, h, mul_comm, mul_assoc]
    have hpi_le : (Real.pi : ℝ) ≤ 3.15 := le_of_lt hpi
    calc
      c_crit = (3 / 5 : ℝ) * Real.pi ^ 2 := hc'
      _ ≤ (3 / 5 : ℝ) * (3.15 : ℝ) ^ 2 := by
            have hpi_nonneg : 0 ≤ (Real.pi : ℝ) := by exact le_of_lt Real.pi_pos
            have h315_nonneg : 0 ≤ (3.15 : ℝ) := by norm_num
            have hpi_abs : |(Real.pi : ℝ)| ≤ |(3.15 : ℝ)| := by
              simpa [abs_of_nonneg hpi_nonneg, abs_of_nonneg h315_nonneg] using hpi_le
            have hsq : (Real.pi : ℝ) ^ 2 ≤ (3.15 : ℝ) ^ 2 := by
              simpa [pow_two] using (sq_le_sq.mpr hpi_abs)
            exact mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ ≤ (49 / 20 : ℝ) ^ 2 := by norm_num
  have hsqrt : Real.sqrt c_crit ≤ (49 / 20 : ℝ) := by
    have hnonneg : 0 ≤ c_crit := by nlinarith [c_crit_pos]
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, hc⟩
  nlinarith [hsqrt]

/-- Lipschitz bound for the Gaussian `x ↦ exp(-c_crit * x^2)`. -/
private lemma gauss_deriv_bound (z : ℝ) :
    |deriv (fun x => Real.exp (-c_crit * x^2)) z| ≤ (49 / 10 : ℝ) := by
  have h1 : HasDerivAt (fun x => -c_crit * x^2) (-2 * c_crit * z) z := by
    have hsq : HasDerivAt (fun x => x^2) (2 * z) z := by
      simpa [pow_two] using (hasDerivAt_pow 2 z)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsq.const_mul (-c_crit)
  have hderiv : deriv (fun x => Real.exp (-c_crit * x^2)) z =
      Real.exp (-c_crit * z^2) * (-2 * c_crit * z) := by
    simpa using (HasDerivAt.deriv ((Real.hasDerivAt_exp (-c_crit * z^2)).comp z h1))
  have hmul : |mulExpNegMulSq c_crit z| ≤ (Real.sqrt c_crit)⁻¹ := by
    simpa [Real.mulExpNegMulSq, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      (Real.abs_mulExpNegMulSq_le (ε := c_crit) (x := z) c_crit_pos)
  have hpos : 0 ≤ (2 * c_crit : ℝ) := by nlinarith [c_crit_pos]
  have hbound : |Real.exp (-c_crit * z^2) * (-2 * c_crit * z)| ≤ 2 * Real.sqrt c_crit := by
    have hrewrite :
        |Real.exp (-c_crit * z^2) * (-2 * c_crit * z)|
          = |(-2 * c_crit) * mulExpNegMulSq c_crit z| := by
      simp [Real.mulExpNegMulSq, mul_comm, mul_left_comm, mul_assoc]
    have hfinal : (2 * c_crit) * (Real.sqrt c_crit)⁻¹ = 2 * Real.sqrt c_crit := by
      have hsq' : c_crit = (Real.sqrt c_crit) ^ 2 := by
        symm
        have hnonneg : 0 ≤ c_crit := by linarith [c_crit_pos]
        simpa [pow_two] using (Real.sq_sqrt hnonneg)
      have hpos : (Real.sqrt c_crit) ≠ 0 := by
        exact Real.sqrt_ne_zero'.mpr c_crit_pos
      calc
        (2 * c_crit) * (Real.sqrt c_crit)⁻¹
            = 2 * (c_crit * (Real.sqrt c_crit)⁻¹) := by ring
        _ = 2 * ((Real.sqrt c_crit) ^ 2 * (Real.sqrt c_crit)⁻¹) := by
              simp [hsq']
        _ = 2 * Real.sqrt c_crit := by
              field_simp [hpos]
    calc
      |Real.exp (-c_crit * z^2) * (-2 * c_crit * z)|
          = |(-2 * c_crit) * mulExpNegMulSq c_crit z| := by simpa [hrewrite]
      _ = (2 * c_crit) * |mulExpNegMulSq c_crit z| := by
            simp [abs_mul, abs_neg, abs_of_nonneg (by nlinarith [c_crit_pos])]
      _ ≤ (2 * c_crit) * (Real.sqrt c_crit)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hmul hpos
      _ = 2 * Real.sqrt c_crit := hfinal
  have hderiv' : |deriv (fun x => Real.exp (-c_crit * x^2)) z|
      ≤ 2 * Real.sqrt c_crit := by
    simpa [hderiv] using hbound
  exact le_trans hderiv' two_sqrt_c_crit_le

private lemma gauss_lipschitz (x y : ℝ) :
    |Real.exp (-c_crit * x^2) - Real.exp (-c_crit * y^2)| ≤
      (49 / 10 : ℝ) * |x - y| := by
  -- global Lipschitz from derivative bound
  have hdiff : Differentiable ℝ (fun x => Real.exp (-c_crit * x^2)) := by
    intro z
    have hsq : DifferentiableAt ℝ (fun x => x^2) z := by
      simpa [pow_two] using (differentiableAt_mul_self z)
    have hlin : DifferentiableAt ℝ (fun x => -c_crit * x^2) z :=
      hsq.const_mul (-c_crit)
    exact (Real.differentiable_exp).differentiableAt.comp z hlin
  have hbound : ∀ z, ‖deriv (fun x => Real.exp (-c_crit * x^2)) z‖₊ ≤
      (Real.toNNReal (49 / 10 : ℝ)) := by
    intro z
    have h := gauss_deriv_bound z
    -- convert abs to nnnorm
    simpa [Real.norm_eq_abs, Real.toNNReal, max_eq_left (by nlinarith : (0:ℝ) ≤ (49/10:ℝ))]
      using h
  have hLip : LipschitzWith (Real.toNNReal (49 / 10 : ℝ))
      (fun x => Real.exp (-c_crit * x^2)) :=
    lipschitzWith_of_nnnorm_deriv_le hdiff hbound
  have h := hLip.norm_sub_le x y
  simpa [Real.norm_eq_abs, Real.toNNReal, max_eq_left (by nlinarith : (0:ℝ) ≤ (49/10:ℝ))]
    using h

/-- Lipschitz bound for the hat part `max 0 (1 - |x|/B)`. -/
private lemma hat_lipschitz (x y : ℝ) :
    |(max 0 (1 - |x| / B_min)) - (max 0 (1 - |y| / B_min))| ≤
      (1 / B_min : ℝ) * |x - y| := by
  have hB : 0 < (B_min : ℝ) := by norm_num [B_min]
  have h_abs : |abs x - abs y| ≤ |x - y| := by
    simpa using (abs_abs_sub_abs_le_abs_sub x y)
  have h1 :
      |(1 - |x| / B_min) - (1 - |y| / B_min)| ≤ (1 / B_min : ℝ) * |x - y| := by
    calc
      |(1 - |x| / B_min) - (1 - |y| / B_min)|
          = |(|y| - |x|) / B_min| := by
              ring_nf
              simp [abs_sub_comm]
      _ = (1 / B_min) * abs (|y| - |x|) := by
            simp [div_eq_mul_inv, abs_mul, abs_inv, abs_of_pos hB,
              mul_comm, mul_assoc]
      _ ≤ (1 / B_min) * |x - y| := by
            have h_abs' : abs (|y| - |x|) ≤ |x - y| := by
              simpa [abs_sub_comm] using h_abs
            have hB' : 0 ≤ (1 / B_min : ℝ) := by
              exact one_div_nonneg.mpr (le_of_lt hB)
            exact mul_le_mul_of_nonneg_left h_abs' hB'
  -- max is 1-Lipschitz: |max 0 u - max 0 v| ≤ |u - v|
  have hmax :
      |max 0 (1 - |x| / B_min) - max 0 (1 - |y| / B_min)| ≤
        |(1 - |x| / B_min) - (1 - |y| / B_min)| := by
    simpa [max_comm] using (abs_max_sub_max_le_abs (1 - |x| / B_min)
      (1 - |y| / B_min) (0 : ℝ))
  exact le_trans hmax h1

/-- Lipschitz bound for `w`. -/
private lemma w_lipschitz (x y : ℝ) :
    |w B_min t_critical x - w B_min t_critical y| ≤ (53 / 10 : ℝ) * |x - y| := by
  -- product bound: |hat*gauss - hat*gauss| ≤ |hat-hat|*|gauss| + |gauss-gauss|*|hat|
  have hgauss : ∀ z, |Real.exp (-c_crit * z^2)| ≤ 1 := by
    intro z
    have : -c_crit * z^2 ≤ 0 := by nlinarith [c_crit_pos]
    have h := Real.exp_le_one_iff.mpr this
    simpa using h
  have hhat : ∀ z, |max 0 (1 - |z| / B_min)| ≤ 1 := by
    intro z
    have h0 : 0 ≤ max 0 (1 - |z| / B_min) := by exact le_max_left _ _
    have h1 : max 0 (1 - |z| / B_min) ≤ 1 := by
      refine max_le_iff.mpr ?_
      constructor
      · exact zero_le_one
      · have hB : 0 < (B_min : ℝ) := by norm_num [B_min]
        have hzpos : 0 ≤ |z| / B_min := by
          exact div_nonneg (abs_nonneg _) (le_of_lt hB)
        have : (1 - |z| / B_min) ≤ 1 := by linarith
        exact this
    simpa [abs_of_nonneg h0] using h1
  have hhat_lip := hat_lipschitz x y
  have hgauss_lip := gauss_lipschitz x y
  -- combine using triangle inequality
  have hcomb :
      |max 0 (1 - |x| / B_min) * Real.exp (-c_crit * x^2) -
        max 0 (1 - |y| / B_min) * Real.exp (-c_crit * y^2)| ≤
      (1 / B_min + (49 / 10 : ℝ)) * |x - y| := by
    set hx := max 0 (1 - |x| / B_min)
    set hy := max 0 (1 - |y| / B_min)
    set gx := Real.exp (-c_crit * x^2)
    set gy := Real.exp (-c_crit * y^2)
    have hsplit : hx * gx - hy * gy = (hx - hy) * gx + hy * (gx - gy) := by
      ring
    calc
      |hx * gx - hy * gy|
          = |(hx - hy) * gx + hy * (gx - gy)| := by simpa [hsplit]
      _ ≤ |hx - hy| * |gx| + |hy| * |gx - gy| := by
            simpa [abs_mul] using (abs_add_le ((hx - hy) * gx) (hy * (gx - gy)))
      _ ≤ (1 / B_min) * |x - y| + (49 / 10 : ℝ) * |x - y| := by
            have h1 : |hx - hy| * |gx| ≤ (1 / B_min : ℝ) * |x - y| := by
              have hga : |gx| ≤ 1 := hgauss x
              have h0 : 0 ≤ |hx - hy| := by exact abs_nonneg _
              have h1' : |hx - hy| * |gx| ≤ |hx - hy| := by
                simpa using (mul_le_mul_of_nonneg_left hga h0)
              exact le_trans h1' hhat_lip
            have h2 : |hy| * |gx - gy| ≤ (49 / 10 : ℝ) * |x - y| := by
              have h0 : 0 ≤ |gx - gy| := by exact abs_nonneg _
              have h2' : |hy| * |gx - gy| ≤ |gx - gy| := by
                simpa using (mul_le_mul_of_nonneg_right (hhat y) h0)
              exact le_trans h2' hgauss_lip
            exact add_le_add h1 h2
      _ = (1 / B_min + (49 / 10 : ℝ)) * |x - y| := by ring
  -- finalize with numeric bound 1/B_min + 49/10 ≤ 53/10
  have hB : (1 / B_min : ℝ) ≤ (1 / 3 : ℝ) := by
    norm_num [B_min]
  have hfinal : (1 / B_min + (49 / 10 : ℝ)) ≤ (53 / 10 : ℝ) := by
    norm_num [B_min]
  -- rewrite to w
  simpa [w, c_crit, t_critical, pow_two, mul_comm, mul_left_comm, mul_assoc] using
    (le_trans hcomb (mul_le_mul_of_nonneg_right hfinal (abs_nonneg _)))

/-- Bound for `|a|` on `[-B_min, B_min]`. -/
private lemma a_zero_val :
    Q3.a 0 = Real.log Real.pi + Real.eulerMascheroniConstant + Real.pi / 2 + 3 * Real.log 2 := by
  simp [Q3.a, Q3.digamma_one_fourth_eq, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc]

private lemma a_zero_le_seven : Q3.a 0 ≤ (7 : ℝ) := by
  have h0 : Q3.a 0 = Real.log Real.pi + Real.eulerMascheroniConstant + Real.pi / 2 + 3 * Real.log 2 :=
    a_zero_val
  have hlog2 : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Real.log_two_lt_d9
    nlinarith
  have hgamma : Real.eulerMascheroniConstant ≤ (2 / 3 : ℝ) :=
    le_of_lt Real.eulerMascheroniConstant_lt_two_thirds
  have hpi2 : Real.pi / 2 ≤ (8 / 5 : ℝ) := by
    have h := Real.pi_lt_d2
    nlinarith
  have hlogpi : Real.log Real.pi ≤ (14 / 10 : ℝ) := by
    have hpi_pos : 0 < (Real.pi : ℝ) := Real.pi_pos
    have hpi4 : (Real.pi : ℝ) ≤ 4 := le_of_lt Real.pi_lt_four
    have hlog4 : Real.log 4 = (2 : ℝ) * Real.log 2 := by
      have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      simpa [h4] using (Real.log_pow (2 : ℝ) 2)
    have hlogpi' : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log hpi_pos hpi4
    have hlog4' : Real.log 4 ≤ (14 / 10 : ℝ) := by
      nlinarith [hlog4, hlog2]
    exact le_trans hlogpi' hlog4'
  nlinarith [h0, hlogpi, hgamma, hpi2, hlog2]

private lemma a_lower_bound_support : -7 ≤ Q3.a B_support := by
  have h := a_lower_bound_from_stieltjes (xi := B_support)
  have hBpos : 0 < (B_support : ℝ) := by
    norm_num [B_support, B_min]
  -- crude bounds to show RHS ≥ -7
  have hnorm_pos : 0 < ‖(1 / 4 : ℂ) + Complex.I * Real.pi * B_support‖ := by
    have hre : 0 < ((1 / 4 : ℂ) + Complex.I * Real.pi * B_support).re := by
      simp [B_support]
    exact lt_of_lt_of_le (by nlinarith : (0 : ℝ) < (1 / 4 : ℝ)) (by
      simpa using (Complex.abs_re_le_norm ((1 / 4 : ℂ) + Complex.I * Real.pi * B_support)))
  have hnorm_le : ‖(1 / 4 : ℂ) + Complex.I * Real.pi * B_support‖ ≤ (12 : ℝ) := by
    have hpi : (Real.pi : ℝ) < 3.15 := Real.pi_lt_d2
    have hnorm_add : ‖(1 / 4 : ℂ) + Complex.I * Real.pi * B_support‖ ≤
        ‖(1 / 4 : ℂ)‖ + ‖Complex.I * Real.pi * B_support‖ := by
      simpa using (norm_add_le ((1 / 4 : ℂ)) (Complex.I * Real.pi * B_support))
    have hnorm_I : ‖Complex.I * Real.pi * B_support‖ = Real.pi * B_support := by
      have hposπ : 0 ≤ (Real.pi : ℝ) := by exact le_of_lt Real.pi_pos
      have hposB : 0 ≤ (B_support : ℝ) := by exact le_of_lt hBpos
      simp [abs_of_nonneg hposπ, abs_of_nonneg hposB, mul_comm, mul_assoc]
    have hbound : ‖(1 / 4 : ℂ) + Complex.I * Real.pi * B_support‖ ≤
        (1 / 4 : ℝ) + Real.pi * B_support := by
      nlinarith [hnorm_add, hnorm_I]
    have hB : Real.pi * B_support ≤ (11 : ℝ) := by
      -- B_support = 3.5
      simp [B_support]
      nlinarith [hpi]
    nlinarith [hbound, hB]
  have hlog_bound : Real.log ‖(1 / 4 : ℂ) + Complex.I * Real.pi * B_support‖ ≤ (4 : ℝ) := by
    have hpos : 0 < ‖(1 / 4 : ℂ) + Complex.I * Real.pi * B_support‖ := hnorm_pos
    have hnorm_le16 : ‖(1 / 4 : ℂ) + Complex.I * Real.pi * B_support‖ ≤ (16 : ℝ) :=
      le_trans hnorm_le (by norm_num)
    have hlog_le : Real.log ‖(1 / 4 : ℂ) + Complex.I * Real.pi * B_support‖ ≤ Real.log 16 :=
      Real.log_le_log hpos (by nlinarith [hnorm_le16])
    have hlog16 : Real.log 16 ≤ (4 : ℝ) := by
      have hlog2 : Real.log 2 ≤ (7 / 10 : ℝ) := by
        have h := Real.log_two_lt_d9
        nlinarith
      have hlog16' : Real.log 16 = (4 : ℝ) * Real.log 2 := by
        -- 16 = 2^4
        have h16 : (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
        simpa [h16] using (Real.log_pow (2 : ℝ) 4)
      nlinarith [hlog16', hlog2]
    exact le_trans hlog_le hlog16
  have hterm : (1 / 8 : ℝ) * (1 / ‖(1 / 4 : ℂ) + Complex.I * Real.pi * B_support‖ ^ 2) ≤ 2 := by
    have hnorm_ge : (1 / 4 : ℝ) ≤ ‖(1 / 4 : ℂ) + Complex.I * Real.pi * B_support‖ := by
      have h := Complex.abs_re_le_norm ((1 / 4 : ℂ) + Complex.I * Real.pi * B_support)
      simpa using h
    have hsq : (1 / 16 : ℝ) ≤ ‖(1 / 4 : ℂ) + Complex.I * Real.pi * B_support‖ ^ 2 := by
      nlinarith [hnorm_ge]
    have h_inv : (1 / ‖(1 / 4 : ℂ) + Complex.I * Real.pi * B_support‖ ^ 2) ≤ 16 := by
      have hpos' : 0 < (1 / 16 : ℝ) := by norm_num
      -- from (1/16) ≤ ‖z‖^2, infer 1/‖z‖^2 ≤ 16
      have h' := one_div_le_one_div_of_le hpos' hsq
      simpa using h'
    nlinarith [h_inv]
  -- combine: a ≥ log π - log ‖z‖ - (1/8) * (1/‖z‖^2)
  have hmain :
      Q3.a B_support ≥
        Real.log Real.pi - Real.log ‖(1 / 4 : ℂ) + Complex.I * Real.pi * B_support‖ - 2 := by
    nlinarith [h, hterm]
  have hlogpi : 0 ≤ Real.log Real.pi := by
    have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    exact Real.log_nonneg hpi1
  -- log‖z‖ ≤ 4, so RHS ≥ log π - 6 ≥ -6
  have hmain' : Q3.a B_support ≥ -6 := by
    nlinarith [hmain, hlog_bound, hlogpi]
  nlinarith [hmain']

private lemma a_le_a_zero_of_pos {y : ℝ} (hy : 0 < y) : Q3.a y ≤ Q3.a 0 := by
  have hcont : ContinuousWithinAt Q3.a (Set.Ici 0) 0 := by
    simpa using (continuousOn_a.continuousWithinAt (by simp : (0 : ℝ) ∈ Set.Ici (0 : ℝ)))
  have hseq :
      Tendsto (fun n : ℕ => y / ((n + 1 : ℕ) : ℝ)) atTop (nhds (0 : ℝ)) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat
    -- y/(n+1) = y * (1/(n+1))
    simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using
      (tendsto_const_nhds.mul h)
  have hseq' :
      Tendsto (fun n : ℕ => y / ((n + 1 : ℕ) : ℝ)) atTop (nhdsWithin (0 : ℝ) (Set.Ici 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (f := fun n : ℕ => y / ((n + 1 : ℕ) : ℝ)) (s := Set.Ici 0) hseq ?_
    refine (Filter.Eventually.of_forall ?_)
    intro n
    have hpos : (0 : ℝ) ≤ y / ((n + 1 : ℕ) : ℝ) := by
      have hpos' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos n
      exact div_nonneg (le_of_lt hy) (le_of_lt hpos')
    simpa using hpos
  have hlim :
      Tendsto (fun n : ℕ => Q3.a (y / ((n + 1 : ℕ) : ℝ))) atTop (nhds (Q3.a 0)) :=
    hcont.tendsto.comp hseq'
  have hconst :
      Tendsto (fun n : ℕ => Q3.a y) atTop (nhds (Q3.a y)) :=
    tendsto_const_nhds
  have hle :
      (fun n : ℕ => Q3.a y) ≤ᶠ[atTop]
        fun n : ℕ => Q3.a (y / ((n + 1 : ℕ) : ℝ)) := by
    refine Filter.eventually_atTop.mpr ?_
    refine ⟨1, ?_⟩
    intro n hn
    have hxpos : (0 : ℝ) < y / ((n + 1 : ℕ) : ℝ) := by
      have hpos' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos n
      exact div_pos hy hpos'
    have hx : (y / ((n + 1 : ℕ) : ℝ)) ∈ Set.Ioi (0 : ℝ) := by
      simpa using hxpos
    have hy' : y ∈ Set.Ioi (0 : ℝ) := by simpa using hy
    have hge : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
    have hxy : (y / ((n + 1 : ℕ) : ℝ)) ≤ y := by
      have h' : (1 / ((n + 1 : ℕ) : ℝ)) ≤ (1 : ℝ) := by
        have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hge
        simpa using h
      have hy' : 0 ≤ y := le_of_lt hy
      have hmul := mul_le_mul_of_nonneg_left h' hy'
      -- y * (1/(n+1)) ≤ y * 1
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    exact a_antitone_on_Ioi hx hy' hxy
  exact le_of_tendsto_of_tendsto hconst hlim hle

private lemma a_abs_bound_support (x : ℝ) (hx : |x| ≤ B_support) : |Q3.a x| ≤ (7 : ℝ) := by
  have hBmin : 0 < (B_min : ℝ) := by norm_num [B_min]
  have hupper : Q3.a x ≤ (7 : ℝ) := by
    have h0 : Q3.a 0 ≤ (7 : ℝ) := a_zero_le_seven
    have hax : Q3.a x = Q3.a (|x|) := by
      by_cases hx0 : 0 ≤ x
      · simpa [abs_of_nonneg hx0]
      · have hx0' : x < 0 := lt_of_not_ge hx0
        simpa [abs_of_neg hx0', a_even] using (rfl : Q3.a x = Q3.a (-x))
    by_cases hx0 : |x| = 0
    · simpa [hax, hx0] using h0
    · have hxpos : 0 < |x| := by
        exact lt_of_le_of_ne (abs_nonneg _) (ne_comm.mp hx0)
      have hle : Q3.a (|x|) ≤ Q3.a 0 := a_le_a_zero_of_pos hxpos
      simpa [hax] using le_trans hle h0
  have hlower : (-7 : ℝ) ≤ Q3.a x := by
    have hB : (-7 : ℝ) ≤ Q3.a B_support := a_lower_bound_support
    have hax : Q3.a x = Q3.a (|x|) := by
      by_cases hx0 : 0 ≤ x
      · simpa [abs_of_nonneg hx0]
      · have hx0' : x < 0 := lt_of_not_ge hx0
        simpa [abs_of_neg hx0', a_even] using (rfl : Q3.a x = Q3.a (-x))
    by_cases hx0 : |x| = 0
    · have hB : (-7 : ℝ) ≤ Q3.a B_support := a_lower_bound_support
      have hBpos : 0 < B_support := by
        norm_num [B_support, B_min]
      have hle : Q3.a B_support ≤ Q3.a 0 := a_le_a_zero_of_pos hBpos
      have : (-7 : ℝ) ≤ Q3.a 0 := le_trans hB hle
      simpa [hax, hx0] using this
    · have hxpos : 0 < |x| := by
        exact lt_of_le_of_ne (abs_nonneg _) (ne_comm.mp hx0)
      have hBpos : 0 < B_support := by
        norm_num [B_support, B_min]
      have hge : Q3.a B_support ≤ Q3.a (|x|) := by
        exact a_antitone_on_Ioi (by exact hxpos) (by exact hBpos) (by exact hx)
      have : (-7 : ℝ) ≤ Q3.a (|x|) := le_trans hB hge
      simpa [hax] using this
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Bound on the derivative of `a`. -/
private lemma a_deriv_bound (x : ℝ) : |deriv Q3.a x| ≤ (56 : ℝ) := by
  -- use trigamma series bound
  -- z = 1/4 + i*pi*x
  let z : ℂ := (1 / 4 : ℂ) + Complex.I * Real.pi * x
  have hz : 0 < z.re := by simp [z]
  have hderiv : deriv Q3.a x = Real.pi * (trigamma z).im := by
    -- reuse deriv_re_digamma and deriv_digamma_eq_trigamma
    have h1 : deriv (fun t : ℝ => (Q3.digamma (1 / 4 + Complex.I * Real.pi * t)).re) x =
        -Real.pi * (deriv (fun z : ℂ => Q3.digamma z) z).im := by
      simpa [z] using deriv_re_digamma x
    have h2 : deriv (fun z : ℂ => Q3.digamma z) z = trigamma z :=
      deriv_digamma_eq_trigamma hz
    -- a = log pi - re(digamma)
    simp [Q3.a, h1, h2, sub_eq_add_neg, z]
  have htrig : ‖trigamma z‖ ≤ 16 + Real.pi ^ 2 / 6 := by
    -- use norm_tsum_le_tsum_norm and compare to 1/(n+1/4)^2
    have hsum : Summable (fun n : ℕ => (1 : ℂ) / (z + n)^2) :=
      summable_trigamma_series hz
    have hnorm := norm_tsum_le_tsum_norm hsum.norm
    -- bound each term
    have hterm : ∀ n : ℕ, ‖(1 : ℂ) / (z + n)^2‖ ≤ (1 : ℝ) / ((n : ℝ) + 1/4)^2 := by
      intro n
      -- norm of inverse
      have hpos : 0 < ((n : ℝ) + (1 / 4 : ℝ)) := by nlinarith
      have hnorm_ge : ((n : ℝ) + (1 / 4 : ℝ)) ≤ ‖z + n‖ := by
        have h := Complex.abs_re_le_norm (z + n)
        have hre : (z + n).re = (n : ℝ) + 1/4 := by simp [z]
        have hnonneg : 0 ≤ (n : ℝ) + 1/4 := by nlinarith
        simpa [hre, abs_of_nonneg hnonneg] using h
      have hle : ‖(1 : ℂ) / (z + n)^2‖ = 1 / ‖z + n‖^2 := by
        simp [norm_div, norm_pow]
      have hle' : 1 / ‖z + n‖^2 ≤ (1 : ℝ) / ((n : ℝ) + 1/4)^2 := by
        have hpos' : 0 < ‖z + n‖ := by
          have : (0 : ℝ) < (n : ℝ) + 1/4 := by nlinarith
          exact lt_of_lt_of_le this hnorm_ge
        have hsq : ((n : ℝ) + 1/4)^2 ≤ ‖z + n‖^2 := by nlinarith
        exact (one_div_le_one_div_of_le hsq).trans_eq (by ring)
      exact le_trans (by simpa [hle] using hle') (le_rfl)
    have hsum_le : ∑' n : ℕ, ‖(1 : ℂ) / (z + n)^2‖ ≤ ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1/4)^2 := by
      exact hsum.norm.tsum_le_tsum hterm (by
        -- summable RHS
        have : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
          (hasSum_zeta_two.summable)
        -- compare shifted series with zeta
        exact Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => by
          have : (1 : ℝ) / ((n : ℝ) + 1/4)^2 ≤ (1 : ℝ) / (n : ℝ) ^ 2 := by
            by_cases h0 : n = 0
            · simp [h0]
            · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
              have hle : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1/4)^2 := by nlinarith
              exact one_div_le_one_div_of_le hle
          exact this) this)
    -- bound shifted series by 16 + pi^2/6
    have hsum_shift : ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1/4)^2 ≤ (16 : ℝ) + Real.pi ^ 2 / 6 := by
      -- split n=0 term
      have h0 : (1 : ℝ) / ((0 : ℝ) + 1/4)^2 = 16 := by norm_num
      have htail : ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1/4)^2 ≤
          (1 : ℝ) / ((0 : ℝ) + 1/4)^2 + ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
        -- compare termwise and add n=0
        have hle : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 1/4)^2 ≤ (1 : ℝ) / (n : ℝ) ^ 2 := by
          intro n
          by_cases h0 : n = 0
          · simp [h0]
          · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
            have hle : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1/4)^2 := by nlinarith
            exact one_div_le_one_div_of_le hle
        exact hsum.norm.tsum_le_tsum hle (hasSum_zeta_two.summable)
      have hsum_zeta : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = Real.pi ^ 2 / 6 := by
        simpa using hasSum_zeta_two.tsum_eq
      nlinarith [htail, h0, hsum_zeta]
    exact le_trans (le_trans hnorm hsum_le) hsum_shift
  -- finish bound
  have hpi : (Real.pi : ℝ) < 3.15 := Real.pi_lt_d2
  have hpi2 : Real.pi ^ 2 / 6 < (9.9225 : ℝ) / 6 := by
    have : Real.pi ^ 2 < (3.15:ℝ)^2 := by nlinarith [hpi]
    nlinarith
  have hconst : Real.pi * (16 + Real.pi ^ 2 / 6) ≤ (56 : ℝ) := by
    nlinarith [hpi, hpi2]
  have h1 : |deriv Q3.a x| ≤ Real.pi * ‖trigamma z‖ := by
    -- |pi * im| ≤ pi * norm
    have : |(trigamma z).im| ≤ ‖trigamma z‖ := by simpa using (Complex.abs_im_le_norm (trigamma z))
    nlinarith [hderiv, this]
  exact le_trans (le_trans h1 (mul_le_mul_of_nonneg_left htrig (by positivity))) hconst

/-- Global Lipschitz bound for `a`. -/
private lemma a_lipschitz (x y : ℝ) : |Q3.a x - Q3.a y| ≤ (56 : ℝ) * |x - y| := by
  classical
  -- reduce to x ≤ y
  wlog hxy : x ≤ y := by
    have h := this y x (by linarith)
    simpa [abs_sub_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  -- apply mean value theorem on segment
  have hdiff : DifferentiableOn ℝ Q3.a (Set.Icc x y) := by
    intro z hz
    have : DifferentiableAt ℝ Q3.a z := by
      -- digamma is analytic on Re>0, so a is differentiable everywhere
      simpa using (Q3.a_star_continuous.differentiableAt)
    exact this.differentiableWithinAt
  have hderiv : ∀ z ∈ Set.Icc x y, |deriv Q3.a z| ≤ (56 : ℝ) := by
    intro z hz
    simpa using a_deriv_bound z
  have hseg := norm_image_sub_le_of_norm_deriv_le_segment hdiff hderiv y (by simp [hxy])
  simpa [Real.norm_eq_abs] using hseg

/-- Lipschitz bound for `g = a * w` at the critical scale. -/
private lemma g_lipschitz (x y : ℝ) (hx : |x| ≤ B_support) (hy : |y| ≤ B_support) :
    |g B_min t_critical x - g B_min t_critical y| ≤
      (56 : ℝ + (7 : ℝ) * (53 / 10 : ℝ)) * |x - y| := by
  -- use |a w - a w| ≤ |a-a|*|w| + |w-w|*|a|
  have hwa : ∀ z, |w B_min t_critical z| ≤ 1 := by
    intro z
    have h0 : 0 ≤ max 0 (1 - |z| / B_min) := by exact le_max_left _ _
    have h1 : max 0 (1 - |z| / B_min) ≤ 1 := by
      have : 1 - |z| / B_min ≤ 1 := by linarith
      exact max_le_iff.mpr ⟨by linarith, this⟩
    have hga : 0 ≤ Real.exp (-c_crit * z^2) := Real.exp_nonneg _
    have hga1 : Real.exp (-c_crit * z^2) ≤ 1 := by
      have : -c_crit * z^2 ≤ 0 := by nlinarith [c_crit_pos]
      exact Real.exp_le_one_iff.mpr this
    have hprod : |max 0 (1 - |z| / B_min) * Real.exp (-c_crit * z^2)| ≤ 1 := by
      have hnonneg : 0 ≤ max 0 (1 - |z| / B_min) * Real.exp (-c_crit * z^2) := by
        exact mul_nonneg h0 hga
      have hle : max 0 (1 - |z| / B_min) * Real.exp (-c_crit * z^2) ≤ 1 := by
        have := mul_le_mul h1 hga1 h0 hga
        nlinarith
      simpa [abs_of_nonneg hnonneg] using hle
    simpa [w, c_crit, t_critical, pow_two, mul_comm, mul_left_comm, mul_assoc] using hprod
  have h1 := a_lipschitz x y
  have h2 := w_lipschitz x y
  calc
    |g B_min t_critical x - g B_min t_critical y|
        = |Q3.a x * w B_min t_critical x - Q3.a y * w B_min t_critical y| := by simp [g]
    _ ≤ |Q3.a x - Q3.a y| * |w B_min t_critical x| +
        |w B_min t_critical x - w B_min t_critical y| * |Q3.a y| := by
          nlinarith [abs_mul, abs_sub_le_iff]
    _ ≤ (56 : ℝ) * |x - y| * 1 + (53 / 10 : ℝ) * |x - y| * (7 : ℝ) := by
          nlinarith [h1, h2, hwa x, a_abs_bound_support x hx, a_abs_bound_support y hy]
    _ = (56 : ℝ + (7 : ℝ) * (53 / 10 : ℝ)) * |x - y| := by ring

private lemma abs_le_half_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (-1/2 : ℝ) (1/2)) :
    |x| ≤ (1/2 : ℝ) := by
  refine abs_le.mpr ?_
  constructor <;> linarith [hx.1, hx.2]

private lemma abs_add_le_B_support {x : ℝ} (hx : x ∈ Set.Icc (-1/2 : ℝ) (1/2))
    {m : ℤ} (hm : m ∈ Finset.Icc (-3 : ℤ) 3) :
    |x + m| ≤ B_support := by
  have hxabs : |x| ≤ (1/2 : ℝ) := abs_le_half_of_mem_Icc hx
  have hm' : (-3 : ℤ) ≤ m ∧ m ≤ 3 := by
    simpa [Finset.mem_Icc] using hm
  have hmabs : |(m : ℝ)| ≤ (3 : ℝ) := by
    have hmlo : (-(3 : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hm'.1
    have hmhi : (m : ℝ) ≤ (3 : ℝ) := by exact_mod_cast hm'.2
    exact abs_le.mpr ⟨hmlo, hmhi⟩
  have htri : |x + (m : ℝ)| ≤ |x| + |(m : ℝ)| := by
    simpa [Real.norm_eq_abs, add_comm, add_left_comm, add_assoc] using
      (norm_add_le (x) (m : ℝ))
  have hsum : |x + (m : ℝ)| ≤ (1/2 : ℝ) + (3 : ℝ) := by
    nlinarith [htri, hxabs, hmabs]
  -- B_support = B_min + 1/2 = 3.5
  simpa [B_support, B_min, add_comm, add_left_comm, add_assoc] using hsum

private lemma abs_add_ge_B_min_of_not_mem {x : ℝ} (hx : x ∈ Set.Icc (-1/2 : ℝ) (1/2))
    {m : ℤ} (hm : m ∉ Finset.Icc (-3 : ℤ) 3) :
    (B_min : ℝ) ≤ |x + m| := by
  have hxabs : |x| ≤ (1/2 : ℝ) := abs_le_half_of_mem_Icc hx
  have hm' : m ≤ -4 ∨ 4 ≤ m := by
    -- outside [-3,3] for integers
    have hm'' : ¬ (-3 ≤ m ∧ m ≤ 3) := by simpa [Finset.mem_Icc] using hm
    omega
  have hmabs : (4 : ℝ) ≤ |(m : ℝ)| := by
    cases hm' with
    | inl hml =>
        have hm0 : (m : ℝ) ≤ 0 := by nlinarith
        have h4 : (4 : ℝ) ≤ -(m : ℝ) := by nlinarith
        simpa [abs_of_nonpos hm0] using h4
    | inr hmr =>
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := by nlinarith
        have h4 : (4 : ℝ) ≤ (m : ℝ) := by nlinarith
        simpa [abs_of_nonneg hm0] using h4
  have htri : |(m : ℝ)| - |x| ≤ |x + (m : ℝ)| := by
    have h := norm_add_le (x + (m : ℝ)) (-x)
    -- |(x+m) + (-x)| = |m|
    have h' : |(m : ℝ)| ≤ |x + (m : ℝ)| + |x| := by
      simpa [Real.norm_eq_abs, add_assoc, add_comm, add_left_comm] using h
    linarith
  have hB : (B_min : ℝ) = 3 := by norm_num [B_min]
  have hbound : (3 : ℝ) ≤ |(m : ℝ)| - |x| := by nlinarith [hmabs, hxabs]
  have : (3 : ℝ) ≤ |x + (m : ℝ)| := by nlinarith [htri, hbound]
  simpa [hB] using this

private lemma P_A_eq_sum_Icc (t : ℝ) (x : ℝ)
    (hx : x ∈ Set.Icc (-1/2 : ℝ) (1/2)) :
    P_A B_min t x =
      2 * Real.pi * ∑ m ∈ Finset.Icc (-3 : ℤ) 3, g B_min t (x + (m : ℝ)) := by
  unfold P_A
  congr 1
  refine tsum_eq_sum ?_
  intro m hm
  have hlarge : (B_min : ℝ) ≤ |x + (m : ℝ)| :=
    abs_add_ge_B_min_of_not_mem (x := x) hx hm
  exact g_support_B_min_of_t (t := t) (ξ := x + (m : ℝ)) hlarge

/-- Lipschitz certificate on the fundamental domain (analytic). -/
theorem P_A_Lipschitz_on_Icc_analytic :
    ∀ x y,
      x ∈ Set.Icc (-1/2 : ℝ) (1/2) →
      y ∈ Set.Icc (-1/2 : ℝ) (1/2) →
      |P_A B_min t_critical x - P_A B_min t_critical y| ≤
        floor_cert_L_ub * |x - y| := by
  intro x y hx hy
  -- On [-1/2,1/2], only m ∈ [-3,3] contribute
  have hsum :
      |P_A B_min t_critical x - P_A B_min t_critical y| ≤
        2 * Real.pi * (7 : ℝ) *
          (56 : ℝ + (7 : ℝ) * (53 / 10 : ℝ)) * |x - y| := by
    have hxsum : P_A B_min t_critical x =
        2 * Real.pi * ∑ m ∈ Finset.Icc (-3 : ℤ) 3, g B_min t_critical (x + (m : ℝ)) :=
      P_A_eq_sum_Icc (t := t_critical) x hx
    have hysum : P_A B_min t_critical y =
        2 * Real.pi * ∑ m ∈ Finset.Icc (-3 : ℤ) 3, g B_min t_critical (y + (m : ℝ)) :=
      P_A_eq_sum_Icc (t := t_critical) y hy
    have hsum' :
        |∑ m ∈ Finset.Icc (-3 : ℤ) 3, (g B_min t_critical (x + (m : ℝ)) -
              g B_min t_critical (y + (m : ℝ)))|
          ≤ ∑ m ∈ Finset.Icc (-3 : ℤ) 3,
              |g B_min t_critical (x + (m : ℝ)) - g B_min t_critical (y + (m : ℝ))| := by
      simpa [Real.norm_eq_abs] using
        (norm_sum_le (s := Finset.Icc (-3 : ℤ) 3)
          (f := fun m => g B_min t_critical (x + (m : ℝ)) - g B_min t_critical (y + (m : ℝ))))
    have hsum'' :
        ∑ m ∈ Finset.Icc (-3 : ℤ) 3,
            |g B_min t_critical (x + (m : ℝ)) - g B_min t_critical (y + (m : ℝ))|
          ≤ ∑ m ∈ Finset.Icc (-3 : ℤ) 3,
              (56 : ℝ + (7 : ℝ) * (53 / 10 : ℝ)) * |x - y| := by
      refine Finset.sum_le_sum ?_
      intro m hm
      have hx' : |x + (m : ℝ)| ≤ B_support := abs_add_le_B_support (x := x) hx (m := m) hm
      have hy' : |y + (m : ℝ)| ≤ B_support := abs_add_le_B_support (x := y) hy (m := m) hm
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (g_lipschitz (x := x + (m : ℝ)) (y := y + (m : ℝ)) hx' hy')
    have hcard : (Finset.Icc (-3 : ℤ) 3).card = 7 := by decide
    have hsum''' :
        ∑ m ∈ Finset.Icc (-3 : ℤ) 3,
            (56 : ℝ + (7 : ℝ) * (53 / 10 : ℝ)) * |x - y|
          = (7 : ℝ) * (56 : ℝ + (7 : ℝ) * (53 / 10 : ℝ)) * |x - y| := by
      -- sum of constant over 7 terms
      simp [hcard, mul_assoc, mul_left_comm, mul_comm]
    -- combine
    have hpi : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
    have : |P_A B_min t_critical x - P_A B_min t_critical y|
        ≤ 2 * Real.pi *
          ((7 : ℝ) * (56 : ℝ + (7 : ℝ) * (53 / 10 : ℝ)) * |x - y|) := by
      -- rewrite and use triangle inequality
      have hdiff :
          P_A B_min t_critical x - P_A B_min t_critical y =
            2 * Real.pi * ∑ m ∈ Finset.Icc (-3 : ℤ) 3,
              (g B_min t_critical (x + (m : ℝ)) - g B_min t_critical (y + (m : ℝ))) := by
        nlinarith [hxsum, hysum]
      -- apply bound
      have hsum_bound :
          |∑ m ∈ Finset.Icc (-3 : ℤ) 3,
              (g B_min t_critical (x + (m : ℝ)) - g B_min t_critical (y + (m : ℝ)))|
            ≤ (7 : ℝ) * (56 : ℝ + (7 : ℝ) * (53 / 10 : ℝ)) * |x - y| := by
        have h1 :
            |∑ m ∈ Finset.Icc (-3 : ℤ) 3,
                (g B_min t_critical (x + (m : ℝ)) - g B_min t_critical (y + (m : ℝ)))|
              ≤ ∑ m ∈ Finset.Icc (-3 : ℤ) 3,
                  (56 : ℝ + (7 : ℝ) * (53 / 10 : ℝ)) * |x - y| := by
          exact le_trans hsum' hsum''
        simpa [hsum'''] using h1
      -- multiply by 2*pi
      nlinarith [hdiff, hsum_bound, hpi]
    -- rearrange to expected form
    nlinarith [this]
  -- numeric bound
  have hL :
      2 * Real.pi * (7 : ℝ) * (56 : ℝ + (7 : ℝ) * (53 / 10 : ℝ)) ≤ floor_cert_L_ub := by
    -- floor_cert_L_ub = 4200
    norm_num [floor_cert_L_ub]
  nlinarith [hsum, hL]

end Q3.Proofs.FloorCert
