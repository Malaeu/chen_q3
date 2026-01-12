import Mathlib
import Q3.Basic.Defs
import Q3.Axioms
import Q3.DigammaRemainder

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set
open Q3

set_option maxHeartbeats 400000

noncomputable section

def B_min : ℝ := 3
def t_sym : ℝ := 3 / 50

def w (B t xi : ℝ) : ℝ :=
  max 0 (1 - |xi| / B) * Real.exp (-4 * Real.pi^2 * t * xi^2)

lemma w_half_eq :
    w B_min t_sym (1 / 2) = (5 / 6 : ℝ) * Real.exp (-3 * Real.pi^2 / 50) := by
  have hnonneg : (0 : ℝ) ≤ 1 - (2⁻¹ : ℝ) / 3 := by norm_num
  simp [w, B_min, t_sym, pow_two, mul_comm, mul_left_comm, mul_assoc]
  rw [max_eq_right hnonneg]
  ring_nf

lemma w_one_eq :
    w B_min t_sym 1 = (2 / 3 : ℝ) * Real.exp (-12 * Real.pi^2 / 50) := by
  have hnonneg : (0 : ℝ) ≤ 1 - (3⁻¹ : ℝ) := by norm_num
  simp [w, B_min, t_sym, pow_two, mul_comm, mul_left_comm, mul_assoc]
  rw [max_eq_right hnonneg]
  ring_nf

lemma w_two_eq :
    w B_min t_sym 2 = (1 / 3 : ℝ) * Real.exp (-48 * Real.pi^2 / 50) := by
  have hnonneg : (0 : ℝ) ≤ 1 - (2 : ℝ) / 3 := by norm_num
  simp [w, B_min, t_sym, pow_two, mul_comm, mul_left_comm, mul_assoc]
  rw [max_eq_right hnonneg]
  ring_nf

lemma exp_bound_half :
    Real.exp (-3 * Real.pi^2 / 50) ≥ (27 / 50 : ℝ) := by
  suffices h_exp : 3 * Real.pi ^ 2 / 50 ≤ Real.log (50 / 27) by
    exact le_trans (by norm_num [Real.exp_neg, Real.exp_log])
      (Real.exp_le_exp.mpr (show -3 * Real.pi ^ 2 / 50 ≥ -Real.log (50 / 27) by
        linarith))
  have h_pi_approx : Real.pi < 3.15 := by
    exact Real.pi_lt_d2
  have h_log_approx : Real.log (50 / 27) > 0.6 := by
    norm_num [Real.log_lt_log]
    rw [div_lt_iff₀'] <;> norm_num [← Real.log_rpow, Real.lt_log_iff_exp_lt]
    have := Real.exp_one_lt_d9.le
    norm_num1 at *
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [Real.add_one_le_exp 1]
  norm_num at *
  nlinarith [Real.pi_gt_three]

theorem w_half_bound : w B_min t_sym (1 / 2) ≥ (9 / 20 : ℝ) := by
  have h_exp : Real.exp (-3 * Real.pi^2 / 50) ≥ (27 / 50 : ℝ) := exp_bound_half
  have hpos : (0 : ℝ) ≤ (5 / 6 : ℝ) := by norm_num
  calc
    w B_min t_sym (1 / 2)
        = (5 / 6 : ℝ) * Real.exp (-3 * Real.pi^2 / 50) := w_half_eq
    _ ≥ (5 / 6 : ℝ) * (27 / 50 : ℝ) := by
      exact mul_le_mul_of_nonneg_left h_exp hpos
    _ = (9 / 20 : ℝ) := by norm_num

lemma log_one_add_le (u : ℝ) (hu : 0 ≤ u) : Real.log (1 + u) ≤ u := by
  have hpos : 0 < 1 + u := by linarith
  have hle : 1 + u ≤ Real.exp u := by
    simpa [add_comm] using (Real.add_one_le_exp u)
  exact (Real.log_le_iff_le_exp hpos).2 hle

lemma log_abs_z_le (xi : ℝ) (hxi : 0 < xi) :
    Real.log ‖(1 / 4 : ℂ) + Complex.I * Real.pi * xi‖ ≤
      Real.log (Real.pi * xi) + (1 / (32 * Real.pi^2 * xi^2) : ℝ) := by
  set z : ℂ := (1 / 4 : ℂ) + Complex.I * Real.pi * xi
  set u : ℝ := 1 / (16 * Real.pi^2 * xi^2)
  have hxi_ne : xi ≠ 0 := by linarith
  have hpi_pos : 0 < (Real.pi : ℝ) := Real.pi_pos
  have hpi_ne : (Real.pi : ℝ) ≠ 0 := ne_of_gt hpi_pos
  have hquarter : (4⁻¹ : ℝ)^2 = (4^2)⁻¹ := by norm_num
  have hpos_pi_xi : 0 < Real.pi * xi := mul_pos hpi_pos hxi
  have hs_nonneg : 0 ≤ (Real.pi * xi)^2 + (4^2)⁻¹ := by
    simpa [hquarter] using (by nlinarith : 0 ≤ (Real.pi * xi)^2 + (4⁻¹ : ℝ)^2)
  have h_abs' :
      ‖z‖ =
        Real.sqrt (4⁻¹ * 4⁻¹ + xi * (xi * (Real.pi * Real.pi))) := by
    simp [Complex.norm_def, Complex.normSq_apply, z, pow_two, mul_comm, mul_left_comm, mul_assoc]
  have h_abs :
      ‖z‖ = Real.sqrt ((Real.pi * xi)^2 + (4^2)⁻¹) := by
    have h_inside :
        4⁻¹ * 4⁻¹ + xi * (xi * (Real.pi * Real.pi)) =
          (Real.pi * xi)^2 + (4^2)⁻¹ := by
      ring
    simpa [h_inside] using h_abs'
  have hlog_abs :
      Real.log ‖z‖ =
        (1 / 2 : ℝ) * Real.log ((Real.pi * xi)^2 + (4^2)⁻¹) := by
    calc
      Real.log ‖z‖ = Real.log (Real.sqrt ((Real.pi * xi)^2 + (4^2)⁻¹)) := by
        simpa [h_abs]
      _ = Real.log ((Real.pi * xi)^2 + (4^2)⁻¹) / 2 := by
        simpa using (Real.log_sqrt hs_nonneg)
      _ = (1 / 2 : ℝ) * Real.log ((Real.pi * xi)^2 + (4^2)⁻¹) := by
        ring
  have hpi_sq_ne : (Real.pi^2 : ℝ) ≠ 0 := by
    exact pow_ne_zero 2 hpi_ne
  have hxi_sq_ne : (xi^2 : ℝ) ≠ 0 := by
    exact pow_ne_zero 2 hxi_ne
  have hmul : (Real.pi * xi)^2 * u = (4^2)⁻¹ := by
    calc
      (Real.pi * xi)^2 * u =
          (Real.pi^2 * xi^2) * (1 / (16 * Real.pi^2 * xi^2)) := by
        simp [u, pow_two, mul_comm, mul_left_comm, mul_assoc]
      _ = (1 / 16 : ℝ) := by
        field_simp [hpi_sq_ne, hxi_sq_ne]
      _ = (4^2)⁻¹ := by norm_num
  have hs_eq :
      (Real.pi * xi)^2 + (4^2)⁻¹ =
        (Real.pi * xi)^2 * (1 + u) := by
    calc
      (Real.pi * xi)^2 + (4^2)⁻¹ =
          (Real.pi * xi)^2 + (Real.pi * xi)^2 * u := by
        simpa [hmul]
      _ = (Real.pi * xi)^2 * (1 + u) := by ring
  have hpos_sq : 0 < (Real.pi * xi)^2 := by nlinarith [hpos_pi_xi]
  have hu_nonneg : 0 ≤ u := by
    have hpos : 0 < (16 * Real.pi^2 * xi^2 : ℝ) := by nlinarith [Real.pi_pos, hxi]
    nlinarith [u]
  have hpos_one_u : 0 < 1 + u := by nlinarith [hu_nonneg]
  have hlog_split :
      Real.log ((Real.pi * xi)^2 + (4^2)⁻¹) =
        Real.log ((Real.pi * xi)^2) + Real.log (1 + u) := by
    calc
      Real.log ((Real.pi * xi)^2 + (4^2)⁻¹)
          = Real.log ((Real.pi * xi)^2 * (1 + u)) := by simpa [hs_eq]
      _ = Real.log ((Real.pi * xi)^2) + Real.log (1 + u) := by
        simpa using (Real.log_mul hpos_sq.ne' hpos_one_u.ne')
  have hlog_sq :
      Real.log ((Real.pi * xi)^2) = 2 * Real.log (Real.pi * xi) := by
    have h := Real.log_mul hpos_pi_xi.ne' hpos_pi_xi.ne'
    simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc] using h
  have hlog_abs' :
      Real.log ‖z‖ =
        Real.log (Real.pi * xi) + (1 / 2 : ℝ) * Real.log (1 + u) := by
    calc
      Real.log ‖z‖ =
          (1 / 2 : ℝ) * (Real.log ((Real.pi * xi)^2) + Real.log (1 + u)) := by
        simpa [hlog_abs, hlog_split]
      _ = (1 / 2 : ℝ) * (2 * Real.log (Real.pi * xi)) +
            (1 / 2 : ℝ) * Real.log (1 + u) := by
        simp [hlog_sq, mul_add, mul_comm, mul_left_comm, mul_assoc]
      _ = Real.log (Real.pi * xi) + (1 / 2 : ℝ) * Real.log (1 + u) := by ring
  have hlog_u : Real.log (1 + u) ≤ u := log_one_add_le u hu_nonneg
  have hbound : Real.log ‖z‖ ≤ Real.log (Real.pi * xi) + (1 / 2 : ℝ) * u := by
    nlinarith [hlog_abs', hlog_u]
  have hconst :
      (1 / 2 : ℝ) * u = (1 / (32 * Real.pi^2 * xi^2) : ℝ) := by
    calc
      (1 / 2 : ℝ) * u =
          (1 / 2 : ℝ) * (1 / (16 * Real.pi^2 * xi^2)) := by
        simp [u]
      _ = (1 / (32 * Real.pi^2 * xi^2) : ℝ) := by
        field_simp [hpi_sq_ne, hxi_sq_ne]
        ring
  have hbound' :
      Real.log ‖z‖ ≤ Real.log (Real.pi * xi) + (1 / (32 * Real.pi^2 * xi^2) : ℝ) := by
    nlinarith [hbound, hconst]
  exact hbound'

lemma a_lower_bound_from_remainder (xi : ℝ) (hxi : 0 < xi) :
    a xi ≥
      Real.log Real.pi -
        Real.log ‖(1 / 4 : ℂ) + Complex.I * Real.pi * xi‖ +
        (1 / 24 : ℝ) * (1 / ‖(1 / 4 : ℂ) + Complex.I * Real.pi * xi‖^2) := by
  set z : ℂ := (1 / 4 : ℂ) + Complex.I * Real.pi * xi
  have hz : (1 / 4 : ℝ) ≤ z.re := by simp [z]
  have hrem := re_digamma_remainder_bound z hz
  have hrem' :
      |(Q3.digamma z).re - (Real.log ‖z‖ - z.re / (2 * ‖z‖^2))| ≤
        1 / (12 * ‖z‖^2) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hrem
  have hle :
      (Q3.digamma z).re ≤
        Real.log ‖z‖ - z.re / (2 * ‖z‖^2) + 1 / (12 * ‖z‖^2) := by
    have hle' := (abs_sub_le_iff.mp hrem').1
    linarith
  have hconst :
      z.re / (2 * ‖z‖^2) - 1 / (12 * ‖z‖^2) =
        (1 / 24 : ℝ) * (1 / ‖z‖^2) := by
    simp [z, mul_comm, mul_left_comm, mul_assoc]
    ring
  have hmain :
      a xi ≥ Real.log Real.pi - Real.log ‖z‖ + (1 / 24 : ℝ) * (1 / ‖z‖^2) := by
    have hdef : a xi = Real.log Real.pi - (Q3.digamma z).re := by
      simp [a, z, sub_eq_add_neg]
    nlinarith [hdef, hle, hconst]
  simpa [z] using hmain

lemma norm_z_sq (xi : ℝ) :
    ‖(1 / 4 : ℂ) + Complex.I * Real.pi * xi‖^2 =
      (Real.pi * xi)^2 + (1 / 4 : ℝ)^2 := by
  calc
    ‖(1 / 4 : ℂ) + Complex.I * Real.pi * xi‖^2 =
        Complex.normSq ((1 / 4 : ℂ) + Complex.I * Real.pi * xi) := by
          simpa using (Complex.sq_norm ((1 / 4 : ℂ) + Complex.I * Real.pi * xi))
    _ = (1 / 4 : ℝ) * (1 / 4 : ℝ) + (Real.pi * xi) * (Real.pi * xi) := by
          simp [Complex.normSq_apply, pow_two, mul_comm, mul_left_comm, mul_assoc]
    _ = (Real.pi * xi)^2 + (1 / 4 : ℝ)^2 := by ring

lemma a_lower_bound_from_stieltjes (xi : ℝ) :
    a xi ≥
      Real.log Real.pi -
        Real.log ‖(1 / 4 : ℂ) + Complex.I * Real.pi * xi‖ -
        (1 / 8 : ℝ) * (1 / ‖(1 / 4 : ℂ) + Complex.I * Real.pi * xi‖^2) := by
  set z : ℂ := (1 / 4 : ℂ) + Complex.I * Real.pi * xi
  have hz : 0 < z.re := by simp [z]
  have hrem := re_digamma_remainder_bound_stieltjes z hz
  have hrem' :
      |(Q3.digamma z).re - (Real.log ‖z‖ - z.re / (2 * ‖z‖^2))| ≤
        1 / (4 * ‖z‖^2) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hrem
  have hle :
      (Q3.digamma z).re ≤
        Real.log ‖z‖ - z.re / (2 * ‖z‖^2) + 1 / (4 * ‖z‖^2) := by
    have hle' := (abs_sub_le_iff.mp hrem').1
    linarith
  have hconst :
      z.re / (2 * ‖z‖^2) - 1 / (4 * ‖z‖^2) =
        (-1 / 8 : ℝ) * (1 / ‖z‖^2) := by
    simp [z, mul_comm, mul_left_comm, mul_assoc]
    ring
  have hmain :
      a xi ≥
        Real.log Real.pi - Real.log ‖z‖ - (1 / 8 : ℝ) * (1 / ‖z‖^2) := by
    have hdef : a xi = Real.log Real.pi - (Q3.digamma z).re := by
      simp [a, z, sub_eq_add_neg]
    nlinarith [hdef, hle, hconst]
  simpa [z] using hmain

lemma a_ge_neg_log_xi (xi : ℝ) (hxi : (1 / 2 : ℝ) ≤ xi) :
    a xi ≥ -Real.log xi := by
  have hxi_pos : 0 < xi := by linarith
  set z : ℂ := (1 / 4 : ℂ) + Complex.I * Real.pi * xi
  have hbase := a_lower_bound_from_remainder xi hxi_pos
  have hlog_le := log_abs_z_le xi hxi_pos
  have hbound :
      a xi ≥
        Real.log Real.pi - Real.log (Real.pi * xi) -
          (1 / (32 * Real.pi^2 * xi^2) : ℝ) +
          (1 / 24 : ℝ) * (1 / ‖z‖^2) := by
    nlinarith [hbase, hlog_le]
  have hlog_pi :
      Real.log Real.pi - Real.log (Real.pi * xi) = -Real.log xi := by
    have hpi_pos : 0 < (Real.pi : ℝ) := Real.pi_pos
    have hpi_xi_pos : 0 < Real.pi * xi := mul_pos Real.pi_pos hxi_pos
    have hpi_ne : (Real.pi : ℝ) ≠ 0 := ne_of_gt hpi_pos
    have hpi_xi_ne : (Real.pi * xi : ℝ) ≠ 0 := ne_of_gt hpi_xi_pos
    have hlog_div := Real.log_div hpi_ne hpi_xi_ne
    have hxi_ne : xi ≠ 0 := by linarith
    have hratio : Real.pi / (Real.pi * xi) = 1 / xi := by
      field_simp [Real.pi_ne_zero, hxi_ne]
    calc
      Real.log Real.pi - Real.log (Real.pi * xi) =
          Real.log (Real.pi / (Real.pi * xi)) := by
        symm
        simpa using hlog_div
      _ = Real.log (1 / xi) := by simp [hratio]
      _ = -Real.log xi := by
        simpa [one_div] using (Real.log_inv xi)
  have hden_le : 24 * ‖z‖^2 ≤ 32 * Real.pi^2 * xi^2 := by
    have hnorm_sq :
        ‖z‖^2 = (Real.pi * xi)^2 + (1 / 4 : ℝ)^2 := by
      calc
        ‖z‖^2 = Complex.normSq z := by
          simpa using (Complex.sq_norm z)
        _ = z.re * z.re + z.im * z.im := by
          simp [Complex.normSq_apply, pow_two]
        _ = (1 / 4 : ℝ)^2 + (Real.pi * xi)^2 := by
          simp [z, pow_two, mul_comm, mul_left_comm, mul_assoc]
        _ = (Real.pi * xi)^2 + (1 / 4 : ℝ)^2 := by ring
    have hpi : (3 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
    have hpi_sq : (9 : ℝ) ≤ Real.pi^2 := by nlinarith [hpi]
    have hxi_sq : (1 / 4 : ℝ) ≤ xi^2 := by nlinarith [hxi]
    have hbig : (3 / 2 : ℝ) ≤ 8 * Real.pi^2 * xi^2 := by
      nlinarith [hpi_sq, hxi_sq]
    have hpi_xi_sq : (Real.pi * xi)^2 = Real.pi^2 * xi^2 := by
      ring
    calc
      24 * ‖z‖^2 = 24 * ((Real.pi * xi)^2 + (1 / 4 : ℝ)^2) := by
        simpa [hnorm_sq]
      _ = 24 * (Real.pi^2 * xi^2) + (3 / 2 : ℝ) := by
        calc
          24 * ((Real.pi * xi)^2 + (1 / 4 : ℝ)^2) =
              24 * (Real.pi * xi)^2 + 24 * (1 / 4 : ℝ)^2 := by ring
          _ = 24 * (Real.pi^2 * xi^2) + 24 * (1 / 4 : ℝ)^2 := by
            simp [hpi_xi_sq]
          _ = 24 * (Real.pi^2 * xi^2) + (3 / 2 : ℝ) := by norm_num
      _ ≤ 24 * (Real.pi^2 * xi^2) + 8 * Real.pi^2 * xi^2 := by
        nlinarith [hbig]
      _ = 32 * Real.pi^2 * xi^2 := by ring
  have hpos : 0 < (24 * ‖z‖^2 : ℝ) := by
    have hnorm_sq :
        ‖z‖^2 = (Real.pi * xi)^2 + (1 / 4 : ℝ)^2 := by
      calc
        ‖z‖^2 = Complex.normSq z := by
          simpa using (Complex.sq_norm z)
        _ = z.re * z.re + z.im * z.im := by
          simp [Complex.normSq_apply, pow_two]
        _ = (1 / 4 : ℝ)^2 + (Real.pi * xi)^2 := by
          simp [z, pow_two, mul_comm, mul_left_comm, mul_assoc]
        _ = (Real.pi * xi)^2 + (1 / 4 : ℝ)^2 := by ring
    nlinarith [hnorm_sq, Real.pi_pos, hxi_pos]
  have hfrac :
      (1 / (32 * Real.pi^2 * xi^2) : ℝ) ≤ (1 / (24 * ‖z‖^2) : ℝ) := by
    exact one_div_le_one_div_of_le hpos hden_le
  set t : ℝ :=
    -(1 / (32 * Real.pi^2 * xi^2) : ℝ) + (1 / 24 : ℝ) * (1 / ‖z‖^2)
  have hbound' : a xi ≥ -Real.log xi + t := by
    dsimp [t]
    nlinarith [hbound, hlog_pi]
  have hnonneg : 0 ≤ t := by
    dsimp [t]
    have h' :
        0 ≤ (1 / (24 * ‖z‖^2) : ℝ) -
            (1 / (32 * Real.pi^2 * xi^2) : ℝ) := by
      exact sub_nonneg.mpr hfrac
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using h'
  have hfinal : a xi ≥ -Real.log xi := by
    linarith [hbound', hnonneg]
  exact hfinal

lemma log_three_halves_le_421_over_960 :
    Real.log (3 / 2 : ℝ) ≤ (421 / 960 : ℝ) := by
  have hx : |(-(1 / 2 : ℝ))| < (1 : ℝ) := by norm_num
  have h :=
    Real.abs_log_sub_add_sum_range_le (x := -(1 / 2 : ℝ)) hx 5
  have hconst : (2^6 : ℝ)⁻¹ / (1 + -(2 : ℝ)⁻¹) = (1 / 32 : ℝ) := by
    norm_num
  have h1 :
      |(∑ i ∈ Finset.range 5, (-(1 / 2 : ℝ))^(i + 1) / (i + 1)) +
          Real.log (1 + (2 : ℝ)⁻¹)| ≤ (1 / 32 : ℝ) := by
    simpa [sub_eq_add_neg, hconst] using h
  have h' :
      |(∑ i ∈ Finset.range 5, (-(1 / 2 : ℝ))^(i + 1) / (i + 1)) +
          Real.log (3 / 2 : ℝ)| ≤ (1 / 32 : ℝ) := by
    have hlog : (1 + (2 : ℝ)⁻¹) = (3 / 2 : ℝ) := by norm_num
    simpa [hlog] using h1
  have hle := (abs_le.mp h').2
  have hsum :
      (∑ i ∈ Finset.range 5, (-(1 / 2 : ℝ))^(i + 1) / (i + 1)) =
        (-391 / 960 : ℝ) := by
    norm_num
  nlinarith [hle, hsum]

lemma log_three_halves_lt_nine_twenty :
    Real.log (3 / 2 : ℝ) < (9 / 20 : ℝ) := by
  have hle : Real.log (3 / 2 : ℝ) ≤ (421 / 960 : ℝ) :=
    log_three_halves_le_421_over_960
  have hlt : (421 / 960 : ℝ) < (9 / 20 : ℝ) := by norm_num
  exact lt_of_le_of_lt hle hlt

lemma log_five_halves_lt_one : Real.log (5 / 2 : ℝ) < (1 : ℝ) := by
  have hpos : 0 < (5 / 2 : ℝ) := by norm_num
  have hlt : (5 / 2 : ℝ) < Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    have h' : (5 / 2 : ℝ) < (2.7182818283 : ℝ) := by norm_num
    exact lt_of_lt_of_le h' (le_of_lt h)
  exact (Real.log_lt_iff_lt_exp hpos).2 hlt

lemma log_two_ge_seventeen_over_twenty_five :
    (17 / 25 : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  have h' : (17 / 25 : ℝ) ≤ (0.6931471803 : ℝ) := by norm_num
  exact le_trans h' (le_of_lt h)

lemma log_two_ge_69_over_100 :
    (69 / 100 : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  have h' : (69 / 100 : ℝ) ≤ (0.6931471803 : ℝ) := by norm_num
  exact le_trans h' (le_of_lt h)

theorem a_half_bound : a (1 / 2 : ℝ) ≥ (5 / 8 : ℝ) := by
  have hxi : 0 < (1 / 2 : ℝ) := by norm_num
  set z : ℂ := (1 / 4 : ℂ) + Complex.I * Real.pi * (1 / 2 : ℝ)
  have hbase :
      a (1 / 2 : ℝ) ≥
        Real.log Real.pi - Real.log ‖z‖ - (1 / 8 : ℝ) * (1 / ‖z‖^2) := by
    simpa [z] using (a_lower_bound_from_stieltjes (1 / 2 : ℝ))
  have hlog :
      Real.log ‖z‖ ≤
        Real.log (Real.pi * (1 / 2 : ℝ)) +
          (1 / (32 * Real.pi^2 * (1 / 2 : ℝ)^2) : ℝ) := by
    have h := log_abs_z_le (1 / 2 : ℝ) hxi
    simpa [z] using h
  have hlog' :
      -Real.log ‖z‖ ≥
        -Real.log (Real.pi * (1 / 2 : ℝ)) -
          (1 / (32 * Real.pi^2 * (1 / 2 : ℝ)^2) : ℝ) := by
    nlinarith [hlog]
  have hstep :
      a (1 / 2 : ℝ) ≥
        Real.log Real.pi - Real.log (Real.pi * (1 / 2 : ℝ)) -
          (1 / (32 * Real.pi^2 * (1 / 2 : ℝ)^2) : ℝ) -
            (1 / 8 : ℝ) * (1 / ‖z‖^2) := by
    nlinarith [hbase, hlog']
  have hlog_pi :
      Real.log Real.pi - Real.log (Real.pi * (1 / 2 : ℝ)) = Real.log 2 := by
    have hpi_pos : 0 < (Real.pi : ℝ) := Real.pi_pos
    have hpi_ne : (Real.pi : ℝ) ≠ 0 := ne_of_gt hpi_pos
    have hpi_half_ne : (Real.pi * (1 / 2 : ℝ) : ℝ) ≠ 0 := by nlinarith [hpi_pos]
    have hlog_div := Real.log_div hpi_ne hpi_half_ne
    have hratio : Real.pi / (Real.pi * (2⁻¹ : ℝ)) = (2 : ℝ) := by
      field_simp [Real.pi_ne_zero]
    calc
      Real.log Real.pi - Real.log (Real.pi * (1 / 2 : ℝ)) =
          Real.log (Real.pi / (Real.pi * (1 / 2 : ℝ))) := by
            symm
            simpa using hlog_div
      _ = Real.log 2 := by simp [hratio, one_div]
  have hpi2 : (9 : ℝ) ≤ Real.pi^2 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith [hpi]
  have hpi_term :
      (1 / (32 * Real.pi^2 * (1 / 2 : ℝ)^2) : ℝ) ≤ (1 / 72 : ℝ) := by
    have hpos : 0 < (72 : ℝ) := by norm_num
    have hle : (72 : ℝ) ≤ 32 * Real.pi^2 * (1 / 2 : ℝ)^2 := by
      nlinarith [hpi2]
    exact one_div_le_one_div_of_le hpos hle
  have hnorm_sq :
      (5 / 2 : ℝ) ≤ ‖z‖^2 := by
    have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
    have hpi2 : (3.1415 : ℝ)^2 ≤ Real.pi^2 := by nlinarith [hpi]
    have hnorm : ‖z‖^2 = (Real.pi * (1 / 2 : ℝ))^2 + (1 / 4 : ℝ)^2 := by
      simpa [z] using (norm_z_sq (1 / 2 : ℝ))
    have hpi_half : (3.1415 / 2 : ℝ)^2 ≤ (Real.pi * (1 / 2 : ℝ))^2 := by
      nlinarith [hpi2]
    have hconst : (5 / 2 : ℝ) ≤ (3.1415 / 2 : ℝ)^2 + (1 / 4 : ℝ)^2 := by
      norm_num
    calc
      (5 / 2 : ℝ) ≤ (3.1415 / 2 : ℝ)^2 + (1 / 4 : ℝ)^2 := hconst
      _ ≤ (Real.pi * (1 / 2 : ℝ))^2 + (1 / 4 : ℝ)^2 := by nlinarith [hpi_half]
      _ = ‖z‖^2 := hnorm.symm
  have hnorm_term : (1 / 8 : ℝ) * (1 / ‖z‖^2) ≤ (1 / 20 : ℝ) := by
    have hpos : 0 < (5 / 2 : ℝ) := by nlinarith
    have hle : (5 / 2 : ℝ) ≤ ‖z‖^2 := hnorm_sq
    have hdiv := one_div_le_one_div_of_le hpos hle
    have hdiv' : (1 / ‖z‖^2 : ℝ) ≤ (2 / 5 : ℝ) := by
      simpa using hdiv
    nlinarith [hdiv']
  have hlog2 : (69 / 100 : ℝ) ≤ Real.log 2 := log_two_ge_69_over_100
  have hfinal :
      a (1 / 2 : ℝ) ≥
        (69 / 100 : ℝ) - (1 / 72 : ℝ) - (1 / 20 : ℝ) := by
    nlinarith [hstep, hlog_pi, hlog2, hpi_term, hnorm_term]
  have hconst : (69 / 100 : ℝ) - (1 / 72 : ℝ) - (1 / 20 : ℝ) ≥ (5 / 8 : ℝ) := by
    norm_num
  nlinarith [hfinal, hconst]

theorem a_three_half_bound : a (3 / 2 : ℝ) ≥ (-1 / 2 : ℝ) := by
  have hxi : 0 < (3 / 2 : ℝ) := by norm_num
  set z : ℂ := (1 / 4 : ℂ) + Complex.I * Real.pi * (3 / 2 : ℝ)
  have hbase :
      a (3 / 2 : ℝ) ≥
        Real.log Real.pi - Real.log ‖z‖ - (1 / 8 : ℝ) * (1 / ‖z‖^2) := by
    simpa [z] using (a_lower_bound_from_stieltjes (3 / 2 : ℝ))
  have hlog :
      Real.log ‖z‖ ≤
        Real.log (Real.pi * (3 / 2 : ℝ)) +
          (1 / (32 * Real.pi^2 * (3 / 2 : ℝ)^2) : ℝ) := by
    have h := log_abs_z_le (3 / 2 : ℝ) hxi
    simpa [z] using h
  have hlog' :
      -Real.log ‖z‖ ≥
        -Real.log (Real.pi * (3 / 2 : ℝ)) -
          (1 / (32 * Real.pi^2 * (3 / 2 : ℝ)^2) : ℝ) := by
    nlinarith [hlog]
  have hstep :
      a (3 / 2 : ℝ) ≥
        -Real.log (3 / 2 : ℝ) - (1 / (32 * Real.pi^2 * (3 / 2 : ℝ)^2) : ℝ) -
          (1 / 8 : ℝ) * (1 / ‖z‖^2) := by
    have hlog_pi :
        Real.log Real.pi - Real.log (Real.pi * (3 / 2 : ℝ)) = -Real.log (3 / 2 : ℝ) := by
      have hpi_pos : 0 < (Real.pi : ℝ) := Real.pi_pos
      have hpi_ne : (Real.pi : ℝ) ≠ 0 := ne_of_gt hpi_pos
      have hpi_mul_ne : (Real.pi * (3 / 2 : ℝ) : ℝ) ≠ 0 := by nlinarith [hpi_pos]
      have hlog_div := Real.log_div hpi_ne hpi_mul_ne
      have hratio : Real.pi / (Real.pi * (3 / 2 : ℝ)) = (1 / (3 / 2 : ℝ)) := by
        field_simp [Real.pi_ne_zero]
      calc
        Real.log Real.pi - Real.log (Real.pi * (3 / 2 : ℝ)) =
            Real.log (Real.pi / (Real.pi * (3 / 2 : ℝ))) := by
              symm
              simpa using hlog_div
        _ = Real.log (1 / (3 / 2 : ℝ)) := by simp [hratio]
        _ = -Real.log (3 / 2 : ℝ) := by
          simpa [one_div] using (Real.log_inv (3 / 2 : ℝ))
    nlinarith [hbase, hlog', hlog_pi]
  have hlog_bound : -Real.log (3 / 2 : ℝ) ≥ (-9 / 20 : ℝ) := by
    have hlt := log_three_halves_lt_nine_twenty
    linarith
  have hpi2 : (9 : ℝ) ≤ Real.pi^2 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith [hpi]
  have hpi_term :
      (1 / (32 * Real.pi^2 * (3 / 2 : ℝ)^2) : ℝ) ≤ (1 / 648 : ℝ) := by
    have hpos : 0 < (648 : ℝ) := by norm_num
    have hle : (648 : ℝ) ≤ 32 * Real.pi^2 * (3 / 2 : ℝ)^2 := by
      nlinarith [hpi2]
    exact one_div_le_one_div_of_le hpos hle
  have hnorm_sq :
      (81 / 4 : ℝ) ≤ ‖z‖^2 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hpi2 : (3 : ℝ)^2 ≤ Real.pi^2 := by nlinarith [hpi]
    have hnorm : ‖z‖^2 = (Real.pi * (3 / 2 : ℝ))^2 + (1 / 4 : ℝ)^2 := by
      simpa [z] using (norm_z_sq (3 / 2 : ℝ))
    have hpi_part : ((3 : ℝ) * (3 / 2 : ℝ))^2 ≤ (Real.pi * (3 / 2 : ℝ))^2 := by
      nlinarith [hpi2]
    have hconst : (81 / 4 : ℝ) ≤ ((3 : ℝ) * (3 / 2 : ℝ))^2 + (1 / 4 : ℝ)^2 := by
      norm_num
    calc
      (81 / 4 : ℝ) ≤ ((3 : ℝ) * (3 / 2 : ℝ))^2 + (1 / 4 : ℝ)^2 := hconst
      _ ≤ (Real.pi * (3 / 2 : ℝ))^2 + (1 / 4 : ℝ)^2 := by nlinarith [hpi_part]
      _ = ‖z‖^2 := hnorm.symm
  have hnorm_term : (1 / 8 : ℝ) * (1 / ‖z‖^2) ≤ (1 / 160 : ℝ) := by
    have hpos : 0 < (81 / 4 : ℝ) := by nlinarith
    have hle : (81 / 4 : ℝ) ≤ ‖z‖^2 := hnorm_sq
    have hdiv := one_div_le_one_div_of_le hpos hle
    have hdiv' : (1 / ‖z‖^2 : ℝ) ≤ (4 / 81 : ℝ) := by
      simpa using hdiv
    have hmul : (1 / 8 : ℝ) * (1 / ‖z‖^2) ≤ (1 / 8 : ℝ) * (4 / 81 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hdiv' (by norm_num)
    have hconst : (1 / 8 : ℝ) * (4 / 81 : ℝ) ≤ (1 / 160 : ℝ) := by norm_num
    exact le_trans hmul hconst
  have hsmall :
      (1 / (32 * Real.pi^2 * (3 / 2 : ℝ)^2) : ℝ) + (1 / 8 : ℝ) * (1 / ‖z‖^2) ≤
        (1 / 20 : ℝ) := by
    nlinarith [hpi_term, hnorm_term]
  nlinarith [hstep, hlog_bound, hsmall]

theorem a_five_half_bound : a (5 / 2 : ℝ) ≥ (-21 / 20 : ℝ) := by
  have hxi : 0 < (5 / 2 : ℝ) := by norm_num
  set z : ℂ := (1 / 4 : ℂ) + Complex.I * Real.pi * (5 / 2 : ℝ)
  have hbase :
      a (5 / 2 : ℝ) ≥
        Real.log Real.pi - Real.log ‖z‖ - (1 / 8 : ℝ) * (1 / ‖z‖^2) := by
    simpa [z] using (a_lower_bound_from_stieltjes (5 / 2 : ℝ))
  have hlog :
      Real.log ‖z‖ ≤
        Real.log (Real.pi * (5 / 2 : ℝ)) +
          (1 / (32 * Real.pi^2 * (5 / 2 : ℝ)^2) : ℝ) := by
    have h := log_abs_z_le (5 / 2 : ℝ) hxi
    simpa [z] using h
  have hlog' :
      -Real.log ‖z‖ ≥
        -Real.log (Real.pi * (5 / 2 : ℝ)) -
          (1 / (32 * Real.pi^2 * (5 / 2 : ℝ)^2) : ℝ) := by
    nlinarith [hlog]
  have hstep :
      a (5 / 2 : ℝ) ≥
        -Real.log (5 / 2 : ℝ) - (1 / (32 * Real.pi^2 * (5 / 2 : ℝ)^2) : ℝ) -
          (1 / 8 : ℝ) * (1 / ‖z‖^2) := by
    have hlog_pi :
        Real.log Real.pi - Real.log (Real.pi * (5 / 2 : ℝ)) = -Real.log (5 / 2 : ℝ) := by
      have hpi_pos : 0 < (Real.pi : ℝ) := Real.pi_pos
      have hpi_ne : (Real.pi : ℝ) ≠ 0 := ne_of_gt hpi_pos
      have hpi_mul_ne : (Real.pi * (5 / 2 : ℝ) : ℝ) ≠ 0 := by nlinarith [hpi_pos]
      have hlog_div := Real.log_div hpi_ne hpi_mul_ne
      have hratio : Real.pi / (Real.pi * (5 / 2 : ℝ)) = (1 / (5 / 2 : ℝ)) := by
        field_simp [Real.pi_ne_zero]
      calc
        Real.log Real.pi - Real.log (Real.pi * (5 / 2 : ℝ)) =
            Real.log (Real.pi / (Real.pi * (5 / 2 : ℝ))) := by
              symm
              simpa using hlog_div
        _ = Real.log (1 / (5 / 2 : ℝ)) := by simp [hratio]
        _ = -Real.log (5 / 2 : ℝ) := by
          simpa [one_div] using (Real.log_inv (5 / 2 : ℝ))
    nlinarith [hbase, hlog', hlog_pi]
  have hlog_bound : -Real.log (5 / 2 : ℝ) ≥ (-1 : ℝ) := by
    have hlt := log_five_halves_lt_one
    linarith
  have hpi2 : (9 : ℝ) ≤ Real.pi^2 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith [hpi]
  have hpi_term :
      (1 / (32 * Real.pi^2 * (5 / 2 : ℝ)^2) : ℝ) ≤ (1 / 1800 : ℝ) := by
    have hpos : 0 < (1800 : ℝ) := by norm_num
    have hle : (1800 : ℝ) ≤ 32 * Real.pi^2 * (5 / 2 : ℝ)^2 := by
      nlinarith [hpi2]
    exact one_div_le_one_div_of_le hpos hle
  have hnorm_sq :
      (225 / 4 : ℝ) ≤ ‖z‖^2 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hpi2 : (3 : ℝ)^2 ≤ Real.pi^2 := by nlinarith [hpi]
    have hnorm : ‖z‖^2 = (Real.pi * (5 / 2 : ℝ))^2 + (1 / 4 : ℝ)^2 := by
      simpa [z] using (norm_z_sq (5 / 2 : ℝ))
    have hpi_part : ((3 : ℝ) * (5 / 2 : ℝ))^2 ≤ (Real.pi * (5 / 2 : ℝ))^2 := by
      nlinarith [hpi2]
    have hconst : (225 / 4 : ℝ) ≤ ((3 : ℝ) * (5 / 2 : ℝ))^2 + (1 / 4 : ℝ)^2 := by
      norm_num
    calc
      (225 / 4 : ℝ) ≤ ((3 : ℝ) * (5 / 2 : ℝ))^2 + (1 / 4 : ℝ)^2 := hconst
      _ ≤ (Real.pi * (5 / 2 : ℝ))^2 + (1 / 4 : ℝ)^2 := by nlinarith [hpi_part]
      _ = ‖z‖^2 := hnorm.symm
  have hnorm_term : (1 / 8 : ℝ) * (1 / ‖z‖^2) ≤ (1 / 225 : ℝ) := by
    have hpos : 0 < (225 / 4 : ℝ) := by nlinarith
    have hle : (225 / 4 : ℝ) ≤ ‖z‖^2 := hnorm_sq
    have hdiv := one_div_le_one_div_of_le hpos hle
    have hdiv' : (1 / ‖z‖^2 : ℝ) ≤ (4 / 225 : ℝ) := by
      simpa using hdiv
    have hmul :
        (1 / 8 : ℝ) * (1 / ‖z‖^2) ≤ (1 / 8 : ℝ) * (4 / 225 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hdiv' (by norm_num)
    have hconst : (1 / 8 : ℝ) * (4 / 225 : ℝ) ≤ (1 / 225 : ℝ) := by norm_num
    exact le_trans hmul hconst
  have hsmall :
      (1 / (32 * Real.pi^2 * (5 / 2 : ℝ)^2) : ℝ) + (1 / 8 : ℝ) * (1 / ‖z‖^2) ≤
        (1 / 200 : ℝ) := by
    nlinarith [hpi_term, hnorm_term]
  have hfinal : a (5 / 2 : ℝ) ≥ (-1 : ℝ) - (1 / 200 : ℝ) := by
    nlinarith [hstep, hlog_bound, hsmall]
  have hconst : (-1 : ℝ) - (1 / 200 : ℝ) ≥ (-21 / 20 : ℝ) := by
    norm_num
  nlinarith [hfinal, hconst]

lemma a_one_bound : a (1 : ℝ) ≥ (-1 / 50 : ℝ) := by
  have hxi : 0 < (1 : ℝ) := by norm_num
  set z : ℂ := (1 / 4 : ℂ) + Complex.I * Real.pi * (1 : ℝ)
  have hbase :
      a (1 : ℝ) ≥
        Real.log Real.pi - Real.log ‖z‖ - (1 / 8 : ℝ) * (1 / ‖z‖^2) := by
    simpa [z] using (a_lower_bound_from_stieltjes (1 : ℝ))
  have hlog :
      Real.log ‖z‖ ≤
        Real.log (Real.pi * (1 : ℝ)) + (1 / (32 * Real.pi^2) : ℝ) := by
    have h := log_abs_z_le (1 : ℝ) hxi
    simpa [z] using h
  have hlog' :
      -Real.log ‖z‖ ≥ -Real.log Real.pi - (1 / (32 * Real.pi^2) : ℝ) := by
    have hlog'' :
        -Real.log ‖z‖ ≥ -Real.log (Real.pi * (1 : ℝ)) - (1 / (32 * Real.pi^2) : ℝ) := by
      nlinarith [hlog]
    simpa using hlog''
  have hstep :
      a (1 : ℝ) ≥
        -(1 / (32 * Real.pi^2) : ℝ) - (1 / 8 : ℝ) * (1 / ‖z‖^2) := by
    nlinarith [hbase, hlog']
  have hpi2 : (9 : ℝ) ≤ Real.pi^2 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith [hpi]
  have hpi_term : (1 / (32 * Real.pi^2) : ℝ) ≤ (1 / 288 : ℝ) := by
    have hpos : 0 < (288 : ℝ) := by norm_num
    have hle : (288 : ℝ) ≤ 32 * Real.pi^2 := by nlinarith [hpi2]
    exact one_div_le_one_div_of_le hpos hle
  have hnorm_sq :
      (145 / 16 : ℝ) ≤ ‖z‖^2 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hpi2 : (3 : ℝ)^2 ≤ Real.pi^2 := by nlinarith [hpi]
    have hnorm : ‖z‖^2 = (Real.pi : ℝ)^2 + (1 / 4 : ℝ)^2 := by
      simpa [z] using (norm_z_sq (1 : ℝ))
    have hpi_part : (3 : ℝ)^2 ≤ (Real.pi : ℝ)^2 := by nlinarith [hpi2]
    have hconst : (145 / 16 : ℝ) ≤ (3 : ℝ)^2 + (1 / 4 : ℝ)^2 := by
      norm_num
    calc
      (145 / 16 : ℝ) ≤ (3 : ℝ)^2 + (1 / 4 : ℝ)^2 := hconst
      _ ≤ (Real.pi : ℝ)^2 + (1 / 4 : ℝ)^2 := by nlinarith [hpi_part]
      _ = ‖z‖^2 := hnorm.symm
  have hnorm_term : (1 / 8 : ℝ) * (1 / ‖z‖^2) ≤ (2 / 145 : ℝ) := by
    have hpos : 0 < (145 / 16 : ℝ) := by nlinarith
    have hle : (145 / 16 : ℝ) ≤ ‖z‖^2 := hnorm_sq
    have hdiv := one_div_le_one_div_of_le hpos hle
    have hdiv' : (1 / ‖z‖^2 : ℝ) ≤ (16 / 145 : ℝ) := by
      simpa using hdiv
    nlinarith [hdiv']
  have hsmall :
      (1 / (32 * Real.pi^2) : ℝ) + (1 / 8 : ℝ) * (1 / ‖z‖^2) ≤ (1 / 50 : ℝ) := by
    nlinarith [hpi_term, hnorm_term]
  nlinarith [hstep, hsmall]

lemma a_two_bound : a (2 : ℝ) ≥ (-2 : ℝ) := by
  have hxi : 0 < (2 : ℝ) := by norm_num
  set z : ℂ := (1 / 4 : ℂ) + Complex.I * Real.pi * (2 : ℝ)
  have hbase :
      a (2 : ℝ) ≥
        Real.log Real.pi - Real.log ‖z‖ - (1 / 8 : ℝ) * (1 / ‖z‖^2) := by
    simpa [z] using (a_lower_bound_from_stieltjes (2 : ℝ))
  have hlog :
      Real.log ‖z‖ ≤
        Real.log (Real.pi * (2 : ℝ)) + (1 / (32 * Real.pi^2 * (2 : ℝ)^2) : ℝ) := by
    have h := log_abs_z_le (2 : ℝ) hxi
    simpa [z] using h
  have hlog' :
      -Real.log ‖z‖ ≥
        -Real.log (Real.pi * (2 : ℝ)) - (1 / (32 * Real.pi^2 * (2 : ℝ)^2) : ℝ) := by
    nlinarith [hlog]
  have hstep :
      a (2 : ℝ) ≥
        -Real.log (2 : ℝ) - (1 / (32 * Real.pi^2 * (2 : ℝ)^2) : ℝ) -
          (1 / 8 : ℝ) * (1 / ‖z‖^2) := by
    have hlog_pi :
        Real.log Real.pi - Real.log (Real.pi * (2 : ℝ)) = -Real.log (2 : ℝ) := by
      have hpi_pos : 0 < (Real.pi : ℝ) := Real.pi_pos
      have hpi_ne : (Real.pi : ℝ) ≠ 0 := ne_of_gt hpi_pos
      have hpi_mul_ne : (Real.pi * (2 : ℝ) : ℝ) ≠ 0 := by nlinarith [hpi_pos]
      have hlog_div := Real.log_div hpi_ne hpi_mul_ne
      have hratio : Real.pi / (Real.pi * (2 : ℝ)) = (1 / (2 : ℝ)) := by
        field_simp [Real.pi_ne_zero]
      calc
        Real.log Real.pi - Real.log (Real.pi * (2 : ℝ)) =
            Real.log (Real.pi / (Real.pi * (2 : ℝ))) := by
              symm
              simpa using hlog_div
        _ = Real.log (1 / (2 : ℝ)) := by simp [hratio]
        _ = -Real.log (2 : ℝ) := by
          simpa [one_div] using (Real.log_inv (2 : ℝ))
    nlinarith [hbase, hlog', hlog_pi]
  have hpos : 0 < (Real.pi * 2 : ℝ) := by nlinarith [Real.pi_pos]
  have hlog2 : Real.log (2 : ℝ) ≤ (1 : ℝ) := by
    have hle : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.exp_one_gt_d9
      nlinarith
    exact (Real.log_le_iff_le_exp (by linarith : (0 : ℝ) < 2)).2 hle
  have hpi2 : (9 : ℝ) ≤ Real.pi^2 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith [hpi]
  have hnorm_sq : (36 : ℝ) ≤ ‖z‖^2 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hnorm : ‖z‖^2 = (Real.pi * (2 : ℝ))^2 + (1 / 4 : ℝ)^2 := by
      simpa [z] using (norm_z_sq (2 : ℝ))
    have hpi_part : (3 : ℝ)^2 ≤ (Real.pi : ℝ)^2 := by nlinarith [hpi]
    have hconst : (36 : ℝ) ≤ ((3 : ℝ) * (2 : ℝ))^2 + (1 / 4 : ℝ)^2 := by
      norm_num
    calc
      (36 : ℝ) ≤ ((3 : ℝ) * (2 : ℝ))^2 + (1 / 4 : ℝ)^2 := hconst
      _ ≤ (Real.pi * (2 : ℝ))^2 + (1 / 4 : ℝ)^2 := by nlinarith [hpi_part]
      _ = ‖z‖^2 := hnorm.symm
  have hdiv : (1 / ‖z‖^2 : ℝ) ≤ (1 / 36 : ℝ) := by
    have hpos : 0 < (36 : ℝ) := by nlinarith
    exact one_div_le_one_div_of_le hpos hnorm_sq
  have hsmall :
      (1 / (128 * Real.pi^2) : ℝ) + (1 / 8 : ℝ) * (1 / ‖z‖^2) ≤ (1 : ℝ) := by
    have hpi_term : (1 / (128 * Real.pi^2) : ℝ) ≤ (1 / 1152 : ℝ) := by
      have hpos : 0 < (1152 : ℝ) := by norm_num
      have hle : (1152 : ℝ) ≤ 128 * Real.pi^2 := by nlinarith [hpi2]
      exact one_div_le_one_div_of_le hpos hle
    have hnorm_term : (1 / 8 : ℝ) * (1 / ‖z‖^2) ≤ (1 / 288 : ℝ) := by
      nlinarith [hdiv]
    nlinarith [hpi_term, hnorm_term]
  have hbound :
      -Real.log (2 : ℝ) - (1 / (128 * Real.pi^2) : ℝ) -
          (1 / 8 : ℝ) * (1 / ‖z‖^2) ≥ (-2 : ℝ) := by
    have hlog2' : -Real.log (2 : ℝ) ≥ (-1 : ℝ) := by
      linarith [hlog2]
    have hsmall' :
        -((1 / (128 * Real.pi^2) : ℝ) + (1 / 8 : ℝ) * (1 / ‖z‖^2)) ≥ (-1 : ℝ) := by
      linarith [hsmall]
    nlinarith [hlog2', hsmall']
  have hterm_eq :
      (1 / (32 * Real.pi^2 * (2 : ℝ)^2) : ℝ) = (1 / (128 * Real.pi^2) : ℝ) := by
    ring_nf
  have hstep' :
      a (2 : ℝ) ≥
        -Real.log (2 : ℝ) - (1 / (128 * Real.pi^2) : ℝ) -
          (1 / 8 : ℝ) * (1 / ‖z‖^2) := by
    simpa [hterm_eq] using hstep
  calc
    a (2 : ℝ) ≥
        -Real.log (2 : ℝ) - (1 / (128 * Real.pi^2) : ℝ) -
          (1 / 8 : ℝ) * (1 / ‖z‖^2) := hstep'
    _ ≥ (-2 : ℝ) := hbound

lemma a_three_bound : a (3 : ℝ) ≥ (-3 : ℝ) := by
  have hxi : 0 < (3 : ℝ) := by norm_num
  set z : ℂ := (1 / 4 : ℂ) + Complex.I * Real.pi * (3 : ℝ)
  have hbase :
      a (3 : ℝ) ≥
        Real.log Real.pi - Real.log ‖z‖ - (1 / 8 : ℝ) * (1 / ‖z‖^2) := by
    simpa [z] using (a_lower_bound_from_stieltjes (3 : ℝ))
  have hlog :
      Real.log ‖z‖ ≤
        Real.log (Real.pi * (3 : ℝ)) + (1 / (32 * Real.pi^2 * (3 : ℝ)^2) : ℝ) := by
    have h := log_abs_z_le (3 : ℝ) hxi
    simpa [z] using h
  have hlog' :
      -Real.log ‖z‖ ≥
        -Real.log (Real.pi * (3 : ℝ)) - (1 / (32 * Real.pi^2 * (3 : ℝ)^2) : ℝ) := by
    nlinarith [hlog]
  have hstep :
      a (3 : ℝ) ≥
        -Real.log (3 : ℝ) - (1 / (32 * Real.pi^2 * (3 : ℝ)^2) : ℝ) -
          (1 / 8 : ℝ) * (1 / ‖z‖^2) := by
    have hlog_pi :
        Real.log Real.pi - Real.log (Real.pi * (3 : ℝ)) = -Real.log (3 : ℝ) := by
      have hpi_pos : 0 < (Real.pi : ℝ) := Real.pi_pos
      have hpi_ne : (Real.pi : ℝ) ≠ 0 := ne_of_gt hpi_pos
      have hpi_mul_ne : (Real.pi * (3 : ℝ) : ℝ) ≠ 0 := by nlinarith [hpi_pos]
      have hlog_div := Real.log_div hpi_ne hpi_mul_ne
      have hratio : Real.pi / (Real.pi * (3 : ℝ)) = (1 / (3 : ℝ)) := by
        field_simp [Real.pi_ne_zero]
      calc
        Real.log Real.pi - Real.log (Real.pi * (3 : ℝ)) =
            Real.log (Real.pi / (Real.pi * (3 : ℝ))) := by
              symm
              simpa using hlog_div
        _ = Real.log (1 / (3 : ℝ)) := by simp [hratio]
        _ = -Real.log (3 : ℝ) := by
          simpa [one_div] using (Real.log_inv (3 : ℝ))
    nlinarith [hbase, hlog', hlog_pi]
  have hlog3 : Real.log (3 : ℝ) ≤ (2 : ℝ) := by
    have h_exp1 : (2.7 : ℝ) ≤ Real.exp 1 := by
      have h := Real.exp_one_gt_d9
      nlinarith
    have h_pow : (2.7 : ℝ)^2 ≤ (Real.exp 1)^2 := by
      exact pow_le_pow_left₀ (by positivity : 0 ≤ (2.7 : ℝ)) h_exp1 _
    have h_exp2 : (2.7 : ℝ)^2 ≤ Real.exp 2 := by
      have h := Real.exp_nat_mul 1 2
      simpa using (h_pow.trans_eq h.symm)
    have h_num : (3 : ℝ) ≤ (2.7 : ℝ)^2 := by norm_num
    have hle : (3 : ℝ) ≤ Real.exp 2 := by exact le_trans h_num h_exp2
    exact (Real.log_le_iff_le_exp (by linarith : (0 : ℝ) < 3)).2 hle
  have hpi2 : (9 : ℝ) ≤ Real.pi^2 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith [hpi]
  have hnorm_sq : (81 : ℝ) ≤ ‖z‖^2 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hnorm : ‖z‖^2 = (Real.pi * (3 : ℝ))^2 + (1 / 4 : ℝ)^2 := by
      simpa [z] using (norm_z_sq (3 : ℝ))
    have hpi_part : (3 : ℝ)^2 ≤ (Real.pi : ℝ)^2 := by nlinarith [hpi]
    have hconst : (81 : ℝ) ≤ ((3 : ℝ) * (3 : ℝ))^2 + (1 / 4 : ℝ)^2 := by
      norm_num
    calc
      (81 : ℝ) ≤ ((3 : ℝ) * (3 : ℝ))^2 + (1 / 4 : ℝ)^2 := hconst
      _ ≤ (Real.pi * (3 : ℝ))^2 + (1 / 4 : ℝ)^2 := by nlinarith [hpi_part]
      _ = ‖z‖^2 := hnorm.symm
  have hdiv : (1 / ‖z‖^2 : ℝ) ≤ (1 / 81 : ℝ) := by
    have hpos : 0 < (81 : ℝ) := by nlinarith
    exact one_div_le_one_div_of_le hpos hnorm_sq
  have hsmall :
      (1 / (32 * Real.pi^2 * (3 : ℝ)^2) : ℝ) + (1 / 8 : ℝ) * (1 / ‖z‖^2) ≤
        (1 : ℝ) := by
    have hpi_term : (1 / (32 * Real.pi^2 * (3 : ℝ)^2) : ℝ) ≤ (1 / 288 : ℝ) := by
      have hpos : 0 < (288 : ℝ) := by norm_num
      have hle : (288 : ℝ) ≤ 32 * Real.pi^2 * (3 : ℝ)^2 := by
        nlinarith [hpi2]
      exact one_div_le_one_div_of_le hpos hle
    have hnorm_term : (1 / 8 : ℝ) * (1 / ‖z‖^2) ≤ (1 / 648 : ℝ) := by
      nlinarith [hdiv]
    nlinarith [hpi_term, hnorm_term]
  nlinarith [hstep, hlog3, hsmall]
