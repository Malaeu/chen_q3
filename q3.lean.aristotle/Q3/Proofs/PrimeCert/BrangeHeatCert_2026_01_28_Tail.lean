import Mathlib
import Q3.Basic.Defs
import Q3.Proofs.Params_Critical
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_Data

/-!
Analytic tail bound for the heat-weighted prime sum (t_critical, tau = 0).
This keeps the proof independent of interval arithmetic.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

open Q3

def prime_heat_tail_term (n : ℕ) : ℝ :=
  ((2 * Real.log (n : ℝ)) / Real.sqrt n) *
    Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) * |xi_n n|

lemma xi_n_sq_scaled (n : ℕ) :
    4 * Real.pi ^ 2 * (xi_n n) ^ 2 = (Real.log n) ^ 2 := by
  have hpi : (Real.pi : ℝ) ≠ 0 := by
    exact Real.pi_ne_zero
  simp [xi_n, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  field_simp [hpi]
  ring

lemma prime_heat_weight_term_le_tail_term (n : ℕ) :
    prime_heat_weight_term n ≤ prime_heat_tail_term n := by
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log
  have hmul : (2 : ℝ) * ArithmeticFunction.vonMangoldt n ≤
      (2 : ℝ) * Real.log (n : ℝ) := by
    exact mul_le_mul_of_nonneg_left hΛ (by norm_num)
  have hden : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have h_w : w_Q n ≤ (2 * Real.log (n : ℝ)) / Real.sqrt n := by
    unfold w_Q
    exact div_le_div_of_nonneg_right hmul hden
  have h_ind_le : (if |xi_n n| ≤ prime_cert_B_max then (1 : ℝ) else 0) ≤ 1 := by
    by_cases h : |xi_n n| ≤ prime_cert_B_max <;> simp [h]
  have h_factor_nonneg :
      0 ≤ w_Q n * (Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) * |xi_n n|) := by
    have hw_nonneg : 0 ≤ w_Q n := w_Q_nonneg n
    have hexp_nonneg :
        0 ≤ Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) := Real.exp_nonneg _
    have hxi_nonneg : 0 ≤ |xi_n n| := abs_nonneg _
    exact mul_nonneg hw_nonneg (mul_nonneg hexp_nonneg hxi_nonneg)
  have h_exp_nonneg :
      0 ≤ Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) := Real.exp_nonneg _
  have h_xi_nonneg : 0 ≤ |xi_n n| := abs_nonneg _
  have hmul_nonneg :
      0 ≤ Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) * |xi_n n| := by
    exact mul_nonneg h_exp_nonneg h_xi_nonneg
  calc
    prime_heat_weight_term n
        = w_Q n * (Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) * |xi_n n|) *
            (if |xi_n n| ≤ prime_cert_B_max then (1 : ℝ) else 0) := by
            simp [prime_heat_weight_term, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ w_Q n * (Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) * |xi_n n|) * 1 := by
            exact mul_le_mul_of_nonneg_left h_ind_le h_factor_nonneg
    _ = w_Q n * (Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) * |xi_n n|) := by
            simp
    _ ≤ ((2 * Real.log (n : ℝ)) / Real.sqrt n) *
          (Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) * |xi_n n|) := by
            exact mul_le_mul_of_nonneg_right h_w hmul_nonneg
    _ = prime_heat_tail_term n := by
            simp [prime_heat_tail_term, mul_comm, mul_left_comm, mul_assoc]

lemma prime_heat_weight_term_shift_le_tail_term (n : ℕ) :
    prime_heat_weight_term (n + (prime_cert_heat_N + 1)) ≤
      prime_heat_tail_term (n + (prime_cert_heat_N + 1)) := by
  simpa using prime_heat_weight_term_le_tail_term (n + (prime_cert_heat_N + 1))

def prime_heat_tail_N0 : ℕ := prime_cert_heat_N + 1

lemma prime_heat_tail_N0_pos : (0 : ℝ) < (prime_heat_tail_N0 : ℝ) := by
  norm_num [prime_heat_tail_N0, prime_cert_heat_N]

lemma prime_heat_tail_log_N0_ge_13 :
    (13 : ℝ) ≤ Real.log (prime_heat_tail_N0 : ℝ) := by
  have h_exp1_le : Real.exp (1 : ℝ) ≤ (2.7182818286 : ℝ) := by
    exact le_of_lt Real.exp_one_lt_d9
  have h_exp13_le : Real.exp (13 : ℝ) ≤ (2.7182818286 : ℝ) ^ (13 : ℕ) := by
    have hpow : Real.exp (13 : ℝ) = (Real.exp 1) ^ (13 : ℕ) := by
      simpa [mul_comm] using (Real.exp_nat_mul (1 : ℝ) 13)
    have hpow_le : (Real.exp 1) ^ (13 : ℕ) ≤ (2.7182818286 : ℝ) ^ (13 : ℕ) := by
      exact pow_le_pow_left₀ (Real.exp_pos 1).le h_exp1_le 13
    calc
      Real.exp (13 : ℝ) = (Real.exp 1) ^ (13 : ℕ) := hpow
      _ ≤ (2.7182818286 : ℝ) ^ (13 : ℕ) := hpow_le
  have hpow_lt : (2.7182818286 : ℝ) ^ (13 : ℕ) < (prime_heat_tail_N0 : ℝ) := by
    norm_num [prime_heat_tail_N0, prime_cert_heat_N]
  have h_exp13_le' : Real.exp (13 : ℝ) ≤ (prime_heat_tail_N0 : ℝ) :=
    le_trans h_exp13_le (le_of_lt hpow_lt)
  have hlog_le := Real.log_le_log (Real.exp_pos 13) h_exp13_le'
  simpa using hlog_le

lemma prime_heat_tail_exp_le_rpow
    {m : ℕ} (hm : prime_heat_tail_N0 ≤ m) :
    Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) ≤
      (m : ℝ) ^ (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ))) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    have hN0_pos_nat : 0 < prime_heat_tail_N0 := by
      norm_num [prime_heat_tail_N0, prime_cert_heat_N]
    have hm_pos_nat : 0 < m := lt_of_lt_of_le hN0_pos_nat hm
    exact_mod_cast hm_pos_nat
  have hlog_m_nonneg : 0 ≤ Real.log (m : ℝ) := by
    simpa using (Real.log_natCast_nonneg m)
  have hlog_N0_le : Real.log (prime_heat_tail_N0 : ℝ) ≤ Real.log (m : ℝ) := by
    have hN0_pos : (0 : ℝ) < (prime_heat_tail_N0 : ℝ) := prime_heat_tail_N0_pos
    have hN0_le : (prime_heat_tail_N0 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hm
    exact Real.log_le_log hN0_pos hN0_le
  have ht_nonneg : 0 ≤ t_critical := by
    norm_num [t_critical]
  have hmul : t_critical * Real.log (prime_heat_tail_N0 : ℝ) ≤
      t_critical * Real.log (m : ℝ) := by
    exact mul_le_mul_of_nonneg_left hlog_N0_le ht_nonneg
  have hmul' :
      (t_critical * Real.log (prime_heat_tail_N0 : ℝ)) * Real.log (m : ℝ) ≤
        (t_critical * Real.log (m : ℝ)) * Real.log (m : ℝ) := by
    exact mul_le_mul_of_nonneg_right hmul hlog_m_nonneg
  have hneg :
      -t_critical * (Real.log (m : ℝ)) ^ 2 ≤
        -(t_critical * Real.log (prime_heat_tail_N0 : ℝ)) * Real.log (m : ℝ) := by
    have hmul'' :
        t_critical * (Real.log (m : ℝ)) ^ 2 ≥
          (t_critical * Real.log (prime_heat_tail_N0 : ℝ)) * Real.log (m : ℝ) := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul'
    nlinarith
  have hexp' :
      Real.exp (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ)) * Real.log (m : ℝ)) =
        (m : ℝ) ^ (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ))) := by
    have h := (Real.rpow_def_of_pos hm_pos (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ))))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h.symm
  calc
    Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2)
        ≤ Real.exp (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ)) * Real.log (m : ℝ)) := by
            exact (Real.exp_le_exp).2 hneg
    _ = (m : ℝ) ^ (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ))) := hexp'

def prime_heat_tail_eps : ℝ := (1 / 10 : ℝ)

def prime_heat_tail_p0 : ℝ := (9 / 4 : ℝ)

def prime_heat_tail_coeff : ℝ := (100 / 3 : ℝ)

lemma prime_heat_tail_p0_le :
    prime_heat_tail_p0 ≤
      t_critical * Real.log (prime_heat_tail_N0 : ℝ) + (3 / 10 : ℝ) := by
  have hlog : (13 : ℝ) ≤ Real.log (prime_heat_tail_N0 : ℝ) :=
    prime_heat_tail_log_N0_ge_13
  have ht : t_critical = (3 / 20 : ℝ) := by
    simp [t_critical]
  -- 13 * (3/20) + 3/10 = 9/4
  have h' :
      (9 / 4 : ℝ) ≤
        t_critical * Real.log (prime_heat_tail_N0 : ℝ) + (3 / 10 : ℝ) := by
    nlinarith [hlog, ht]
  simpa [prime_heat_tail_p0] using h'

lemma prime_heat_tail_term_le_rpow_p0 {m : ℕ} (hm : prime_heat_tail_N0 ≤ m) :
    prime_heat_tail_term m ≤
      prime_heat_tail_coeff * (m : ℝ) ^ (-prime_heat_tail_p0) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    have hN0_pos : 0 < prime_heat_tail_N0 := by
      norm_num [prime_heat_tail_N0, prime_cert_heat_N]
    have hm_pos_nat : 0 < m := lt_of_lt_of_le hN0_pos hm
    exact_mod_cast hm_pos_nat
  have hlog_nonneg : 0 ≤ Real.log (m : ℝ) := by
    simpa using (Real.log_natCast_nonneg m)
  have h2pi_pos : (0 : ℝ) < (2 * Real.pi) := by
    nlinarith [Real.pi_pos]
  have h2pi_ge : (6 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have h_inv : (1 / (2 * Real.pi) : ℝ) ≤ (1 / 6 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) h2pi_ge
  have h_exp :
      Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n m) ^ 2) =
        Real.exp (-t_critical * (Real.log m) ^ 2) := by
    have hpow :
        4 * Real.pi ^ 2 * t_critical * (xi_n m) ^ 2 =
          t_critical * (Real.log m) ^ 2 := by
      calc
        4 * Real.pi ^ 2 * t_critical * (xi_n m) ^ 2
            = t_critical * (4 * Real.pi ^ 2 * (xi_n m) ^ 2) := by
                ring
        _ = t_critical * (Real.log m) ^ 2 := by
                simp [xi_n_sq_scaled]
    have hpow' :
        -4 * Real.pi ^ 2 * t_critical * (xi_n m) ^ 2 =
          -t_critical * (Real.log m) ^ 2 := by
      calc
        -4 * Real.pi ^ 2 * t_critical * (xi_n m) ^ 2
            = -(4 * Real.pi ^ 2 * t_critical * (xi_n m) ^ 2) := by
                ring
        _ = -(t_critical * (Real.log m) ^ 2) := by
                simp [hpow]
        _ = -t_critical * (Real.log m) ^ 2 := by
                ring
    simpa [hpow']
  have hxi_le : |xi_n m| ≤ Real.log (m : ℝ) / 6 := by
    have hxi_nonneg : 0 ≤ xi_n m := by
      exact div_nonneg hlog_nonneg (le_of_lt h2pi_pos)
    have hxi_eq : |xi_n m| = xi_n m := by
      simpa using (abs_of_nonneg hxi_nonneg)
    have hxi_eq' : |xi_n m| = Real.log (m : ℝ) / (2 * Real.pi) := by
      simpa [xi_n] using hxi_eq
    calc
      |xi_n m| = Real.log (m : ℝ) / (2 * Real.pi) := hxi_eq'
      _ = Real.log (m : ℝ) * (1 / (2 * Real.pi)) := by
            simp [div_eq_mul_inv]
      _ ≤ Real.log (m : ℝ) * (1 / 6 : ℝ) := by
            exact mul_le_mul_of_nonneg_left h_inv hlog_nonneg
      _ = Real.log (m : ℝ) / 6 := by
            simp [div_eq_mul_inv]
  have hfactor_nonneg :
      0 ≤ ((2 * Real.log (m : ℝ)) / Real.sqrt m) *
          Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) := by
    have hlog_nonneg' : 0 ≤ (2 * Real.log (m : ℝ)) / Real.sqrt m := by
      exact div_nonneg (mul_nonneg (by norm_num) hlog_nonneg) (Real.sqrt_nonneg _)
    exact mul_nonneg hlog_nonneg' (Real.exp_nonneg _)
  have hstep1 :
      prime_heat_tail_term m ≤
        ((2 * Real.log (m : ℝ)) / Real.sqrt m) *
          Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) *
            (Real.log (m : ℝ) / 6) := by
    have htail :
        prime_heat_tail_term m =
          ((2 * Real.log (m : ℝ)) / Real.sqrt m) *
            Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) * |xi_n m| := by
      dsimp [prime_heat_tail_term]
      rw [h_exp]
    calc
      prime_heat_tail_term m =
          ((2 * Real.log (m : ℝ)) / Real.sqrt m) *
            Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) * |xi_n m| := htail
      _ ≤ ((2 * Real.log (m : ℝ)) / Real.sqrt m) *
            Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) *
              (Real.log (m : ℝ) / 6) := by
            exact mul_le_mul_of_nonneg_left hxi_le hfactor_nonneg
  have hlog_le :
      Real.log (m : ℝ) ≤ (m : ℝ) ^ prime_heat_tail_eps / prime_heat_tail_eps := by
    simpa [prime_heat_tail_eps] using
      (Real.log_natCast_le_rpow_div m (by norm_num : (0 : ℝ) < (1 / 10 : ℝ)))
  have hA_nonneg :
      0 ≤ (m : ℝ) ^ prime_heat_tail_eps / prime_heat_tail_eps := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hpow_nonneg : 0 ≤ (m : ℝ) ^ prime_heat_tail_eps :=
      Real.rpow_nonneg hm_nonneg _
    have h_eps_pos : 0 < prime_heat_tail_eps := by norm_num [prime_heat_tail_eps]
    exact div_nonneg hpow_nonneg (le_of_lt h_eps_pos)
  have hlog_sq :
      (Real.log (m : ℝ)) ^ 2 ≤
        ((m : ℝ) ^ prime_heat_tail_eps / prime_heat_tail_eps) *
          ((m : ℝ) ^ prime_heat_tail_eps / prime_heat_tail_eps) := by
    have h := mul_le_mul hlog_le hlog_le hlog_nonneg hA_nonneg
    simpa [pow_two] using h
  have hlog_sq' :
      (Real.log (m : ℝ)) ^ 2 ≤
        (1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^ (2 * prime_heat_tail_eps) := by
    have hm_pos' : 0 < (m : ℝ) := hm_pos
    have hpow :
        ((m : ℝ) ^ prime_heat_tail_eps) * ((m : ℝ) ^ prime_heat_tail_eps) =
          (m : ℝ) ^ (2 * prime_heat_tail_eps) := by
      have h := (Real.rpow_add (x := (m : ℝ)) hm_pos' prime_heat_tail_eps prime_heat_tail_eps)
      -- rewrite a+a as 2*a
      simpa [two_mul, add_comm, add_left_comm, add_assoc] using h.symm
    have hcoeff :
        ((m : ℝ) ^ prime_heat_tail_eps / prime_heat_tail_eps) *
          ((m : ℝ) ^ prime_heat_tail_eps / prime_heat_tail_eps) =
        (1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^ (2 * prime_heat_tail_eps) := by
      calc
        ((m : ℝ) ^ prime_heat_tail_eps / prime_heat_tail_eps) *
            ((m : ℝ) ^ prime_heat_tail_eps / prime_heat_tail_eps)
            = ((m : ℝ) ^ prime_heat_tail_eps * (m : ℝ) ^ prime_heat_tail_eps) *
                ((prime_heat_tail_eps)⁻¹ * (prime_heat_tail_eps)⁻¹) := by
                  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        _ = (m : ℝ) ^ (2 * prime_heat_tail_eps) *
              ((prime_heat_tail_eps)⁻¹ * (prime_heat_tail_eps)⁻¹) := by
              simp [hpow, mul_comm, mul_left_comm, mul_assoc]
        _ = (m : ℝ) ^ (2 * prime_heat_tail_eps) * (prime_heat_tail_eps ^ 2)⁻¹ := by
              simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
        _ = (1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^ (2 * prime_heat_tail_eps) := by
              ring
    calc
      (Real.log (m : ℝ)) ^ 2 ≤
          ((m : ℝ) ^ prime_heat_tail_eps / prime_heat_tail_eps) *
            ((m : ℝ) ^ prime_heat_tail_eps / prime_heat_tail_eps) := hlog_sq
      _ = (1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^ (2 * prime_heat_tail_eps) := by
            simpa [hcoeff]
  have hdiv_le :
      (1 / 3 : ℝ) * (Real.log (m : ℝ)) ^ 2 / Real.sqrt m ≤
        (1 / 3 : ℝ) *
          ((1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^ (2 * prime_heat_tail_eps)) /
            Real.sqrt m := by
    have hnonneg : 0 ≤ (1 / 3 : ℝ) := by norm_num
    have hsqrt_nonneg : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
    -- multiply by (1/3) and divide by sqrt m
    have h1 :
        (1 / 3 : ℝ) * (Real.log (m : ℝ)) ^ 2 ≤
          (1 / 3 : ℝ) *
            ((1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^ (2 * prime_heat_tail_eps)) := by
      exact mul_le_mul_of_nonneg_left hlog_sq' hnonneg
    -- divide both sides by sqrt m ≥ 0
    exact (div_le_div_of_nonneg_right h1 hsqrt_nonneg)
  have hsqrt : Real.sqrt (m : ℝ) = (m : ℝ) ^ (1 / 2 : ℝ) := by
    simpa [one_div] using (Real.sqrt_eq_rpow (m : ℝ))
  have hdiv :
      ((1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^ (2 * prime_heat_tail_eps)) /
          Real.sqrt m =
        (1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^ (2 * prime_heat_tail_eps - (1 / 2 : ℝ)) := by
    have hm_pos' : 0 < (m : ℝ) := hm_pos
    have h := (Real.rpow_sub (x := (m : ℝ)) (y := 2 * prime_heat_tail_eps)
      (z := (1 / 2 : ℝ)) hm_pos')
    -- rewrite using sqrt = rpow
    calc
      ((1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^ (2 * prime_heat_tail_eps)) /
          Real.sqrt m
          = (1 / (prime_heat_tail_eps ^ 2 : ℝ)) *
              ((m : ℝ) ^ (2 * prime_heat_tail_eps) / Real.sqrt m) := by
                ring
      _ = (1 / (prime_heat_tail_eps ^ 2 : ℝ)) *
              ((m : ℝ) ^ (2 * prime_heat_tail_eps) / (m : ℝ) ^ (1 / 2 : ℝ)) := by
                simp [hsqrt]
      _ = (1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^ (2 * prime_heat_tail_eps - (1 / 2 : ℝ)) := by
                have h' :=
                  congrArg (fun x => (1 / (prime_heat_tail_eps ^ 2 : ℝ)) * x) h.symm
                simpa [mul_comm, mul_left_comm, mul_assoc] using h'
  have hdiv' :
      (1 / 3 : ℝ) *
          ((1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^ (2 * prime_heat_tail_eps)) /
            Real.sqrt m =
        prime_heat_tail_coeff * (m : ℝ) ^ (2 * prime_heat_tail_eps - (1 / 2 : ℝ)) := by
    have hcoeff :
        (1 / 3 : ℝ) * (1 / (prime_heat_tail_eps ^ 2 : ℝ)) = prime_heat_tail_coeff := by
      norm_num [prime_heat_tail_coeff, prime_heat_tail_eps]
    have hdiv'' :
        (1 / 3 : ℝ) *
            (((1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^ (2 * prime_heat_tail_eps)) /
              Real.sqrt m) =
          (1 / 3 : ℝ) *
            ((1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^
              (2 * prime_heat_tail_eps - (1 / 2 : ℝ))) := by
      have h := congrArg (fun x => (1 / 3 : ℝ) * x) hdiv
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    calc
      (1 / 3 : ℝ) *
          ((1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^ (2 * prime_heat_tail_eps)) /
            Real.sqrt m
          = (1 / 3 : ℝ) *
            (((1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^ (2 * prime_heat_tail_eps)) /
              Real.sqrt m) := by
                ring
      _ = (1 / 3 : ℝ) *
            ((1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^
              (2 * prime_heat_tail_eps - (1 / 2 : ℝ))) := hdiv''
      _ = prime_heat_tail_coeff * (m : ℝ) ^ (2 * prime_heat_tail_eps - (1 / 2 : ℝ)) := by
            have hcoeff' :
                prime_heat_tail_coeff =
                  (1 / 3 : ℝ) * (1 / (prime_heat_tail_eps ^ 2 : ℝ)) := by
              symm
              exact hcoeff
            simp [hcoeff', mul_comm, mul_left_comm, mul_assoc]
  have hexp_le := prime_heat_tail_exp_le_rpow (m := m) hm
  have hnonneg1 :
      0 ≤ prime_heat_tail_coeff * (m : ℝ) ^ (2 * prime_heat_tail_eps - (1 / 2 : ℝ)) := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hrpow_nonneg :
        0 ≤ (m : ℝ) ^ (2 * prime_heat_tail_eps - (1 / 2 : ℝ)) :=
      Real.rpow_nonneg hm_nonneg _
    have hcoeff_nonneg : 0 ≤ prime_heat_tail_coeff := by
      norm_num [prime_heat_tail_coeff]
    exact mul_nonneg hcoeff_nonneg hrpow_nonneg
  have hmul :
      (1 / 3 : ℝ) * (Real.log (m : ℝ)) ^ 2 / Real.sqrt m *
          Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) ≤
        prime_heat_tail_coeff * (m : ℝ) ^ (2 * prime_heat_tail_eps - (1 / 2 : ℝ)) *
          (m : ℝ) ^ (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ))) := by
    have h1 :
        (1 / 3 : ℝ) * (Real.log (m : ℝ)) ^ 2 / Real.sqrt m ≤
          prime_heat_tail_coeff * (m : ℝ) ^ (2 * prime_heat_tail_eps - (1 / 2 : ℝ)) := by
      calc
        (1 / 3 : ℝ) * (Real.log (m : ℝ)) ^ 2 / Real.sqrt m ≤
            (1 / 3 : ℝ) *
              ((1 / (prime_heat_tail_eps ^ 2 : ℝ)) * (m : ℝ) ^ (2 * prime_heat_tail_eps)) /
                Real.sqrt m := hdiv_le
        _ = prime_heat_tail_coeff * (m : ℝ) ^ (2 * prime_heat_tail_eps - (1 / 2 : ℝ)) := hdiv'
    exact mul_le_mul h1 hexp_le (Real.exp_nonneg _) hnonneg1
  have hcombine :
      (m : ℝ) ^ (2 * prime_heat_tail_eps - (1 / 2 : ℝ)) *
          (m : ℝ) ^ (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ))) =
        (m : ℝ) ^ (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ) + (1 / 2 : ℝ) -
          2 * prime_heat_tail_eps)) := by
    have hm_pos' : 0 < (m : ℝ) := hm_pos
    -- x^a * x^b = x^(a + b)
    have h := (Real.rpow_add (x := (m : ℝ)) hm_pos'
      (2 * prime_heat_tail_eps - (1 / 2 : ℝ))
      (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ)))).symm
    -- rearrange signs
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hpow_le :
      (m : ℝ) ^ (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ) + (1 / 2 : ℝ) -
        2 * prime_heat_tail_eps)) ≤
        (m : ℝ) ^ (-prime_heat_tail_p0) := by
    have hm_one_nat : (1 : ℕ) ≤ m := by
      have hN0_one : (1 : ℕ) ≤ prime_heat_tail_N0 := by
        norm_num [prime_heat_tail_N0, prime_cert_heat_N]
      exact le_trans hN0_one hm
    have hm_one : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hm_one_nat
    have h_exp_le :
        -(t_critical * Real.log (prime_heat_tail_N0 : ℝ) + (1 / 2 : ℝ) -
            2 * prime_heat_tail_eps) ≤ -prime_heat_tail_p0 := by
      have h := prime_heat_tail_p0_le
      -- eps = 1/10, so 1/2 - 2*eps = 3/10
      have h_eps : (1 / 2 : ℝ) - 2 * prime_heat_tail_eps = (3 / 10 : ℝ) := by
        norm_num [prime_heat_tail_eps]
      nlinarith [h, h_eps]
    exact Real.rpow_le_rpow_of_exponent_le hm_one h_exp_le
  calc
    prime_heat_tail_term m
        ≤ (1 / 3 : ℝ) * (Real.log (m : ℝ)) ^ 2 / Real.sqrt m *
            Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) := by
            -- apply hxi_le and simplify constants
            -- rewrite to 1/3 * log^2 / sqrt
            have hrewrite :
                ((2 * Real.log (m : ℝ)) / Real.sqrt m) *
                    Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) *
                      (Real.log (m : ℝ) / 6) =
                  (1 / 3 : ℝ) * (Real.log (m : ℝ)) ^ 2 / Real.sqrt m *
                    Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) := by
              have hm_pos' : 0 < (m : ℝ) := hm_pos
              have hsqrt_ne : (Real.sqrt (m : ℝ)) ≠ 0 := by
                exact ne_of_gt (Real.sqrt_pos.mpr hm_pos')
              have hrewrite' :
                  ((2 * Real.log (m : ℝ)) / Real.sqrt m) * (Real.log (m : ℝ) / 6) =
                    (1 / 3 : ℝ) * (Real.log (m : ℝ)) ^ 2 / Real.sqrt m := by
                field_simp [div_eq_mul_inv, pow_two, hsqrt_ne]
                ring
              calc
                ((2 * Real.log (m : ℝ)) / Real.sqrt m) *
                    Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) *
                      (Real.log (m : ℝ) / 6)
                    = (((2 * Real.log (m : ℝ)) / Real.sqrt m) *
                        (Real.log (m : ℝ) / 6)) *
                          Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) := by
                          ring
                _ = ((1 / 3 : ℝ) * (Real.log (m : ℝ)) ^ 2 / Real.sqrt m) *
                      Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) := by
                          simp [hrewrite']
                _ = (1 / 3 : ℝ) * (Real.log (m : ℝ)) ^ 2 / Real.sqrt m *
                      Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) := by
                          ring
            calc
              prime_heat_tail_term m ≤
                  ((2 * Real.log (m : ℝ)) / Real.sqrt m) *
                    Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) *
                      (Real.log (m : ℝ) / 6) := hstep1
              _ = (1 / 3 : ℝ) * (Real.log (m : ℝ)) ^ 2 / Real.sqrt m *
                    Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) := by
                    simpa [mul_comm, mul_left_comm, mul_assoc] using hrewrite
    _ ≤ prime_heat_tail_coeff * (m : ℝ) ^ (2 * prime_heat_tail_eps - (1 / 2 : ℝ)) *
          (m : ℝ) ^ (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ))) := hmul
    _ = prime_heat_tail_coeff *
          (m : ℝ) ^ (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ) + (1 / 2 : ℝ) -
            2 * prime_heat_tail_eps)) := by
            calc
              prime_heat_tail_coeff * (m : ℝ) ^ (2 * prime_heat_tail_eps - (1 / 2 : ℝ)) *
                  (m : ℝ) ^ (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ)))
                  = prime_heat_tail_coeff *
                    ((m : ℝ) ^ (2 * prime_heat_tail_eps - (1 / 2 : ℝ)) *
                      (m : ℝ) ^ (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ)))) := by
                        ring
              _ = prime_heat_tail_coeff *
                    (m : ℝ) ^ (-(t_critical * Real.log (prime_heat_tail_N0 : ℝ) + (1 / 2 : ℝ) -
                      2 * prime_heat_tail_eps)) := by
                        rw [hcombine]
    _ ≤ prime_heat_tail_coeff * (m : ℝ) ^ (-prime_heat_tail_p0) := by
            exact mul_le_mul_of_nonneg_left hpow_le (by norm_num [prime_heat_tail_coeff])

lemma prime_heat_tail_rpow_sum_le (m : ℕ) :
    (∑ i ∈ Finset.range m,
        (i + prime_heat_tail_N0 : ℝ) ^ (-prime_heat_tail_p0)) ≤
      (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) /
        (prime_heat_tail_p0 - 1) := by
  -- compare to integral of x^(-p0)
  have hanti' :
      AntitoneOn (fun x : ℝ => x ^ (-prime_heat_tail_p0)) (Set.Ioi 0) := by
    apply Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
    have : (0 : ℝ) ≤ prime_heat_tail_p0 := by
      norm_num [prime_heat_tail_p0]
    nlinarith
  have hanti :
      AntitoneOn (fun x : ℝ => x ^ (-prime_heat_tail_p0))
        (Set.Icc (prime_cert_heat_N : ℝ) (prime_cert_heat_N + m)) := by
    refine hanti'.mono ?_
    intro x hx
    have hpos : (0 : ℝ) < (prime_cert_heat_N : ℝ) := by
      norm_num [prime_cert_heat_N]
    exact lt_of_lt_of_le hpos hx.1
  have hsum_le :
      (∑ i ∈ Finset.range m,
          (i + prime_heat_tail_N0 : ℝ) ^ (-prime_heat_tail_p0)) ≤
        ∫ x in (prime_cert_heat_N : ℝ)..(prime_cert_heat_N + m), x ^ (-prime_heat_tail_p0) := by
    have h := (AntitoneOn.sum_le_integral
      (x₀ := (prime_cert_heat_N : ℝ)) (a := m)
      (f := fun x : ℝ => x ^ (-prime_heat_tail_p0)) hanti)
    simpa [prime_heat_tail_N0, add_assoc, add_comm, add_left_comm] using h
  -- bound the integral using rpow formula
  have h_integral :
      (∫ x in (prime_cert_heat_N : ℝ)..(prime_cert_heat_N + m), x ^ (-prime_heat_tail_p0)) =
        (((prime_cert_heat_N + m : ℝ)) ^ (1 - prime_heat_tail_p0) -
          (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0)) /
          (1 - prime_heat_tail_p0) := by
    have hne : (-prime_heat_tail_p0 : ℝ) ≠ -1 := by
      norm_num [prime_heat_tail_p0]
    have h0 : (0 : ℝ) ∉ Set.uIcc (prime_cert_heat_N : ℝ) (prime_cert_heat_N + m : ℝ) := by
      intro hmem
      have hpos : (0 : ℝ) < (prime_cert_heat_N : ℝ) := by
        norm_num [prime_cert_heat_N]
      have hab : (prime_cert_heat_N : ℝ) ≤ (prime_cert_heat_N + m : ℝ) := by
        nlinarith
      have hmem' :
          (0 : ℝ) ∈ Set.Icc (prime_cert_heat_N : ℝ) (prime_cert_heat_N + m : ℝ) := by
        simpa [Set.uIcc_of_le hab] using hmem
      exact (not_le_of_gt hpos) hmem'.1
    have hcond : (-1 : ℝ) < (-prime_heat_tail_p0) ∨
        (-prime_heat_tail_p0) ≠ -1 ∧
          (0 : ℝ) ∉ Set.uIcc (prime_cert_heat_N : ℝ) (prime_cert_heat_N + m : ℝ) := by
      right; exact ⟨hne, h0⟩
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (integral_rpow (a := (prime_cert_heat_N : ℝ))
        (b := (prime_cert_heat_N + m : ℝ)) (r := -prime_heat_tail_p0) hcond)
  have hpow_le :
      (prime_cert_heat_N + m : ℝ) ^ (1 - prime_heat_tail_p0) ≤
        (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) := by
    have hpos : (0 : ℝ) < (prime_cert_heat_N : ℝ) := by
      norm_num [prime_cert_heat_N]
    have hbase : (prime_cert_heat_N : ℝ) ≤ (prime_cert_heat_N + m : ℝ) := by
      nlinarith
    have h_exp_nonpos : (1 - prime_heat_tail_p0 : ℝ) ≤ 0 := by
      norm_num [prime_heat_tail_p0]
    -- exponent nonpositive => rpow is antitone in base
    exact Real.rpow_le_rpow_of_exponent_nonpos hpos hbase h_exp_nonpos
  have h_integral_le :
      ∫ x in (prime_cert_heat_N : ℝ)..(prime_cert_heat_N + m), x ^ (-prime_heat_tail_p0) ≤
        (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) /
          (prime_heat_tail_p0 - 1) := by
    have hden_neg : (1 - prime_heat_tail_p0 : ℝ) < 0 := by
      norm_num [prime_heat_tail_p0]
    have hden' : (prime_heat_tail_p0 - 1 : ℝ) = -(1 - prime_heat_tail_p0) := by
      ring
    have hb_nonneg :
        0 ≤ (prime_cert_heat_N + m : ℝ) ^ (1 - prime_heat_tail_p0) := by
      have hbase_nonneg : 0 ≤ (prime_cert_heat_N + m : ℝ) := by nlinarith
      exact Real.rpow_nonneg hbase_nonneg _
    have hdiff :
        -(prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) ≤
          (prime_cert_heat_N + m : ℝ) ^ (1 - prime_heat_tail_p0) -
            (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) := by
      nlinarith [hb_nonneg]
    calc
      ∫ x in (prime_cert_heat_N : ℝ)..(prime_cert_heat_N + m), x ^ (-prime_heat_tail_p0)
          = (((prime_cert_heat_N + m : ℝ)) ^ (1 - prime_heat_tail_p0) -
              (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0)) /
              (1 - prime_heat_tail_p0) := h_integral
      _ ≤ (-(prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0)) / (1 - prime_heat_tail_p0) := by
            exact (div_le_div_of_nonpos_of_le (le_of_lt hden_neg) hdiff)
      _ = (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) /
            (prime_heat_tail_p0 - 1) := by
            have hden'' : (1 - prime_heat_tail_p0 : ℝ) = -(prime_heat_tail_p0 - 1) := by
              ring
            calc
              (-(prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0)) /
                  (1 - prime_heat_tail_p0)
                  = (-(prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0)) /
                      (-(prime_heat_tail_p0 - 1)) := by
                        rw [hden'']
              _ = (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) /
                    (prime_heat_tail_p0 - 1) := by
                        simpa using
                          (neg_div_neg_eq ((prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0))
                            (prime_heat_tail_p0 - 1))
  exact hsum_le.trans h_integral_le

lemma prime_heat_tail_bound :
    ∑' n, prime_heat_weight_term (n + (prime_cert_heat_N + 1)) ≤
      prime_cert_heat_tail_bound := by
  have hnonneg : ∀ n, 0 ≤ prime_heat_weight_term (n + (prime_cert_heat_N + 1)) := by
    intro n
    have hw_nonneg : 0 ≤ w_Q (n + (prime_cert_heat_N + 1)) := by
      simpa using (w_Q_nonneg (n + (prime_cert_heat_N + 1)))
    have h_exp_nonneg :
        0 ≤ Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n (n + (prime_cert_heat_N + 1))) ^ 2) :=
      Real.exp_nonneg _
    have hxi_nonneg : 0 ≤ |xi_n (n + (prime_cert_heat_N + 1))| := abs_nonneg _
    have hmul_nonneg :
        0 ≤ w_Q (n + (prime_cert_heat_N + 1)) *
          (Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n (n + (prime_cert_heat_N + 1))) ^ 2) *
            |xi_n (n + (prime_cert_heat_N + 1))|) := by
      exact mul_nonneg hw_nonneg (mul_nonneg h_exp_nonneg hxi_nonneg)
    have h_ind_nonneg :
        0 ≤
          (if |xi_n (n + (prime_cert_heat_N + 1))| ≤ prime_cert_B_max then (1 : ℝ) else 0) := by
      by_cases h : |xi_n (n + (prime_cert_heat_N + 1))| ≤ prime_cert_B_max <;> simp [h]
    simpa [prime_heat_weight_term, mul_comm, mul_left_comm, mul_assoc] using
      mul_nonneg hmul_nonneg h_ind_nonneg
  have hsum_le :
      ∀ m, (∑ i ∈ Finset.range m,
        prime_heat_weight_term (i + (prime_cert_heat_N + 1))) ≤
          prime_cert_heat_tail_bound := by
    intro m
    have hle_sum :
        (∑ i ∈ Finset.range m,
          prime_heat_weight_term (i + (prime_cert_heat_N + 1))) ≤
          ∑ i ∈ Finset.range m,
            prime_heat_tail_term (i + (prime_cert_heat_N + 1)) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      simpa [prime_heat_tail_N0, add_comm, add_left_comm, add_assoc] using
        prime_heat_weight_term_shift_le_tail_term i
    have hle :
        (∑ i ∈ Finset.range m,
          prime_heat_weight_term (i + (prime_cert_heat_N + 1))) ≤
          prime_heat_tail_coeff *
            (∑ i ∈ Finset.range m,
              (i + prime_heat_tail_N0 : ℝ) ^ (-prime_heat_tail_p0)) := by
      have hle_sum' :
          (∑ i ∈ Finset.range m,
              prime_heat_tail_term (i + (prime_cert_heat_N + 1))) ≤
            ∑ i ∈ Finset.range m,
              prime_heat_tail_coeff *
                (i + prime_heat_tail_N0 : ℝ) ^ (-prime_heat_tail_p0) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hm : prime_heat_tail_N0 ≤ i + prime_heat_tail_N0 := by
          exact Nat.le_add_left _ _
        have h := prime_heat_tail_term_le_rpow_p0 (m := i + prime_heat_tail_N0) hm
        simpa [prime_heat_tail_N0, add_comm, add_left_comm, add_assoc, prime_heat_tail_coeff,
          mul_comm, mul_left_comm, mul_assoc] using h
      have hle'' :
          (∑ i ∈ Finset.range m,
              prime_heat_tail_coeff *
                (i + prime_heat_tail_N0 : ℝ) ^ (-prime_heat_tail_p0)) =
            prime_heat_tail_coeff *
              (∑ i ∈ Finset.range m,
                (i + prime_heat_tail_N0 : ℝ) ^ (-prime_heat_tail_p0)) := by
        simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using rfl
      calc
        (∑ i ∈ Finset.range m,
          prime_heat_weight_term (i + (prime_cert_heat_N + 1))) ≤
            ∑ i ∈ Finset.range m,
              prime_heat_tail_term (i + (prime_cert_heat_N + 1)) := hle_sum
        _ ≤ ∑ i ∈ Finset.range m,
              prime_heat_tail_coeff *
                (i + prime_heat_tail_N0 : ℝ) ^ (-prime_heat_tail_p0) := hle_sum'
        _ = prime_heat_tail_coeff *
              (∑ i ∈ Finset.range m,
                (i + prime_heat_tail_N0 : ℝ) ^ (-prime_heat_tail_p0)) := hle''
    have hsum_rpow :=
      prime_heat_tail_rpow_sum_le m
    have hpow_le :
        (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) ≤
          (10 : ℝ) ^ (-7 : ℝ) := by
      -- (10^6)^(1-p0) = 10^(6*(1-p0)) with 6*(1-p0) = -7.5 ≤ -7
      have h10pos : (1 : ℝ) ≤ (10 : ℝ) := by norm_num
      have hmul :
          (6 : ℝ) * (1 - prime_heat_tail_p0) ≤ (-7 : ℝ) := by
        norm_num [prime_heat_tail_p0]
      have hpow :
          (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) =
            (10 : ℝ) ^ ((6 : ℝ) * (1 - prime_heat_tail_p0)) := by
        have h10 : (prime_cert_heat_N : ℝ) = (10 : ℝ) ^ (6 : ℕ) := by
          norm_num [prime_cert_heat_N]
        calc
          (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0)
              = ((10 : ℝ) ^ (6 : ℕ)) ^ (1 - prime_heat_tail_p0) := by
                  simpa [h10]
          _ = (10 : ℝ) ^ ((6 : ℝ) * (1 - prime_heat_tail_p0)) := by
                  simpa [mul_comm] using
                    (Real.rpow_natCast_mul (x := (10 : ℝ)) (n := 6)
                      (z := (1 - prime_heat_tail_p0)) (by norm_num)).symm
      have hmono :
          (10 : ℝ) ^ ((6 : ℝ) * (1 - prime_heat_tail_p0)) ≤
            (10 : ℝ) ^ (-7 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le h10pos hmul
      simpa [hpow] using hmono
    have hconst_le :
        (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) /
            (prime_heat_tail_p0 - 1) ≤ (1 / 10000000 : ℝ) * (4 / 5 : ℝ) := by
      -- (p0-1)=5/4, and 10^-7 /(5/4) = 4/5 * 10^-7
      have hden : (prime_heat_tail_p0 - 1 : ℝ) = (5 / 4 : ℝ) := by
        norm_num [prime_heat_tail_p0]
      have hten : (10 : ℝ) ^ (-7 : ℝ) = (1 / 10000000 : ℝ) := by
        have hpos : (0 : ℝ) ≤ (10 : ℝ) := by norm_num
        calc
          (10 : ℝ) ^ (-7 : ℝ) = ((10 : ℝ) ^ (7 : ℝ))⁻¹ := by
            simpa using (Real.rpow_neg (x := (10 : ℝ)) (hx := hpos) (y := (7 : ℝ)))
          _ = ((10 : ℝ) ^ (7 : ℕ))⁻¹ := by
            simp [Real.rpow_natCast]
          _ = (1 / 10000000 : ℝ) := by
            norm_num
      have hpow' :
          (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) ≤ (1 / 10000000 : ℝ) := by
        simpa [hten] using hpow_le
      calc
        (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) /
            (prime_heat_tail_p0 - 1)
            = (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) / (5 / 4 : ℝ) := by
                  simpa [hden]
        _ = (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) * ((5 / 4 : ℝ))⁻¹ := by
                  simp [div_eq_mul_inv]
        _ = (prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) * (4 / 5 : ℝ) := by
                  have hfrac : ((5 / 4 : ℝ))⁻¹ = (4 / 5 : ℝ) := by
                    norm_num
                  simpa [hfrac]
        _ ≤ (1 / 10000000 : ℝ) * (4 / 5 : ℝ) := by
                  have hnonneg : 0 ≤ (4 / 5 : ℝ) := by norm_num
                  exact mul_le_mul_of_nonneg_right hpow' hnonneg
    have hcoeff :
        prime_heat_tail_coeff * ((1 / 10000000 : ℝ) * (4 / 5 : ℝ)) ≤
          prime_cert_heat_tail_bound := by
      -- prime_heat_tail_coeff = 100/3, prime_cert_heat_tail_bound = 3e-6
      have hcoeff_q :
          (100 / 3 : ℚ) * ((1 / 10000000 : ℚ) * (4 / 5 : ℚ)) ≤ (3 / 1000000 : ℚ) := by
        norm_num
      have hcoeff_r := (Rat.cast_le (K := ℝ)).2 hcoeff_q
      simpa [prime_heat_tail_coeff, prime_cert_heat_tail_bound] using hcoeff_r
    have hcoeff_nonneg : 0 ≤ prime_heat_tail_coeff := by
      norm_num [prime_heat_tail_coeff]
    calc
      (∑ i ∈ Finset.range m,
          prime_heat_weight_term (i + (prime_cert_heat_N + 1))) ≤
          prime_heat_tail_coeff *
            (∑ i ∈ Finset.range m,
              (i + prime_heat_tail_N0 : ℝ) ^ (-prime_heat_tail_p0)) := hle
      _ ≤ prime_heat_tail_coeff *
            ((prime_cert_heat_N : ℝ) ^ (1 - prime_heat_tail_p0) /
              (prime_heat_tail_p0 - 1)) := by
            exact mul_le_mul_of_nonneg_left hsum_rpow hcoeff_nonneg
      _ ≤ prime_heat_tail_coeff * ((1 / 10000000 : ℝ) * (4 / 5 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hconst_le hcoeff_nonneg
      _ ≤ prime_cert_heat_tail_bound := hcoeff
  exact Real.tsum_le_of_sum_range_le hnonneg hsum_le

end Q3.Proofs.PrimeCert
