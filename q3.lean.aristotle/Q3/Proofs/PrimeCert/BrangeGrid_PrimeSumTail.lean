import Mathlib
import Q3.Basic.Defs
import Q3.Proofs.Params_Critical
import Q3.Proofs.ShiftedWindows
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.BrangeGrid_2046

/-!
Scaffold: split the prime-term sum into a finite partial sum plus a tail bound.
This mirrors the heat-cert scaffolding and isolates the analytic tail proof.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

open Q3

def prime_b_grid_weight_term (i : Fin prime_b_grid_size) (n : ℕ) : ℝ :=
  w_Q n * phi_shift (prime_b_grid i) t_critical 0 (xi_n n)

def prime_b_grid_prime_sum_up_to (i : Fin prime_b_grid_size) : ℝ :=
  (Finset.range (prime_cert_N + 1)).sum (fun n => prime_b_grid_weight_term i n)

def prime_b_grid_tail_term (n : ℕ) : ℝ :=
  (2 * Real.log n / Real.sqrt n) * Real.exp (-t_critical * (Real.log n) ^ 2)

lemma prime_b_grid_pos (i : Fin prime_b_grid_size) : 0 < prime_b_grid i := by
  have hBmin : 0 < B_min := by
    norm_num [B_min]
  have hstep : 0 ≤ (i.1 : ℝ) * prime_cert_B_h := by
    have hstep' : 0 ≤ prime_cert_B_h := by
      norm_num [prime_cert_B_h]
    exact mul_nonneg (Nat.cast_nonneg _) hstep'
  have hBmin_le : B_min ≤ prime_b_grid i := by
    dsimp [prime_b_grid]
    linarith
  exact lt_of_lt_of_le hBmin hBmin_le

lemma xi_n_sq_scaled (n : ℕ) : 4 * Real.pi ^ 2 * (xi_n n) ^ 2 = (Real.log n) ^ 2 := by
  have hpi : (Real.pi : ℝ) ≠ 0 := by
    exact Real.pi_ne_zero
  -- expand xi_n and clear denominators
  simp [xi_n, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  field_simp [hpi]
  ring

lemma prime_b_grid_weight_term_le_tail_term (i : Fin prime_b_grid_size) (n : ℕ) :
    prime_b_grid_weight_term i n ≤ prime_b_grid_tail_term n := by
  have hΛ : (ArithmeticFunction.vonMangoldt n) ≤ Real.log (n : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log
  have hmul : (2 : ℝ) * ArithmeticFunction.vonMangoldt n ≤ (2 : ℝ) * Real.log (n : ℝ) := by
    exact mul_le_mul_of_nonneg_left hΛ (by norm_num)
  have hden : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have h_w : w_Q n ≤ (2 * Real.log (n : ℝ)) / Real.sqrt n := by
    unfold w_Q
    exact div_le_div_of_nonneg_right hmul hden
  have hBpos : 0 < prime_b_grid i := prime_b_grid_pos i
  have hdiv_nonneg : 0 ≤ |xi_n n| / prime_b_grid i := by
    exact div_nonneg (abs_nonneg _) (le_of_lt hBpos)
  have hmax_le : max (0 : ℝ) (1 - |xi_n n| / prime_b_grid i) ≤ 1 := by
    have h1 : 1 - |xi_n n| / prime_b_grid i ≤ 1 := by
      linarith
    exact max_le_iff.mpr ⟨by norm_num, h1⟩
  have h_exp :
      Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) =
        Real.exp (-t_critical * (Real.log n) ^ 2) := by
    have hpow :
        4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2 =
          t_critical * (Real.log n) ^ 2 := by
      calc
        4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2
            = t_critical * (4 * Real.pi ^ 2 * (xi_n n) ^ 2) := by
                ring
        _ = t_critical * (Real.log n) ^ 2 := by
                simp [xi_n_sq_scaled]
    have hpow' :
        -4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2 =
          -t_critical * (Real.log n) ^ 2 := by
      calc
        -4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2
            = -(4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) := by
                ring
        _ = -(t_critical * (Real.log n) ^ 2) := by
                simp [hpow]
        _ = -t_critical * (Real.log n) ^ 2 := by
                ring
    simpa [hpow']
  have h_phi :
      phi_shift (prime_b_grid i) t_critical 0 (xi_n n) ≤
        Real.exp (-t_critical * (Real.log n) ^ 2) := by
    -- fejer factor ≤ 1
    have hmax :
        max (0 : ℝ) (1 - |xi_n n| / prime_b_grid i) *
          Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) ≤
        1 * Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hmax_le (Real.exp_nonneg _)
    have hphi_def :
        phi_shift (prime_b_grid i) t_critical 0 (xi_n n) =
          max (0 : ℝ) (1 - |xi_n n| / prime_b_grid i) *
            Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) := by
      simp [phi_shift, fejer_heat_window]
    calc
      phi_shift (prime_b_grid i) t_critical 0 (xi_n n)
          = max (0 : ℝ) (1 - |xi_n n| / prime_b_grid i) *
              Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) := hphi_def
      _ ≤ 1 * Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) := hmax
      _ = Real.exp (-t_critical * (Real.log n) ^ 2) := by
            simpa [one_mul] using h_exp
  have h_w_nonneg : 0 ≤ (2 * Real.log (n : ℝ)) / Real.sqrt n := by
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      simpa using (Real.log_natCast_nonneg n)
    exact div_nonneg (mul_nonneg (by norm_num) hlog_nonneg) (Real.sqrt_nonneg _)
  have h_phi_nonneg : 0 ≤ phi_shift (prime_b_grid i) t_critical 0 (xi_n n) := by
    simpa [phi_shift] using
      (fejer_heat_window_nonneg (B := prime_b_grid i) (t := t_critical) (ξ := xi_n n))
  calc
    prime_b_grid_weight_term i n
        = w_Q n * phi_shift (prime_b_grid i) t_critical 0 (xi_n n) := by
            simp [prime_b_grid_weight_term]
    _ ≤ ((2 * Real.log (n : ℝ)) / Real.sqrt n) *
          Real.exp (-t_critical * (Real.log n) ^ 2) := by
            exact mul_le_mul h_w h_phi h_phi_nonneg h_w_nonneg
    _ = prime_b_grid_tail_term n := by
          simp [prime_b_grid_tail_term]

lemma prime_b_grid_tsum_eq_sum_add_tsum_nat_add
    (i : Fin prime_b_grid_size)
    (hsum : Summable (prime_b_grid_weight_term i)) :
    (∑' n, prime_b_grid_weight_term i n) =
      prime_b_grid_prime_sum_up_to i +
        ∑' n, prime_b_grid_weight_term i (n + (prime_cert_N + 1)) := by
  have h := (hsum.sum_add_tsum_nat_add (prime_cert_N + 1)).symm
  simpa [prime_b_grid_prime_sum_up_to, Finset.sum_range] using h

lemma prime_b_grid_prime_term_le_prime_ub_of_sum_tail
    (i : Fin prime_b_grid_size)
    (hsum : Summable (prime_b_grid_weight_term i))
    (h_sum :
      prime_b_grid_prime_sum_up_to i ≤ prime_b_grid_prime_sum i)
    (h_tail :
      ∑' n, prime_b_grid_weight_term i (n + (prime_cert_N + 1)) ≤
        prime_b_grid_tail_bound) :
    prime_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ) ≤
      prime_b_grid_prime_ub i := by
  have hsplit := prime_b_grid_tsum_eq_sum_add_tsum_nat_add i hsum
  calc
    prime_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ)
        = ∑' n, prime_b_grid_weight_term i n := by
            simp [prime_term, prime_b_grid_weight_term]
    _ = prime_b_grid_prime_sum_up_to i +
          ∑' n, prime_b_grid_weight_term i (n + (prime_cert_N + 1)) := hsplit
    _ ≤ prime_b_grid_prime_sum i + prime_b_grid_tail_bound := by
          exact add_le_add h_sum h_tail
    _ ≤ prime_b_grid_prime_ub i := by
          exact prime_b_grid_prime_sum_add_tail_le_prime_ub i

/-! ### Tail bound reduction to the pure tail term -/

lemma prime_b_grid_weight_term_shift_le_tail_term
    (i : Fin prime_b_grid_size) (n : ℕ) :
    prime_b_grid_weight_term i (n + (prime_cert_N + 1)) ≤
      prime_b_grid_tail_term (n + (prime_cert_N + 1)) := by
  simpa using prime_b_grid_weight_term_le_tail_term i (n + (prime_cert_N + 1))

lemma prime_b_grid_tail_bound_of_tail_term
    (i : Fin prime_b_grid_size)
    (hsum : Summable (prime_b_grid_weight_term i))
    (hsum_tail : Summable (fun n => prime_b_grid_tail_term (n + (prime_cert_N + 1))))
    (h_tail :
      ∑' n, prime_b_grid_tail_term (n + (prime_cert_N + 1)) ≤
        prime_b_grid_tail_bound) :
    ∑' n, prime_b_grid_weight_term i (n + (prime_cert_N + 1)) ≤
      prime_b_grid_tail_bound := by
  have hsum_shift :
      Summable (fun n => prime_b_grid_weight_term i (n + (prime_cert_N + 1))) := by
    exact (summable_nat_add_iff (f := fun n => prime_b_grid_weight_term i n)
      (prime_cert_N + 1)).2 hsum
  have hle :
      ∑' n, prime_b_grid_weight_term i (n + (prime_cert_N + 1)) ≤
        ∑' n, prime_b_grid_tail_term (n + (prime_cert_N + 1)) := by
    exact Summable.tsum_le_tsum
      (fun n => prime_b_grid_weight_term_shift_le_tail_term i n)
      hsum_shift hsum_tail
  exact hle.trans h_tail

/-! ### Tail term summability (coarse p-series comparison) -/

def prime_b_grid_tail_N0 : ℕ := prime_cert_N + 1

lemma prime_b_grid_tail_N0_pos : (0 : ℝ) < (prime_b_grid_tail_N0 : ℝ) := by
  norm_num [prime_b_grid_tail_N0, prime_cert_N]

lemma prime_b_grid_tail_log_N0_ge_13 :
    (13 : ℝ) ≤ Real.log (prime_b_grid_tail_N0 : ℝ) := by
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
  have hpow_lt : (2.7182818286 : ℝ) ^ (13 : ℕ) < (prime_b_grid_tail_N0 : ℝ) := by
    norm_num [prime_b_grid_tail_N0, prime_cert_N]
  have h_exp13_le' : Real.exp (13 : ℝ) ≤ (prime_b_grid_tail_N0 : ℝ) :=
    le_trans h_exp13_le (le_of_lt hpow_lt)
  have hlog_le := Real.log_le_log (Real.exp_pos 13) h_exp13_le'
  simpa using hlog_le

lemma prime_b_grid_tail_exp_le_rpow
    {m : ℕ} (hm : prime_b_grid_tail_N0 ≤ m) :
    Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) ≤
      (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    have hN0_pos_nat : 0 < prime_b_grid_tail_N0 := by
      norm_num [prime_b_grid_tail_N0, prime_cert_N]
    have hm_pos_nat : 0 < m := lt_of_lt_of_le hN0_pos_nat hm
    exact_mod_cast hm_pos_nat
  have hlog_m_nonneg : 0 ≤ Real.log (m : ℝ) := by
    simpa using (Real.log_natCast_nonneg m)
  have hlog_N0_le : Real.log (prime_b_grid_tail_N0 : ℝ) ≤ Real.log (m : ℝ) := by
    have hN0_pos : (0 : ℝ) < (prime_b_grid_tail_N0 : ℝ) := prime_b_grid_tail_N0_pos
    have hN0_le : (prime_b_grid_tail_N0 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hm
    exact Real.log_le_log hN0_pos hN0_le
  have ht_nonneg : 0 ≤ t_critical := by
    norm_num [t_critical]
  have hmul : t_critical * Real.log (prime_b_grid_tail_N0 : ℝ) ≤
      t_critical * Real.log (m : ℝ) := by
    exact mul_le_mul_of_nonneg_left hlog_N0_le ht_nonneg
  have hmul' : (t_critical * Real.log (prime_b_grid_tail_N0 : ℝ)) * Real.log (m : ℝ) ≤
      (t_critical * Real.log (m : ℝ)) * Real.log (m : ℝ) := by
    exact mul_le_mul_of_nonneg_right hmul hlog_m_nonneg
  have hneg :
      -t_critical * (Real.log (m : ℝ)) ^ 2 ≤
        -(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ)) * Real.log (m : ℝ) := by
    have hmul'' :
        t_critical * (Real.log (m : ℝ)) ^ 2 ≥
          (t_critical * Real.log (prime_b_grid_tail_N0 : ℝ)) * Real.log (m : ℝ) := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul'
    nlinarith
  have hexp' :
      Real.exp (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ)) * Real.log (m : ℝ)) =
        (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))) := by
    have h := (Real.rpow_def_of_pos hm_pos (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h.symm
  calc
    Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2)
        ≤ Real.exp (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ)) * Real.log (m : ℝ)) := by
            exact (Real.exp_le_exp).2 hneg
    _ = (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))) := hexp'

def prime_b_grid_tail_p : ℝ :=
  t_critical * Real.log (prime_b_grid_tail_N0 : ℝ) - (1 / 2 : ℝ)

lemma prime_b_grid_tail_p_gt_one : 1 < prime_b_grid_tail_p := by
  have hlog : (13 : ℝ) ≤ Real.log (prime_b_grid_tail_N0 : ℝ) :=
    prime_b_grid_tail_log_N0_ge_13
  have ht : t_critical = (3 / 20 : ℝ) := by
    simp [t_critical]
  have hmul : (39 / 20 : ℝ) ≤ t_critical * Real.log (prime_b_grid_tail_N0 : ℝ) := by
    -- 13 * (3/20) = 39/20
    nlinarith [hlog, ht]
  have : (29 / 20 : ℝ) ≤ prime_b_grid_tail_p := by
    -- subtract 1/2 from both sides
    dsimp [prime_b_grid_tail_p]
    nlinarith [hmul]
  nlinarith

lemma prime_b_grid_tail_term_le_rpow
    {m : ℕ} (hm : prime_b_grid_tail_N0 ≤ m) :
    prime_b_grid_tail_term m ≤ 2 * (m : ℝ) ^ (-prime_b_grid_tail_p) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    have hN0_pos_nat : 0 < prime_b_grid_tail_N0 := by
      norm_num [prime_b_grid_tail_N0, prime_cert_N]
    have hm_pos_nat : 0 < m := lt_of_lt_of_le hN0_pos_nat hm
    exact_mod_cast hm_pos_nat
  have hlog_nonneg : 0 ≤ Real.log (m : ℝ) := by
    simpa using (Real.log_natCast_nonneg m)
  have hlog_le : Real.log (m : ℝ) ≤ (m : ℝ) := by
    exact Real.log_le_self (by exact_mod_cast (Nat.zero_le m))
  have hfactor :
      (2 * Real.log (m : ℝ)) / Real.sqrt (m : ℝ) ≤
        2 * Real.sqrt (m : ℝ) := by
    have hmul : (2 : ℝ) * Real.log (m : ℝ) ≤ (2 : ℝ) * (m : ℝ) := by
      exact mul_le_mul_of_nonneg_left hlog_le (by norm_num)
    have hsqrt_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos
    -- multiply by sqrt m > 0 and use sqrt_mul_self
    have hmul' :
        (2 : ℝ) * Real.log (m : ℝ) ≤ (2 : ℝ) * Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) := by
      have hsq_nonneg : (0 : ℝ) ≤ m := by
        exact_mod_cast (Nat.zero_le m)
      have hsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := by
        simpa using (Real.mul_self_sqrt hsq_nonneg)
      nlinarith [hmul, hsq]
    exact (div_le_iff₀ hsqrt_pos).2 hmul'
  have hexp_le := prime_b_grid_tail_exp_le_rpow (m := m) hm
  have hfirst_nonneg : 0 ≤ (2 * Real.log (m : ℝ)) / Real.sqrt (m : ℝ) := by
    exact div_nonneg (mul_nonneg (by norm_num) hlog_nonneg) (Real.sqrt_nonneg _)
  have hmul1 :
      (2 * Real.log (m : ℝ)) / Real.sqrt (m : ℝ) *
          Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) ≤
        (2 * Real.log (m : ℝ)) / Real.sqrt (m : ℝ) *
          (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))) := by
    exact mul_le_mul_of_nonneg_left hexp_le hfirst_nonneg
  have hrpow_nonneg :
      0 ≤ (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))) := by
    exact Real.rpow_nonneg (le_of_lt hm_pos) _
  have hmul2 :
      (2 * Real.log (m : ℝ)) / Real.sqrt (m : ℝ) *
          (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))) ≤
        (2 * Real.sqrt (m : ℝ)) *
          (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))) := by
    exact mul_le_mul_of_nonneg_right hfactor hrpow_nonneg
  have hrpow_simp :
      (2 * Real.sqrt (m : ℝ)) *
          (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))) =
        2 * (m : ℝ) ^ (-prime_b_grid_tail_p) := by
    have hpos : 0 < (m : ℝ) := hm_pos
    -- sqrt m = m^(1/2), combine rpow exponents
    have hsqrt : Real.sqrt (m : ℝ) = (m : ℝ) ^ (2⁻¹ : ℝ) := by
      simpa [one_div] using (Real.sqrt_eq_rpow (m : ℝ))
    -- combine exponents
    have hmul :
        (m : ℝ) ^ ((2⁻¹ : ℝ) + (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ)))) =
          (m : ℝ) ^ (2⁻¹ : ℝ) *
            (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))) := by
      simpa using
        (Real.rpow_add (x := (m : ℝ)) hpos (2⁻¹ : ℝ)
          (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))))
    calc
      (2 * Real.sqrt (m : ℝ)) *
          (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ)))
          = 2 * (Real.sqrt (m : ℝ) * (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ)))) := by
                ring
      _ = 2 * ((m : ℝ) ^ (2⁻¹ : ℝ) *
            (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ)))) := by
            simp [hsqrt]
      _ = 2 * (m : ℝ) ^ ((2⁻¹ : ℝ) + (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ)))) := by
            simp [hmul.symm]
      _ = 2 * (m : ℝ) ^ ((2⁻¹ : ℝ) - (t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))) := by
            simp [sub_eq_add_neg]
      _ = 2 * (m : ℝ) ^ (-prime_b_grid_tail_p) := by
            simp [prime_b_grid_tail_p, sub_eq_add_neg, add_comm, one_div]
  calc
    prime_b_grid_tail_term m
        = ((2 * Real.log (m : ℝ)) / Real.sqrt (m : ℝ)) *
            Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) := by
              simp [prime_b_grid_tail_term, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ (2 * Real.log (m : ℝ)) / Real.sqrt (m : ℝ) *
          (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))) := hmul1
    _ ≤ (2 * Real.sqrt (m : ℝ)) *
          (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))) := hmul2
    _ = 2 * (m : ℝ) ^ (-prime_b_grid_tail_p) := hrpow_simp

lemma prime_b_grid_tail_term_summable :
    Summable (fun n => prime_b_grid_tail_term (n + prime_b_grid_tail_N0)) := by
  have hp : 1 < prime_b_grid_tail_p := prime_b_grid_tail_p_gt_one
  have hsum_rpow :
      Summable (fun n : ℕ => (n : ℝ) ^ (-prime_b_grid_tail_p)) := by
    -- p > 1 => exponent -p < -1
    have : (-prime_b_grid_tail_p) < -1 := by nlinarith
    simpa using (Real.summable_nat_rpow (p := -prime_b_grid_tail_p)).2 this
  have hsum_shift :
      Summable (fun n : ℕ => (n + prime_b_grid_tail_N0 : ℝ) ^ (-prime_b_grid_tail_p)) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-prime_b_grid_tail_p))
        prime_b_grid_tail_N0).2 hsum_rpow
  refine Summable.of_nonneg_of_le ?_ ?_ (hsum_shift.mul_left 2)
  · intro n
    have hm : prime_b_grid_tail_N0 ≤ n + prime_b_grid_tail_N0 := by
      exact Nat.le_add_left _ _
    have h_nonneg : 0 ≤ prime_b_grid_tail_term (n + prime_b_grid_tail_N0) := by
      -- all factors are nonnegative
      have hlog_nonneg : 0 ≤ Real.log (n + prime_b_grid_tail_N0 : ℝ) := by
        simpa using (Real.log_natCast_nonneg (n + prime_b_grid_tail_N0))
      have hsqrt_nonneg : 0 ≤ Real.sqrt (n + prime_b_grid_tail_N0 : ℝ) := by
        exact Real.sqrt_nonneg _
      have hexp_nonneg :
          0 ≤ Real.exp (-t_critical * (Real.log (n + prime_b_grid_tail_N0 : ℝ)) ^ 2) :=
        Real.exp_nonneg _
      have hmul_nonneg : 0 ≤ (2 * Real.log (n + prime_b_grid_tail_N0 : ℝ)) / Real.sqrt
          (n + prime_b_grid_tail_N0 : ℝ) := by
        exact div_nonneg (mul_nonneg (by norm_num) hlog_nonneg) hsqrt_nonneg
      simpa [prime_b_grid_tail_term, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        mul_nonneg hmul_nonneg hexp_nonneg
    exact h_nonneg
  · intro n
    have hm : prime_b_grid_tail_N0 ≤ n + prime_b_grid_tail_N0 := by
      exact Nat.le_add_left _ _
    have hle := prime_b_grid_tail_term_le_rpow (m := n + prime_b_grid_tail_N0) hm
    simpa [mul_comm, mul_left_comm, mul_assoc] using hle

lemma prime_b_grid_weight_term_summable (i : Fin prime_b_grid_size) :
    Summable (prime_b_grid_weight_term i) := by
  have hsum_tail :
      Summable (fun n => prime_b_grid_tail_term (n + prime_b_grid_tail_N0)) :=
    prime_b_grid_tail_term_summable
  have hsum_shift :
      Summable (fun n => prime_b_grid_weight_term i (n + prime_b_grid_tail_N0)) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hsum_tail
    · intro n
      have hw_nonneg : 0 ≤ w_Q (n + prime_b_grid_tail_N0) := by
        simpa using (w_Q_nonneg (n + prime_b_grid_tail_N0))
      have hphi_nonneg :
          0 ≤
            phi_shift (prime_b_grid i) t_critical 0 (xi_n (n + prime_b_grid_tail_N0)) := by
        simpa [phi_shift] using
          (fejer_heat_window_nonneg (B := prime_b_grid i) (t := t_critical)
            (ξ := xi_n (n + prime_b_grid_tail_N0)))
      simpa [prime_b_grid_weight_term] using mul_nonneg hw_nonneg hphi_nonneg
    · intro n
      simpa using prime_b_grid_weight_term_shift_le_tail_term i n
  exact (summable_nat_add_iff (f := fun n => prime_b_grid_weight_term i n)
    prime_b_grid_tail_N0).1 hsum_shift

end Q3.Proofs.PrimeCert
