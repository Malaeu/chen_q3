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

/-! ### Coarse analytic tail bound (provable without interval arithmetic) -/

def prime_b_grid_tail_eps : ℝ := (1 / 10 : ℝ)

def prime_b_grid_tail_p0 : ℝ := (47 / 20 : ℝ)

def prime_b_grid_tail_coeff : ℝ := (20 : ℝ)

lemma prime_b_grid_tail_p0_le :
    prime_b_grid_tail_p0 ≤
      t_critical * Real.log (prime_b_grid_tail_N0 : ℝ) + (2 / 5 : ℝ) := by
  have hlog : (13 : ℝ) ≤ Real.log (prime_b_grid_tail_N0 : ℝ) :=
    prime_b_grid_tail_log_N0_ge_13
  have ht : t_critical = (3 / 20 : ℝ) := by
    simp [t_critical]
  -- 13 * (3/20) + 2/5 = 47/20
  have h' : (47 / 20 : ℝ) ≤
      t_critical * Real.log (prime_b_grid_tail_N0 : ℝ) + (2 / 5 : ℝ) := by
    nlinarith [hlog, ht]
  simpa [prime_b_grid_tail_p0] using h'

lemma prime_b_grid_tail_term_le_rpow_p0 {m : ℕ} (hm : prime_b_grid_tail_N0 ≤ m) :
    prime_b_grid_tail_term m ≤
      prime_b_grid_tail_coeff * (m : ℝ) ^ (-prime_b_grid_tail_p0) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    have hN0_pos : 0 < prime_b_grid_tail_N0 := by
      norm_num [prime_b_grid_tail_N0, prime_cert_N]
    have hm_pos_nat : 0 < m := lt_of_lt_of_le hN0_pos hm
    exact_mod_cast hm_pos_nat
  have hlog_le :
      Real.log (m : ℝ) ≤ (m : ℝ) ^ prime_b_grid_tail_eps / prime_b_grid_tail_eps := by
    -- log n ≤ n^ε / ε
    simpa [prime_b_grid_tail_eps] using
      (Real.log_natCast_le_rpow_div m (by norm_num : (0 : ℝ) < (1 / 10 : ℝ)))
  have hlog_mul :
      (2 : ℝ) * Real.log (m : ℝ) ≤
        prime_b_grid_tail_coeff * (m : ℝ) ^ prime_b_grid_tail_eps := by
    -- 2 * log m ≤ (2/eps) * m^eps (coarse)
    have hlog_le' :
        Real.log (m : ℝ) ≤ (10 : ℝ) * (m : ℝ) ^ prime_b_grid_tail_eps := by
      simpa [prime_b_grid_tail_eps, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        hlog_le
    have h' :=
      (mul_le_mul_of_nonneg_left hlog_le' (by norm_num : (0 : ℝ) ≤ 2))
    have hcoeff : prime_b_grid_tail_coeff = (2 : ℝ) * 10 := by
      norm_num [prime_b_grid_tail_coeff]
    simpa [hcoeff, mul_assoc, mul_left_comm, mul_comm] using h'
  have hsqrt_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos
  have hfactor :
      (2 * Real.log (m : ℝ)) / Real.sqrt (m : ℝ) ≤
        prime_b_grid_tail_coeff * (m : ℝ) ^ prime_b_grid_tail_eps / Real.sqrt (m : ℝ) := by
    exact (div_le_div_of_nonneg_right hlog_mul (le_of_lt hsqrt_pos))
  have hsqrt : Real.sqrt (m : ℝ) = (m : ℝ) ^ (1 / 2 : ℝ) := by
    simpa [one_div] using (Real.sqrt_eq_rpow (m : ℝ))
  have hdiv :
      (m : ℝ) ^ prime_b_grid_tail_eps / Real.sqrt (m : ℝ) =
        (m : ℝ) ^ (prime_b_grid_tail_eps - (1 / 2 : ℝ)) := by
    have hm_pos' : 0 < (m : ℝ) := hm_pos
    -- x^(y - z) = x^y / x^z
    have h := (Real.rpow_sub (x := (m : ℝ)) (y := prime_b_grid_tail_eps)
      (z := (1 / 2 : ℝ)) hm_pos')
    -- rearrange
    simpa [hsqrt] using h.symm
  have hfactor' :
      (2 * Real.log (m : ℝ)) / Real.sqrt (m : ℝ) ≤
        prime_b_grid_tail_coeff * (m : ℝ) ^ (prime_b_grid_tail_eps - (1 / 2 : ℝ)) := by
    simpa [hdiv, mul_div_assoc] using hfactor
  have hfactor'' :
      (2 * Real.log (m : ℝ)) / Real.sqrt (m : ℝ) ≤
        prime_b_grid_tail_coeff * (m : ℝ) ^ (-(2 / 5 : ℝ)) := by
    -- eps = 1/10, so eps - 1/2 = -2/5
    have h_eps : prime_b_grid_tail_eps - (2⁻¹ : ℝ) = (-(2 / 5 : ℝ)) := by
      norm_num [prime_b_grid_tail_eps]
    simpa [h_eps] using hfactor'
  have hexp_le := prime_b_grid_tail_exp_le_rpow (m := m) hm
  have hnonneg1 : 0 ≤ prime_b_grid_tail_coeff * (m : ℝ) ^ (-(2 / 5 : ℝ)) := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hrpow_nonneg :
        0 ≤ (m : ℝ) ^ (-(2 / 5 : ℝ)) := Real.rpow_nonneg hm_nonneg _
    have hcoeff_nonneg : 0 ≤ prime_b_grid_tail_coeff := by
      norm_num [prime_b_grid_tail_coeff]
    exact mul_nonneg hcoeff_nonneg hrpow_nonneg
  have hmul :
      ((2 * Real.log (m : ℝ)) / Real.sqrt (m : ℝ)) *
          Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) ≤
        prime_b_grid_tail_coeff * (m : ℝ) ^ (-(2 / 5 : ℝ)) *
          (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))) := by
    exact mul_le_mul hfactor'' hexp_le (Real.exp_nonneg _) hnonneg1
  have hcombine :
      (m : ℝ) ^ (-(2 / 5 : ℝ)) *
          (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))) =
        (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ) + (2 / 5 : ℝ))) := by
    have hm_pos' : 0 < (m : ℝ) := hm_pos
    -- x^a * x^b = x^(a + b)
    simpa [add_comm, add_left_comm, add_assoc] using
      (Real.rpow_add (x := (m : ℝ)) hm_pos'
        (-(2 / 5 : ℝ)) (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ)))).symm
  have hpow_le :
      (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ) + (2 / 5 : ℝ))) ≤
        (m : ℝ) ^ (-prime_b_grid_tail_p0) := by
    have hm_one_nat : (1 : ℕ) ≤ m := by
      have hN0_one : (1 : ℕ) ≤ prime_b_grid_tail_N0 := by
        norm_num [prime_b_grid_tail_N0, prime_cert_N]
      exact le_trans hN0_one hm
    have hm_one : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hm_one_nat
    have h_exp_le :
        -(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ) + (2 / 5 : ℝ)) ≤
          -prime_b_grid_tail_p0 := by
      have h := prime_b_grid_tail_p0_le
      nlinarith [h]
    exact Real.rpow_le_rpow_of_exponent_le hm_one h_exp_le
  calc
    prime_b_grid_tail_term m
        = ((2 * Real.log (m : ℝ)) / Real.sqrt (m : ℝ)) *
            Real.exp (-t_critical * (Real.log (m : ℝ)) ^ 2) := by
            simp [prime_b_grid_tail_term, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ prime_b_grid_tail_coeff * (m : ℝ) ^ (-(2 / 5 : ℝ)) *
          (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ))) := hmul
    _ = prime_b_grid_tail_coeff *
          (m : ℝ) ^ (-(t_critical * Real.log (prime_b_grid_tail_N0 : ℝ) + (2 / 5 : ℝ))) := by
            simp [hcombine, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ prime_b_grid_tail_coeff * (m : ℝ) ^ (-prime_b_grid_tail_p0) := by
            exact mul_le_mul_of_nonneg_left hpow_le (by norm_num [prime_b_grid_tail_coeff])

lemma prime_b_grid_tail_rpow_sum_le (m : ℕ) :
    (∑ i ∈ Finset.range m,
        (i + prime_b_grid_tail_N0 : ℝ) ^ (-prime_b_grid_tail_p0)) ≤
      (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) /
        (prime_b_grid_tail_p0 - 1) := by
  -- compare to integral of x^(-p0)
  have hanti' :
      AntitoneOn (fun x : ℝ => x ^ (-prime_b_grid_tail_p0)) (Set.Ioi 0) := by
    apply Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
    have : (0 : ℝ) ≤ prime_b_grid_tail_p0 := by
      norm_num [prime_b_grid_tail_p0]
    nlinarith
  have hanti :
      AntitoneOn (fun x : ℝ => x ^ (-prime_b_grid_tail_p0))
        (Set.Icc (prime_cert_N : ℝ) (prime_cert_N + m)) := by
    refine hanti'.mono ?_
    intro x hx
    have hpos : (0 : ℝ) < (prime_cert_N : ℝ) := by
      norm_num [prime_cert_N]
    exact lt_of_lt_of_le hpos hx.1
  have hsum_le :
      (∑ i ∈ Finset.range m,
          (i + prime_b_grid_tail_N0 : ℝ) ^ (-prime_b_grid_tail_p0)) ≤
        ∫ x in (prime_cert_N : ℝ)..(prime_cert_N + m), x ^ (-prime_b_grid_tail_p0) := by
    have h := (AntitoneOn.sum_le_integral
      (x₀ := (prime_cert_N : ℝ)) (a := m)
      (f := fun x : ℝ => x ^ (-prime_b_grid_tail_p0)) hanti)
    simpa [prime_b_grid_tail_N0, add_assoc, add_comm, add_left_comm] using h
  -- bound the integral using rpow formula
  have h_integral :
      (∫ x in (prime_cert_N : ℝ)..(prime_cert_N + m), x ^ (-prime_b_grid_tail_p0)) =
        (((prime_cert_N + m : ℝ)) ^ (1 - prime_b_grid_tail_p0) -
          (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0)) /
          (1 - prime_b_grid_tail_p0) := by
    have hne : (-prime_b_grid_tail_p0 : ℝ) ≠ -1 := by
      norm_num [prime_b_grid_tail_p0]
    have h0 : (0 : ℝ) ∉ Set.uIcc (prime_cert_N : ℝ) (prime_cert_N + m : ℝ) := by
      intro hmem
      have hpos : (0 : ℝ) < (prime_cert_N : ℝ) := by
        norm_num [prime_cert_N]
      have hab : (prime_cert_N : ℝ) ≤ (prime_cert_N + m : ℝ) := by
        nlinarith
      have hmem' :
          (0 : ℝ) ∈ Set.Icc (prime_cert_N : ℝ) (prime_cert_N + m : ℝ) := by
        simpa [Set.uIcc_of_le hab] using hmem
      exact (not_le_of_gt hpos) hmem'.1
    have hcond : (-1 : ℝ) < (-prime_b_grid_tail_p0) ∨
        (-prime_b_grid_tail_p0) ≠ -1 ∧
          (0 : ℝ) ∉ Set.uIcc (prime_cert_N : ℝ) (prime_cert_N + m : ℝ) := by
      right; exact ⟨hne, h0⟩
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (integral_rpow (a := (prime_cert_N : ℝ))
        (b := (prime_cert_N + m : ℝ)) (r := -prime_b_grid_tail_p0) hcond)
  have hpow_le :
      (prime_cert_N + m : ℝ) ^ (1 - prime_b_grid_tail_p0) ≤
        (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) := by
    have hpos : (0 : ℝ) < (prime_cert_N : ℝ) := by
      norm_num [prime_cert_N]
    have hbase : (prime_cert_N : ℝ) ≤ (prime_cert_N + m : ℝ) := by
      nlinarith
    have h_exp_nonpos : (1 - prime_b_grid_tail_p0 : ℝ) ≤ 0 := by
      norm_num [prime_b_grid_tail_p0]
    -- exponent nonpositive => rpow is antitone in base
    exact Real.rpow_le_rpow_of_exponent_nonpos hpos hbase h_exp_nonpos
  have h_integral_le :
      ∫ x in (prime_cert_N : ℝ)..(prime_cert_N + m), x ^ (-prime_b_grid_tail_p0) ≤
        (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) /
          (prime_b_grid_tail_p0 - 1) := by
    have hden_neg : (1 - prime_b_grid_tail_p0 : ℝ) < 0 := by
      norm_num [prime_b_grid_tail_p0]
    have hden' : (prime_b_grid_tail_p0 - 1 : ℝ) = -(1 - prime_b_grid_tail_p0) := by
      ring
    have hb_nonneg :
        0 ≤ (prime_cert_N + m : ℝ) ^ (1 - prime_b_grid_tail_p0) := by
      have hbase_nonneg : 0 ≤ (prime_cert_N + m : ℝ) := by nlinarith
      exact Real.rpow_nonneg hbase_nonneg _
    have hdiff :
        -(prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) ≤
          (prime_cert_N + m : ℝ) ^ (1 - prime_b_grid_tail_p0) -
            (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) := by
      nlinarith [hb_nonneg]
    calc
      ∫ x in (prime_cert_N : ℝ)..(prime_cert_N + m), x ^ (-prime_b_grid_tail_p0)
          = (((prime_cert_N + m : ℝ)) ^ (1 - prime_b_grid_tail_p0) -
              (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0)) /
              (1 - prime_b_grid_tail_p0) := h_integral
      _ ≤ (-(prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0)) / (1 - prime_b_grid_tail_p0) := by
            exact (div_le_div_of_nonpos_of_le (le_of_lt hden_neg) hdiff)
      _ = (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) /
            (prime_b_grid_tail_p0 - 1) := by
            have hden'' : (1 - prime_b_grid_tail_p0 : ℝ) = -(prime_b_grid_tail_p0 - 1) := by
              ring
            calc
              (-(prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0)) /
                  (1 - prime_b_grid_tail_p0)
                  = (-(prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0)) /
                      (-(prime_b_grid_tail_p0 - 1)) := by
                        rw [hden'']
              _ = (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) /
                    (prime_b_grid_tail_p0 - 1) := by
                        simpa using
                          (neg_div_neg_eq ((prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0))
                            (prime_b_grid_tail_p0 - 1))
  exact hsum_le.trans h_integral_le

lemma prime_b_grid_tail_term_sum_le_bound :
    ∑' n, prime_b_grid_tail_term (n + prime_b_grid_tail_N0) ≤
      prime_b_grid_tail_bound := by
  have hnonneg : ∀ n, 0 ≤ prime_b_grid_tail_term (n + prime_b_grid_tail_N0) := by
    intro n
    have hm : prime_b_grid_tail_N0 ≤ n + prime_b_grid_tail_N0 := by
      exact Nat.le_add_left _ _
    have hlog_nonneg : 0 ≤ Real.log (n + prime_b_grid_tail_N0 : ℝ) := by
      simpa using (Real.log_natCast_nonneg (n + prime_b_grid_tail_N0))
    have hsqrt_nonneg : 0 ≤ Real.sqrt (n + prime_b_grid_tail_N0 : ℝ) := by
      exact Real.sqrt_nonneg _
    have hexp_nonneg :
        0 ≤ Real.exp (-t_critical * (Real.log (n + prime_b_grid_tail_N0 : ℝ)) ^ 2) :=
      Real.exp_nonneg _
    have hmul_nonneg :
        0 ≤ (2 * Real.log (n + prime_b_grid_tail_N0 : ℝ)) / Real.sqrt
            (n + prime_b_grid_tail_N0 : ℝ) := by
      exact div_nonneg (mul_nonneg (by norm_num) hlog_nonneg) hsqrt_nonneg
    simpa [prime_b_grid_tail_term, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_nonneg hmul_nonneg hexp_nonneg
  have hsum_le :
      ∀ m, (∑ i ∈ Finset.range m,
        prime_b_grid_tail_term (i + prime_b_grid_tail_N0)) ≤
          prime_b_grid_tail_bound := by
    intro m
    have hle_sum :
        (∑ i ∈ Finset.range m,
          prime_b_grid_tail_term (i + prime_b_grid_tail_N0)) ≤
          ∑ i ∈ Finset.range m,
            prime_b_grid_tail_coeff *
              (i + prime_b_grid_tail_N0 : ℝ) ^ (-prime_b_grid_tail_p0) := by
      -- pointwise comparison
      refine Finset.sum_le_sum ?_
      intro i hi
      have hm : prime_b_grid_tail_N0 ≤ i + prime_b_grid_tail_N0 := by
        exact Nat.le_add_left _ _
      have h := prime_b_grid_tail_term_le_rpow_p0 (m := i + prime_b_grid_tail_N0) hm
      simpa [prime_b_grid_tail_coeff, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using h
    have hle :
        (∑ i ∈ Finset.range m,
          prime_b_grid_tail_term (i + prime_b_grid_tail_N0)) ≤
          prime_b_grid_tail_coeff *
            (∑ i ∈ Finset.range m,
              (i + prime_b_grid_tail_N0 : ℝ) ^ (-prime_b_grid_tail_p0)) := by
      simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hle_sum
    have hsum_rpow :=
      prime_b_grid_tail_rpow_sum_le m
    have hsum_rpow' :
        prime_b_grid_tail_coeff *
            (∑ i ∈ Finset.range m,
              (i + prime_b_grid_tail_N0 : ℝ) ^ (-prime_b_grid_tail_p0)) ≤
          prime_b_grid_tail_bound := by
      -- bound the rpow sum by a numeric constant
      have h1 :
          (∑ i ∈ Finset.range m,
              (i + prime_b_grid_tail_N0 : ℝ) ^ (-prime_b_grid_tail_p0)) ≤
            (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) /
              (prime_b_grid_tail_p0 - 1) := hsum_rpow
      have hpow_le :
          (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) ≤
            (10 : ℝ) ^ (-8 : ℝ) := by
        -- (10^6)^(1-p0) = 10^(6*(1-p0)) with 6*(1-p0) = -8.1 ≤ -8
        have h10pos : (1 : ℝ) ≤ (10 : ℝ) := by norm_num
        have hmul :
            (6 : ℝ) * (1 - prime_b_grid_tail_p0) ≤ (-8 : ℝ) := by
          norm_num [prime_b_grid_tail_p0]
        have hpow :
            (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) =
              (10 : ℝ) ^ ((6 : ℝ) * (1 - prime_b_grid_tail_p0)) := by
          -- rewrite prime_cert_N as 10^6 and use rpow_natCast_mul
          have h10 : (prime_cert_N : ℝ) = (10 : ℝ) ^ (6 : ℕ) := by
            norm_num [prime_cert_N]
          calc
            (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0)
                = ((10 : ℝ) ^ (6 : ℕ)) ^ (1 - prime_b_grid_tail_p0) := by
                    simpa [h10]
            _ = (10 : ℝ) ^ ((6 : ℝ) * (1 - prime_b_grid_tail_p0)) := by
                    simpa [mul_comm] using
                      (Real.rpow_natCast_mul (x := (10 : ℝ)) (n := 6)
                        (z := (1 - prime_b_grid_tail_p0)) (by norm_num)).symm
        -- use monotonicity in the exponent
        have hmono :
            (10 : ℝ) ^ ((6 : ℝ) * (1 - prime_b_grid_tail_p0)) ≤
              (10 : ℝ) ^ (-8 : ℝ) := by
          exact Real.rpow_le_rpow_of_exponent_le h10pos hmul
        simpa [hpow] using hmono
      have hconst_le :
          (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) /
              (prime_b_grid_tail_p0 - 1) ≤ (1 / 100000000 : ℝ) * (20 / 27 : ℝ) := by
        -- (p0-1)=27/20, so divide by it and use hpow_le
        have hden : (prime_b_grid_tail_p0 - 1 : ℝ) = (27 / 20 : ℝ) := by
          norm_num [prime_b_grid_tail_p0]
        have hten : (10 : ℝ) ^ (-8 : ℝ) = (1 / 100000000 : ℝ) := by
          have hpos : (0 : ℝ) ≤ (10 : ℝ) := by norm_num
          calc
            (10 : ℝ) ^ (-8 : ℝ) = ((10 : ℝ) ^ (8 : ℝ))⁻¹ := by
              simpa using (Real.rpow_neg (x := (10 : ℝ)) (hx := hpos) (y := (8 : ℝ)))
            _ = ((10 : ℝ) ^ (8 : ℕ))⁻¹ := by
              simp [Real.rpow_natCast]
            _ = (1 / 100000000 : ℝ) := by
              norm_num
        have hpow' :
            (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) ≤ (1 / 100000000 : ℝ) := by
          simpa [hten] using hpow_le
        -- multiply by 20/27
        calc
          (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) /
              (prime_b_grid_tail_p0 - 1)
              = (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) / (27 / 20 : ℝ) := by
                    simpa [hden]
          _ = (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) * ((27 / 20 : ℝ))⁻¹ := by
                    simp [div_eq_mul_inv]
          _ = (prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) * (20 / 27 : ℝ) := by
                    have hfrac : ((27 / 20 : ℝ))⁻¹ = (20 / 27 : ℝ) := by
                      norm_num
                    simpa [hfrac]
          _ ≤ (1 / 100000000 : ℝ) * (20 / 27 : ℝ) := by
                    have hnonneg : 0 ≤ (20 / 27 : ℝ) := by norm_num
                    exact mul_le_mul_of_nonneg_right hpow' hnonneg
      have hcoeff :
          prime_b_grid_tail_coeff * ((1 / 100000000 : ℝ) * (20 / 27 : ℝ)) ≤
            prime_b_grid_tail_bound := by
        -- prime_b_grid_tail_coeff = 20, prime_b_grid_tail_bound = 2e-7
        have hcoeff_q :
            (20 : ℚ) * ((1 / 100000000 : ℚ) * (20 / 27 : ℚ)) ≤
              prime_b_grid_tail_bound_q := by
          norm_num [prime_b_grid_tail_bound_q]
        have hcoeff_r := (Rat.cast_le (K := ℝ)).2 hcoeff_q
        simpa [prime_b_grid_tail_coeff, prime_b_grid_tail_bound] using hcoeff_r
      have hcoeff_nonneg : 0 ≤ prime_b_grid_tail_coeff := by
        norm_num [prime_b_grid_tail_coeff]
      calc
        prime_b_grid_tail_coeff *
            (∑ i ∈ Finset.range m,
              (i + prime_b_grid_tail_N0 : ℝ) ^ (-prime_b_grid_tail_p0))
            ≤ prime_b_grid_tail_coeff *
              ((prime_cert_N : ℝ) ^ (1 - prime_b_grid_tail_p0) /
                (prime_b_grid_tail_p0 - 1)) := by
                    exact mul_le_mul_of_nonneg_left h1 hcoeff_nonneg
        _ ≤ prime_b_grid_tail_coeff * ((1 / 100000000 : ℝ) * (20 / 27 : ℝ)) := by
                    exact mul_le_mul_of_nonneg_left hconst_le hcoeff_nonneg
        _ ≤ prime_b_grid_tail_bound := hcoeff
    exact hle.trans hsum_rpow'
  exact Real.tsum_le_of_sum_range_le hnonneg hsum_le

end Q3.Proofs.PrimeCert
