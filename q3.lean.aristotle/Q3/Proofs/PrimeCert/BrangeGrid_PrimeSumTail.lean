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

end Q3.Proofs.PrimeCert
