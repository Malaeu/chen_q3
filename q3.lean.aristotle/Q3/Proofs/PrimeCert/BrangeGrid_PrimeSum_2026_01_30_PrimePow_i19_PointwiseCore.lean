import Mathlib
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSumTail
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_PrimePow_i19_AllBuckets_Check
import Q3.Proofs.PrimeCert.IntervalPilot

set_option maxHeartbeats 0

/-!
Pointwise helper core for `i = 19` prime-power upper bounds.

This module provides a reusable analytic envelope:
- upper bound `log p` via `log(p^k) / k`;
- upper bound heat factor with a lower log bound;
- upper bound Fejér factor with a lower log bound and an upper bound for `pi`.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

def prime_b_grid_i19_B : ℝ := (49 : ℝ) / 10

lemma prime_b_grid_i19_B_eq :
    prime_b_grid prime_b_grid_i19 = prime_b_grid_i19_B := by
  norm_num [prime_b_grid, prime_b_grid_i19_B, B_min, prime_cert_B_h, prime_b_grid_i19]

lemma prime_b_grid_i19_B_pos : 0 < prime_b_grid_i19_B := by
  norm_num [prime_b_grid_i19_B]

def prime_b_grid_pp_envelope_ub (u r exp_ub fejer_ub : ℝ) (k : ℕ) : ℝ :=
  ((2 * (u / (k : ℝ))) / r) * exp_ub * fejer_ub

lemma prime_b_grid_weight_term_eq_prime_pow
    (i : Fin prime_b_grid_size) (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    prime_b_grid_weight_term i (p ^ k) =
      ((2 * Real.log p) / Real.sqrt ((p ^ k : ℕ) : ℝ)) *
        (Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2) *
          max (0 : ℝ) (1 - |xi_n (p ^ k)| / prime_b_grid i)) := by
  have hk' : k ≠ 0 := Nat.ne_of_gt hk
  simp [prime_b_grid_weight_term, Q3.w_Q,
    ArithmeticFunction.vonMangoldt_apply_pow hk',
    ArithmeticFunction.vonMangoldt_apply_prime hp,
    phi_shift, fejer_heat_window,
    mul_comm, mul_left_comm, mul_assoc]

lemma prime_b_grid_weight_term_i19_le_pp_envelope_of_prime_pow_bounds
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {l u r exp_ub pi_ub fejer_ub : ℝ}
    (hl0 : 0 ≤ l) (hu0 : 0 ≤ u)
    (hlog_l : l ≤ Real.log ((p ^ k : ℕ) : ℝ))
    (hlog_u : Real.log ((p ^ k : ℕ) : ℝ) ≤ u)
    (hr0 : 0 < r) (hsqrt : r ^ 2 ≤ ((p ^ k : ℕ) : ℝ))
    (hexp : Real.exp (-t_critical * l ^ 2) ≤ exp_ub)
    (hpi_pos : 0 < pi_ub) (hpi : Real.pi ≤ pi_ub)
    (hfejer :
      max (0 : ℝ) (1 - l / (2 * pi_ub * prime_b_grid_i19_B)) ≤ fejer_ub) :
    prime_b_grid_weight_term prime_b_grid_i19 (p ^ k) ≤
      prime_b_grid_pp_envelope_ub (u := u) (r := r)
        (exp_ub := exp_ub) (fejer_ub := fejer_ub) (k := k) := by
  have hB_eq : prime_b_grid prime_b_grid_i19 = prime_b_grid_i19_B :=
    prime_b_grid_i19_B_eq
  have hB_pos : 0 < prime_b_grid prime_b_grid_i19 := by
    simpa [hB_eq] using prime_b_grid_i19_B_pos
  have hlog_nonneg : 0 ≤ Real.log ((p ^ k : ℕ) : ℝ) := by
    simpa using (Real.log_natCast_nonneg (p ^ k))
  have h2pi_pos : 0 < (2 * Real.pi : ℝ) := by
    nlinarith [Real.pi_pos]
  have hxi_nonneg : 0 ≤ xi_n (p ^ k) := by
    exact div_nonneg hlog_nonneg (le_of_lt h2pi_pos)
  have hxi_abs : |xi_n (p ^ k)| = Real.log ((p ^ k : ℕ) : ℝ) / (2 * Real.pi) := by
    calc
      |xi_n (p ^ k)| = xi_n (p ^ k) := abs_of_nonneg hxi_nonneg
      _ = Real.log ((p ^ k : ℕ) : ℝ) / (2 * Real.pi) := by rfl
  have hpow' :
      -4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2 =
        -t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2 := by
    calc
      -4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2
          = -t_critical * (4 * Real.pi ^ 2 * (xi_n (p ^ k)) ^ 2) := by
              ring
      _ = -t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2 := by
              simp [xi_n_sq_scaled]
  have hterm_eq :
      prime_b_grid_weight_term prime_b_grid_i19 (p ^ k) =
        ((2 * Real.log p) / Real.sqrt ((p ^ k : ℕ) : ℝ)) *
          Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) *
          max (0 : ℝ) (1 - Real.log ((p ^ k : ℕ) : ℝ) /
            (2 * Real.pi * prime_b_grid prime_b_grid_i19)) := by
    calc
      prime_b_grid_weight_term prime_b_grid_i19 (p ^ k)
          = ((2 * Real.log p) / Real.sqrt ((p ^ k : ℕ) : ℝ)) *
              (Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2) *
                max (0 : ℝ) (1 - |xi_n (p ^ k)| / prime_b_grid prime_b_grid_i19)) := by
                simpa using
                  (prime_b_grid_weight_term_eq_prime_pow
                    (i := prime_b_grid_i19) (p := p) (k := k) hp hk)
      _ = ((2 * Real.log p) / Real.sqrt ((p ^ k : ℕ) : ℝ)) *
            (Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) *
              max (0 : ℝ) (1 - Real.log ((p ^ k : ℕ) : ℝ) /
                (2 * Real.pi * prime_b_grid prime_b_grid_i19))) := by
              have hpow'' :
                  Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2) =
                    Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) := by
                exact congrArg Real.exp hpow'
              have hfej :
                  max (0 : ℝ) (1 - |xi_n (p ^ k)| / prime_b_grid prime_b_grid_i19) =
                    max (0 : ℝ) (1 - Real.log ((p ^ k : ℕ) : ℝ) /
                      (2 * Real.pi * prime_b_grid prime_b_grid_i19)) := by
                rw [hxi_abs]
                ring_nf
              rw [hpow'', hfej]
      _ = ((2 * Real.log p) / Real.sqrt ((p ^ k : ℕ) : ℝ)) *
            Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) *
            max (0 : ℝ) (1 - Real.log ((p ^ k : ℕ) : ℝ) /
              (2 * Real.pi * prime_b_grid prime_b_grid_i19)) := by
              ring
  have hterm_le :
      prime_b_grid_weight_term prime_b_grid_i19 (p ^ k) ≤
        ((2 * Real.log p) / Real.sqrt ((p ^ k : ℕ) : ℝ)) *
          Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) *
          max (0 : ℝ) (1 - Real.log ((p ^ k : ℕ) : ℝ) /
            (2 * Real.pi * prime_b_grid prime_b_grid_i19)) := by
    simpa [hterm_eq]
  have hlogp_le : Real.log (p : ℝ) ≤ u / (k : ℝ) :=
    log_nat_pow_le_div (p := p) (k := k) hk hlog_u
  have hmul2 : 2 * Real.log (p : ℝ) ≤ 2 * (u / (k : ℝ)) := by
    nlinarith [hlogp_le]
  have hA1 :
      (2 * Real.log (p : ℝ)) / Real.sqrt ((p ^ k : ℕ) : ℝ) ≤
        (2 * (u / (k : ℝ))) / Real.sqrt ((p ^ k : ℕ) : ℝ) := by
    have hden : 0 ≤ Real.sqrt ((p ^ k : ℕ) : ℝ) := Real.sqrt_nonneg _
    exact div_le_div_of_nonneg_right hmul2 hden
  have hsqrt' : r ≤ Real.sqrt ((p ^ k : ℕ) : ℝ) := by
    exact Real.le_sqrt_of_sq_le hsqrt
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hdiv_nonneg : 0 ≤ u / (k : ℝ) := by
    exact div_nonneg hu0 (le_of_lt hk')
  have hnum_nonneg : 0 ≤ 2 * (u / (k : ℝ)) := by
    nlinarith [hdiv_nonneg]
  have hA2 :
      (2 * (u / (k : ℝ))) / Real.sqrt ((p ^ k : ℕ) : ℝ) ≤
        (2 * (u / (k : ℝ))) / r := by
    exact div_le_div_of_nonneg_left hnum_nonneg hr0 hsqrt'
  have hA :
      (2 * Real.log (p : ℝ)) / Real.sqrt ((p ^ k : ℕ) : ℝ) ≤
        (2 * (u / (k : ℝ))) / r := by
    exact hA1.trans hA2
  have ht : 0 ≤ t_critical := by norm_num [t_critical]
  have hB :
      Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) ≤ exp_ub := by
    have hB' :
        Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) ≤
          Real.exp (-t_critical * l ^ 2) := by
      exact exp_neg_t_log_sq_le_of_log_lower
        (t := t_critical) (a := l) (n := p ^ k) ht hl0 hlog_l
    exact hB'.trans hexp
  have hden_pi_pos : 0 < 2 * Real.pi * prime_b_grid prime_b_grid_i19 := by
    nlinarith [Real.pi_pos, hB_pos]
  have hden_ub_pos : 0 < 2 * pi_ub * prime_b_grid prime_b_grid_i19 := by
    nlinarith [hpi_pos, hB_pos]
  have hden_le :
      2 * Real.pi * prime_b_grid prime_b_grid_i19 ≤
        2 * pi_ub * prime_b_grid prime_b_grid_i19 := by
    nlinarith [hpi, hB_pos]
  have hfejer_ratio_lb :
      l / (2 * pi_ub * prime_b_grid prime_b_grid_i19) ≤
        Real.log ((p ^ k : ℕ) : ℝ) / (2 * Real.pi * prime_b_grid prime_b_grid_i19) := by
    have hlow_den :
        l / (2 * pi_ub * prime_b_grid prime_b_grid_i19) ≤
          l / (2 * Real.pi * prime_b_grid prime_b_grid_i19) := by
      exact div_le_div_of_nonneg_left hl0 hden_pi_pos hden_le
    have hnum :
        l / (2 * Real.pi * prime_b_grid prime_b_grid_i19) ≤
          Real.log ((p ^ k : ℕ) : ℝ) / (2 * Real.pi * prime_b_grid prime_b_grid_i19) := by
      exact div_le_div_of_nonneg_right hlog_l (le_of_lt hden_pi_pos)
    exact hlow_den.trans hnum
  have hfejer_inner :
      1 - Real.log ((p ^ k : ℕ) : ℝ) /
          (2 * Real.pi * prime_b_grid prime_b_grid_i19) ≤
        1 - l / (2 * pi_ub * prime_b_grid prime_b_grid_i19) := by
    linarith [hfejer_ratio_lb]
  have hC :
      max (0 : ℝ) (1 - Real.log ((p ^ k : ℕ) : ℝ) /
          (2 * Real.pi * prime_b_grid prime_b_grid_i19)) ≤
        fejer_ub := by
    have hC1 :
        max (0 : ℝ) (1 - Real.log ((p ^ k : ℕ) : ℝ) /
          (2 * Real.pi * prime_b_grid prime_b_grid_i19)) ≤
          max (0 : ℝ) (1 - l / (2 * pi_ub * prime_b_grid prime_b_grid_i19)) := by
      exact max_le_max le_rfl hfejer_inner
    have hC2 :
        max (0 : ℝ) (1 - l / (2 * pi_ub * prime_b_grid prime_b_grid_i19)) ≤
          max (0 : ℝ) (1 - l / (2 * pi_ub * prime_b_grid_i19_B)) := by
      simpa [hB_eq]
    exact (hC1.trans hC2).trans hfejer
  have hA_nonneg :
      0 ≤ (2 * Real.log (p : ℝ)) / Real.sqrt ((p ^ k : ℕ) : ℝ) := by
    have hlogp_nonneg : 0 ≤ Real.log (p : ℝ) := by
      simpa using (Real.log_natCast_nonneg p)
    have hnum_nonneg' : 0 ≤ 2 * Real.log (p : ℝ) := by
      nlinarith [hlogp_nonneg]
    exact div_nonneg hnum_nonneg' (Real.sqrt_nonneg _)
  have hB_nonneg :
      0 ≤ Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) := Real.exp_nonneg _
  have hA'_nonneg :
      0 ≤ (2 * (u / (k : ℝ))) / r := by
    exact div_nonneg hnum_nonneg (le_of_lt hr0)
  have hC'_nonneg : 0 ≤ fejer_ub := by
    have h0 : 0 ≤ max (0 : ℝ) (1 - l / (2 * pi_ub * prime_b_grid_i19_B)) := by
      exact le_max_left _ _
    exact le_trans h0 hfejer
  have hmul :=
    mul_mul_mul_le_mul_mul_mul hA hB hC hA_nonneg hB_nonneg hA'_nonneg hC'_nonneg
  calc
    prime_b_grid_weight_term prime_b_grid_i19 (p ^ k) ≤
        ((2 * Real.log (p : ℝ)) / Real.sqrt ((p ^ k : ℕ) : ℝ)) *
          Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) *
          max (0 : ℝ) (1 - Real.log ((p ^ k : ℕ) : ℝ) /
            (2 * Real.pi * prime_b_grid prime_b_grid_i19)) := hterm_le
    _ ≤ ((2 * (u / (k : ℝ))) / r) * exp_ub * fejer_ub := hmul
    _ = prime_b_grid_pp_envelope_ub (u := u) (r := r)
          (exp_ub := exp_ub) (fejer_ub := fejer_ub) (k := k) := by
          simp [prime_b_grid_pp_envelope_ub]

lemma prime_b_grid_weight_term_i19_le_pp_ub_of_prime_pow_bounds
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {l u r exp_ub pi_ub fejer_ub : ℝ}
    (hl0 : 0 ≤ l) (hu0 : 0 ≤ u)
    (hlog_l : l ≤ Real.log ((p ^ k : ℕ) : ℝ))
    (hlog_u : Real.log ((p ^ k : ℕ) : ℝ) ≤ u)
    (hr0 : 0 < r) (hsqrt : r ^ 2 ≤ ((p ^ k : ℕ) : ℝ))
    (hexp : Real.exp (-t_critical * l ^ 2) ≤ exp_ub)
    (hpi_pos : 0 < pi_ub) (hpi : Real.pi ≤ pi_ub)
    (hfejer :
      max (0 : ℝ) (1 - l / (2 * pi_ub * prime_b_grid_i19_B)) ≤ fejer_ub)
    (hub :
      prime_b_grid_pp_envelope_ub (u := u) (r := r)
        (exp_ub := exp_ub) (fejer_ub := fejer_ub) (k := k) ≤
          prime_b_grid_pp_i19_all_ub (p ^ k)) :
    prime_b_grid_weight_term prime_b_grid_i19 (p ^ k) ≤
      prime_b_grid_pp_i19_all_ub (p ^ k) := by
  exact (prime_b_grid_weight_term_i19_le_pp_envelope_of_prime_pow_bounds
    (p := p) (k := k) hp hk hl0 hu0 hlog_l hlog_u hr0 hsqrt
    hexp hpi_pos hpi hfejer).trans hub

end Q3.Proofs.PrimeCert
