import Mathlib
import Q3.Proofs.Params_Critical
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_BucketDefs
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_Tail
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFull
import Q3.Proofs.PrimeCert.IntervalLemmas

/-!
Pilot: small exp bound using the Taylor remainder lemma.

This is a proof-of-concept for interval-style numeric proofs without
`native_decide`. It is not imported into the main chain.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

lemma exp_one_tenth_le : Real.exp (1 / 10 : ℝ) ≤ (111 / 100 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (1 / 10 : ℝ) := by norm_num
  have hx1 : (1 / 10 : ℝ) ≤ 1 := by norm_num
  -- Reduce the Taylor bound to a rational inequality.
  -- For n=3, the RHS evaluates to 1.105222..., well below 1.11.
  have h' :
      (∑ m ∈ Finset.range 3, (1 / 10 : ℝ) ^ m / (Nat.factorial m)) +
          (1 / 10 : ℝ) ^ 3 * (3 + 1) / (Nat.factorial 3 * 3) ≤
        (111 / 100 : ℝ) := by
    norm_num
  exact exp_le_of_taylor_bound (x := (1 / 10 : ℝ)) (b := (111 / 100 : ℝ))
    hx0 hx1 (n := 3) (by decide) h'

lemma exp_sixty_nine_hundredths_le_two : Real.exp (69 / 100 : ℝ) ≤ (2 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (69 / 100 : ℝ) := by norm_num
  have hx1 : (69 / 100 : ℝ) ≤ 1 := by norm_num
  have h' :
      (∑ m ∈ Finset.range 4, (69 / 100 : ℝ) ^ m / (Nat.factorial m)) +
          (69 / 100 : ℝ) ^ 4 * (4 + 1) / (Nat.factorial 4 * 4) ≤
        (2 : ℝ) := by
    norm_num
  exact exp_le_of_taylor_bound (x := (69 / 100 : ℝ)) (b := (2 : ℝ))
    hx0 hx1 (n := 4) (by decide) h'

lemma two_le_exp_seventy_hundredths : (2 : ℝ) ≤ Real.exp (7 / 10 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (7 / 10 : ℝ) := by norm_num
  have hsum :
      (2 : ℝ) ≤ ∑ m ∈ Finset.range 4, (7 / 10 : ℝ) ^ m / (Nat.factorial m) := by
    norm_num
  have hle : ∑ m ∈ Finset.range 4, (7 / 10 : ℝ) ^ m / (Nat.factorial m) ≤
      Real.exp (7 / 10 : ℝ) := by
    simpa using (Real.sum_le_exp_of_nonneg hx0 4)
  exact le_trans hsum hle

lemma log_two_bounds :
    (69 / 100 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (7 / 10 : ℝ) := by
  have hlow : (69 / 100 : ℝ) ≤ Real.log 2 := by
    exact le_log_of_exp_le (y := (2 : ℝ)) (by norm_num) exp_sixty_nine_hundredths_le_two
  have hhigh : Real.log 2 ≤ (7 / 10 : ℝ) := by
    exact log_le_of_le_exp (x := (2 : ℝ)) (by norm_num) two_le_exp_seventy_hundredths
  exact ⟨hlow, hhigh⟩

lemma exp_one_point_zero_nine_le_three : Real.exp (109 / 100 : ℝ) ≤ (3 : ℝ) := by
  have h' :
      (∑ m ∈ Finset.range 4, (109 / 200 : ℝ) ^ m / (Nat.factorial m)) +
          (109 / 200 : ℝ) ^ 4 * (4 + 1) / (Nat.factorial 4 * 4) ≤
        (173 / 100 : ℝ) := by
    norm_num
  have hx0 : (0 : ℝ) ≤ (109 / 100 : ℝ) := by norm_num
  have hx1 : (109 / 100 : ℝ) ≤ 2 := by norm_num
  have hpow :
      Real.exp (109 / 100 : ℝ) ≤ (173 / 100 : ℝ) ^ 2 := by
    exact exp_le_pow_of_taylor_bound_div_nat
      (x := (109 / 100 : ℝ)) (b := (173 / 100 : ℝ)) (n := 2) (k := 4)
      (by decide) (by decide) hx0 hx1 (by
        have hrewrite : ((109 / 100 : ℝ) / 2) = (109 / 200 : ℝ) := by
          norm_num
        simpa [hrewrite] using h')
  have hb : (173 / 100 : ℝ) ^ 2 ≤ (3 : ℝ) := by norm_num
  exact hpow.trans hb

lemma three_le_exp_eleven_tenths : (3 : ℝ) ≤ Real.exp (11 / 10 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (11 / 10 : ℝ) := by norm_num
  have hsum :
      (3 : ℝ) ≤ ∑ m ∈ Finset.range 6, (11 / 10 : ℝ) ^ m / (Nat.factorial m) := by
    norm_num
  have hle : ∑ m ∈ Finset.range 6, (11 / 10 : ℝ) ^ m / (Nat.factorial m) ≤
      Real.exp (11 / 10 : ℝ) := by
    simpa using (Real.sum_le_exp_of_nonneg hx0 6)
  exact le_trans hsum hle

lemma log_three_bounds :
    (109 / 100 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (11 / 10 : ℝ) := by
  have hlow : (109 / 100 : ℝ) ≤ Real.log 3 := by
    exact le_log_of_exp_le (y := (3 : ℝ)) (by norm_num) exp_one_point_zero_nine_le_three
  have hhigh : Real.log 3 ≤ (11 / 10 : ℝ) := by
    exact log_le_of_le_exp (x := (3 : ℝ)) (by norm_num) three_le_exp_eleven_tenths
  exact ⟨hlow, hhigh⟩

lemma exp_one_point_six_le_five : Real.exp (8 / 5 : ℝ) ≤ (5 : ℝ) := by
  have h' :
      (∑ m ∈ Finset.range 4, (4 / 5 : ℝ) ^ m / (Nat.factorial m)) +
          (4 / 5 : ℝ) ^ 4 * (4 + 1) / (Nat.factorial 4 * 4) ≤
        (223 / 100 : ℝ) := by
    norm_num
  have hx0 : (0 : ℝ) ≤ (8 / 5 : ℝ) := by norm_num
  have hx1 : (8 / 5 : ℝ) ≤ 2 := by norm_num
  have hpow :
      Real.exp (8 / 5 : ℝ) ≤ (223 / 100 : ℝ) ^ 2 := by
    exact exp_le_pow_of_taylor_bound_div_nat
      (x := (8 / 5 : ℝ)) (b := (223 / 100 : ℝ)) (n := 2) (k := 4)
      (by decide) (by decide) hx0 hx1 (by
        have hrewrite : ((8 / 5 : ℝ) / 2) = (4 / 5 : ℝ) := by
          norm_num
        simpa [hrewrite] using h')
  have hb : (223 / 100 : ℝ) ^ 2 ≤ (5 : ℝ) := by norm_num
  exact hpow.trans hb

lemma five_le_exp_one_point_six_one : (5 : ℝ) ≤ Real.exp (161 / 100 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (161 / 100 : ℝ) := by norm_num
  have hsum :
      (5 : ℝ) ≤ ∑ m ∈ Finset.range 8, (161 / 100 : ℝ) ^ m / (Nat.factorial m) := by
    norm_num
  have hle : ∑ m ∈ Finset.range 8, (161 / 100 : ℝ) ^ m / (Nat.factorial m) ≤
      Real.exp (161 / 100 : ℝ) := by
    simpa using (Real.sum_le_exp_of_nonneg hx0 8)
  exact le_trans hsum hle

lemma log_five_bounds :
    (8 / 5 : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ (161 / 100 : ℝ) := by
  have hlow : (8 / 5 : ℝ) ≤ Real.log 5 := by
    exact le_log_of_exp_le (y := (5 : ℝ)) (by norm_num) exp_one_point_six_le_five
  have hhigh : Real.log 5 ≤ (161 / 100 : ℝ) := by
    exact log_le_of_le_exp (x := (5 : ℝ)) (by norm_num) five_le_exp_one_point_six_one
  exact ⟨hlow, hhigh⟩

def prime_heat_envelope_ub (n : ℕ) (l u : ℝ) : ℝ :=
  ((2 * u) / Real.sqrt n) * Real.exp (-t_critical * l ^ 2) * (u / (2 * Real.pi))

def prime_heat_pp_envelope_ub (u r exp_ub pi_lb : ℝ) (k : ℕ) : ℝ :=
  ((2 * (u / (k : ℝ))) / r) * exp_ub * (u / (2 * pi_lb))

lemma log_nat_pow_le_div {p k : ℕ} (hk : 0 < k) {u : ℝ}
    (hu : Real.log ((p ^ k : ℕ) : ℝ) ≤ u) :
    Real.log (p : ℝ) ≤ u / (k : ℝ) := by
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk'' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hlog_pow : Real.log ((p ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log (p : ℝ) := by
    simpa using (Real.log_pow (p : ℝ) k)
  have hmul : (k : ℝ) * Real.log (p : ℝ) ≤ u := by
    simpa [hlog_pow] using hu
  have hmul' : Real.log (p : ℝ) * (k : ℝ) ≤ u := by
    simpa [mul_comm] using hmul
  calc
    Real.log (p : ℝ) = (Real.log (p : ℝ) * (k : ℝ)) / (k : ℝ) := by
      symm
      exact mul_div_cancel_right₀ (Real.log (p : ℝ)) (b := (k : ℝ)) hk''
    _ ≤ u / (k : ℝ) := by
      exact div_le_div_of_nonneg_right hmul' (le_of_lt hk')

lemma mul_mul_mul_le_mul_mul_mul {a b c a' b' c' : ℝ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha'0 : 0 ≤ a') (hc'0 : 0 ≤ c') :
    a * b * c ≤ a' * b' * c' := by
  have h12 : a * b ≤ a' * b' := by
    have h1 : a * b ≤ a' * b := by
      exact mul_le_mul_of_nonneg_right ha hb0
    have h2 : a' * b ≤ a' * b' := by
      exact mul_le_mul_of_nonneg_left hb ha'0
    exact h1.trans h2
  have hab_nonneg : 0 ≤ a * b := mul_nonneg ha0 hb0
  have h3 : (a * b) * c ≤ (a * b) * c' := by
    exact mul_le_mul_of_nonneg_left hc hab_nonneg
  have h4 : (a * b) * c' ≤ (a' * b') * c' := by
    exact mul_le_mul_of_nonneg_right h12 hc'0
  have h34 : (a * b) * c ≤ (a' * b') * c' := h3.trans h4
  simpa [mul_assoc] using h34

lemma prime_heat_envelope_ub_le_of_bounds {n : ℕ} {l u r exp_ub pi_lb : ℝ}
    (hu0 : 0 ≤ u) (hr0 : 0 < r) (hsqrt : r ^ 2 ≤ (n : ℝ))
    (hpi_pos : 0 < pi_lb) (hpi : pi_lb ≤ Real.pi)
    (hexp : Real.exp (-t_critical * l ^ 2) ≤ exp_ub) :
    prime_heat_envelope_ub n l u ≤
      ((2 * u) / r) * exp_ub * (u / (2 * pi_lb)) := by
  have hsqrt' : r ≤ Real.sqrt n := by
    exact Real.le_sqrt_of_sq_le hsqrt
  have hA : (2 * u) / Real.sqrt n ≤ (2 * u) / r := by
    have h2u : 0 ≤ (2 * u) := by nlinarith [hu0]
    exact div_le_div_of_nonneg_left h2u hr0 hsqrt'
  have hC : u / (2 * Real.pi) ≤ u / (2 * pi_lb) := by
    have hden : 2 * pi_lb ≤ 2 * Real.pi := by nlinarith [hpi]
    exact div_le_div_of_nonneg_left hu0 (by nlinarith [hpi_pos]) hden
  have hA_nonneg : 0 ≤ (2 * u) / Real.sqrt n := by
    have h2u : 0 ≤ 2 * u := by nlinarith [hu0]
    exact div_nonneg h2u (Real.sqrt_nonneg _)
  have hB_nonneg : 0 ≤ Real.exp (-t_critical * l ^ 2) := Real.exp_nonneg _
  have hA'_nonneg : 0 ≤ (2 * u) / r := by
    have h2u : 0 ≤ 2 * u := by nlinarith [hu0]
    exact div_nonneg h2u (le_of_lt hr0)
  have hC'_nonneg : 0 ≤ u / (2 * pi_lb) := by
    have hden : 0 ≤ (2 * pi_lb : ℝ) := by linarith [hpi_pos]
    exact div_nonneg hu0 hden
  have hmul :=
    mul_mul_mul_le_mul_mul_mul hA hexp hC hA_nonneg hB_nonneg hA'_nonneg hC'_nonneg
  simpa [prime_heat_envelope_ub] using hmul

lemma prime_heat_envelope_le_of_log_bounds {n : ℕ} {l u : ℝ}
    (hl0 : 0 ≤ l) (hu0 : 0 ≤ u)
    (hl : l ≤ Real.log (n : ℝ)) (hu : Real.log (n : ℝ) ≤ u) :
    prime_heat_envelope n ≤ prime_heat_envelope_ub n l u := by
  have ht : 0 ≤ t_critical := by norm_num [t_critical]
  have hA :
      (2 * Real.log (n : ℝ)) / Real.sqrt n ≤ (2 * u) / Real.sqrt n := by
    have h1 : 2 * Real.log (n : ℝ) ≤ 2 * u := by nlinarith [hu]
    exact div_le_div_of_nonneg_right h1 (Real.sqrt_nonneg _)
  have hB :
      Real.exp (-t_critical * (Real.log (n : ℝ)) ^ 2) ≤
        Real.exp (-t_critical * l ^ 2) := by
    exact exp_neg_t_log_sq_le_of_log_lower (t := t_critical) (a := l) (n := n) ht hl0 hl
  have hC :
      Real.log (n : ℝ) / (2 * Real.pi) ≤ u / (2 * Real.pi) := by
    have hden : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
    exact div_le_div_of_nonneg_right hu hden
  have hA_nonneg : 0 ≤ (2 * Real.log (n : ℝ)) / Real.sqrt n := by
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := le_trans hl0 hl
    have h1 : 0 ≤ 2 * Real.log (n : ℝ) := by nlinarith [hlog_nonneg]
    exact div_nonneg h1 (Real.sqrt_nonneg _)
  have hB_nonneg : 0 ≤ Real.exp (-t_critical * (Real.log (n : ℝ)) ^ 2) := Real.exp_nonneg _
  have hA'_nonneg : 0 ≤ (2 * u) / Real.sqrt n := by
    have h1 : 0 ≤ 2 * u := by nlinarith [hu0]
    exact div_nonneg h1 (Real.sqrt_nonneg _)
  have hC'_nonneg : 0 ≤ u / (2 * Real.pi) := by
    have hden : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
    exact div_nonneg hu0 hden
  have hmul :=
    mul_mul_mul_le_mul_mul_mul hA hB hC hA_nonneg hB_nonneg hA'_nonneg hC'_nonneg
  simpa [prime_heat_envelope_ub, prime_heat_envelope] using hmul

lemma prime_heat_weight_term_le_pp_ub_of_prime_pow_bounds {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {l u r exp_ub pi_lb : ℝ}
    (hl0 : 0 ≤ l) (hu0 : 0 ≤ u)
    (hlog_l : l ≤ Real.log ((p ^ k : ℕ) : ℝ))
    (hlog_u : Real.log ((p ^ k : ℕ) : ℝ) ≤ u)
    (hr0 : 0 < r) (hsqrt : r ^ 2 ≤ ((p ^ k : ℕ) : ℝ))
    (hpi_pos : 0 < pi_lb) (hpi : pi_lb ≤ Real.pi)
    (hexp : Real.exp (-t_critical * l ^ 2) ≤ exp_ub)
    (hub :
      prime_heat_pp_envelope_ub (u := u) (r := r) (exp_ub := exp_ub) (pi_lb := pi_lb) (k := k) ≤
        Full.prime_heat_pp_term_ub (p ^ k)) :
    prime_heat_weight_term (p ^ k) ≤ Full.prime_heat_pp_term_ub (p ^ k) := by
  have hlog_nonneg : 0 ≤ Real.log ((p ^ k : ℕ) : ℝ) := by
    exact Real.log_natCast_nonneg (p ^ k)
  have h2pi_pos : 0 < (2 * Real.pi : ℝ) := by
    nlinarith [Real.pi_pos]
  have hxi_nonneg : 0 ≤ xi_n (p ^ k) := by
    exact div_nonneg hlog_nonneg (le_of_lt h2pi_pos)
  have hxi_abs : |xi_n (p ^ k)| = Real.log ((p ^ k : ℕ) : ℝ) / (2 * Real.pi) := by
    calc
      |xi_n (p ^ k)| = xi_n (p ^ k) := abs_of_nonneg hxi_nonneg
      _ = Real.log ((p ^ k : ℕ) : ℝ) / (2 * Real.pi) := by
        rfl
  have hpow' :
      -4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2 =
        -t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2 := by
    calc
      -4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2
          = -t_critical * (4 * Real.pi ^ 2 * (xi_n (p ^ k)) ^ 2) := by
              ring
      _ = -t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2 := by
              simp [xi_n_sq_scaled]
  have h_ind_le :
      (if |xi_n (p ^ k)| ≤ prime_cert_B_max then (1 : ℝ) else 0) ≤ 1 := by
    by_cases h : |xi_n (p ^ k)| ≤ prime_cert_B_max <;> simp [h]
  have hfactor_nonneg :
      0 ≤ ((2 * Real.log p) / Real.sqrt ((p ^ k : ℕ) : ℝ)) *
            (Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2) * |xi_n (p ^ k)|) := by
    have hlogp_nonneg : 0 ≤ Real.log (p : ℝ) := by
      simpa using (Real.log_natCast_nonneg p)
    have hnum_nonneg : 0 ≤ 2 * Real.log (p : ℝ) := by
      nlinarith [hlogp_nonneg]
    have hden_nonneg : 0 ≤ Real.sqrt ((p ^ k : ℕ) : ℝ) := Real.sqrt_nonneg _
    have hA_nonneg : 0 ≤ (2 * Real.log (p : ℝ)) / Real.sqrt ((p ^ k : ℕ) : ℝ) := by
      exact div_nonneg hnum_nonneg hden_nonneg
    have hB_nonneg :
        0 ≤ Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2) * |xi_n (p ^ k)| := by
      have hexp_nonneg :
          0 ≤ Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2) :=
        Real.exp_nonneg _
      have hxi_abs_nonneg : 0 ≤ |xi_n (p ^ k)| := abs_nonneg _
      exact mul_nonneg hexp_nonneg hxi_abs_nonneg
    exact mul_nonneg hA_nonneg hB_nonneg
  have hterm_le :
      prime_heat_weight_term (p ^ k) ≤
        ((2 * Real.log p) / Real.sqrt ((p ^ k : ℕ) : ℝ)) *
          Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) *
          (Real.log ((p ^ k : ℕ) : ℝ) / (2 * Real.pi)) := by
    calc
      prime_heat_weight_term (p ^ k)
          = ((2 * Real.log p) / Real.sqrt ((p ^ k : ℕ) : ℝ)) *
              (Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2) * |xi_n (p ^ k)|) *
              (if |xi_n (p ^ k)| ≤ prime_cert_B_max then (1 : ℝ) else 0) := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  (prime_heat_weight_term_eq_prime_pow p k hp hk)
      _ ≤ ((2 * Real.log p) / Real.sqrt ((p ^ k : ℕ) : ℝ)) *
              (Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2) * |xi_n (p ^ k)|) * 1 := by
                exact mul_le_mul_of_nonneg_left h_ind_le hfactor_nonneg
      _ = ((2 * Real.log p) / Real.sqrt ((p ^ k : ℕ) : ℝ)) *
              (Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2) * |xi_n (p ^ k)|) := by
                simp
      _ = ((2 * Real.log p) / Real.sqrt ((p ^ k : ℕ) : ℝ)) *
              (Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) *
                (Real.log ((p ^ k : ℕ) : ℝ) / (2 * Real.pi))) := by
                have hpow'' :
                    Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2) =
                      Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) := by
                  exact congrArg Real.exp hpow'
                have hinner :
                    Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2) * |xi_n (p ^ k)| =
                      Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) *
                        (Real.log ((p ^ k : ℕ) : ℝ) / (2 * Real.pi)) := by
                  calc
                    Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n (p ^ k)) ^ 2) * |xi_n (p ^ k)|
                        = Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) * |xi_n (p ^ k)| := by
                            rw [hpow'']
                    _ = Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) *
                          (Real.log ((p ^ k : ℕ) : ℝ) / (2 * Real.pi)) := by
                            rw [hxi_abs]
                rw [hinner]
      _ = ((2 * Real.log p) / Real.sqrt ((p ^ k : ℕ) : ℝ)) *
              Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) *
              (Real.log ((p ^ k : ℕ) : ℝ) / (2 * Real.pi)) := by
                ring
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
  have hB' :
      Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) ≤
        Real.exp (-t_critical * l ^ 2) := by
    exact exp_neg_t_log_sq_le_of_log_lower (t := t_critical) (a := l) (n := p ^ k) ht hl0 hlog_l
  have hB :
      Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) ≤ exp_ub := by
    exact hB'.trans hexp
  have hC1 :
      Real.log ((p ^ k : ℕ) : ℝ) / (2 * Real.pi) ≤ u / (2 * Real.pi) := by
    have hden : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
    exact div_le_div_of_nonneg_right hlog_u hden
  have hC2 :
      u / (2 * Real.pi) ≤ u / (2 * pi_lb) := by
    have hden : (2 * pi_lb : ℝ) ≤ 2 * Real.pi := by
      linarith [hpi]
    have hden_pos : 0 < (2 * pi_lb : ℝ) := by
      linarith [hpi_pos]
    exact div_le_div_of_nonneg_left hu0 hden_pos hden
  have hC :
      Real.log ((p ^ k : ℕ) : ℝ) / (2 * Real.pi) ≤ u / (2 * pi_lb) := by
    exact hC1.trans hC2
  have hA_nonneg :
      0 ≤ (2 * Real.log (p : ℝ)) / Real.sqrt ((p ^ k : ℕ) : ℝ) := by
    have hlogp_nonneg : 0 ≤ Real.log (p : ℝ) := by
      simpa using (Real.log_natCast_nonneg p)
    have hnum_nonneg' : 0 ≤ 2 * Real.log (p : ℝ) := by
      linarith [hlogp_nonneg]
    exact div_nonneg hnum_nonneg' (Real.sqrt_nonneg _)
  have hA'_nonneg :
      0 ≤ (2 * (u / (k : ℝ))) / r := by
    exact div_nonneg hnum_nonneg (le_of_lt hr0)
  have hC'_nonneg : 0 ≤ u / (2 * pi_lb) := by
    have hden : 0 ≤ (2 * pi_lb : ℝ) := by linarith [hpi_pos]
    exact div_nonneg hu0 hden
  have hmul :=
    mul_mul_mul_le_mul_mul_mul hA hB hC hA_nonneg (Real.exp_nonneg _) hA'_nonneg hC'_nonneg
  have h_ub :
      ((2 * Real.log (p : ℝ)) / Real.sqrt ((p ^ k : ℕ) : ℝ)) *
          Real.exp (-t_critical * (Real.log ((p ^ k : ℕ) : ℝ)) ^ 2) *
          (Real.log ((p ^ k : ℕ) : ℝ) / (2 * Real.pi)) ≤
        prime_heat_pp_envelope_ub (u := u) (r := r) (exp_ub := exp_ub) (pi_lb := pi_lb) (k := k) := by
    simpa [prime_heat_pp_envelope_ub] using hmul
  exact hterm_le.trans (h_ub.trans hub)

lemma prime_heat_envelope_le_of_nat_bounds {n lo hi : ℕ}
    (hlo : 0 < lo) (hlo_n : lo ≤ n) (hn_hi : n ≤ hi) :
    prime_heat_envelope n ≤
      prime_heat_envelope_ub n (Real.log (lo : ℝ)) (Real.log (hi : ℝ)) := by
  have hlog := log_nat_bounds_of_le (lo := lo) (n := n) (hi := hi) hlo hlo_n hn_hi
  have hl0 : 0 ≤ Real.log (lo : ℝ) := by
    simpa using (Real.log_natCast_nonneg lo)
  have hu0 : 0 ≤ Real.log (hi : ℝ) := by
    simpa using (Real.log_natCast_nonneg hi)
  exact prime_heat_envelope_le_of_log_bounds (n := n) (l := Real.log (lo : ℝ))
    (u := Real.log (hi : ℝ)) hl0 hu0 hlog.1 hlog.2

lemma exp_neg_t_log_sq_two_le :
    Real.exp (-t_critical * (Real.log 2) ^ 2) ≤ Real.exp (-t_critical * (69 / 100 : ℝ) ^ 2) := by
  have ht : 0 ≤ t_critical := by norm_num [t_critical]
  have ha : 0 ≤ (69 / 100 : ℝ) := by norm_num
  have hlog : (69 / 100 : ℝ) ≤ Real.log 2 := (log_two_bounds).1
  simpa using
    (exp_neg_t_log_sq_le_of_log_lower (t := t_critical) (a := (69 / 100 : ℝ)) (n := 2) ht ha
      hlog)

lemma exp_neg_t_log_sq_three_le :
    Real.exp (-t_critical * (Real.log 3) ^ 2) ≤ Real.exp (-t_critical * (109 / 100 : ℝ) ^ 2) := by
  have ht : 0 ≤ t_critical := by norm_num [t_critical]
  have ha : 0 ≤ (109 / 100 : ℝ) := by norm_num
  have hlog : (109 / 100 : ℝ) ≤ Real.log 3 := (log_three_bounds).1
  simpa using
    (exp_neg_t_log_sq_le_of_log_lower (t := t_critical) (a := (109 / 100 : ℝ)) (n := 3) ht ha
      hlog)

lemma exp_neg_t_log_sq_five_le :
    Real.exp (-t_critical * (Real.log 5) ^ 2) ≤ Real.exp (-t_critical * (8 / 5 : ℝ) ^ 2) := by
  have ht : 0 ≤ t_critical := by norm_num [t_critical]
  have ha : 0 ≤ (8 / 5 : ℝ) := by norm_num
  have hlog : (8 / 5 : ℝ) ≤ Real.log 5 := (log_five_bounds).1
  simpa using
    (exp_neg_t_log_sq_le_of_log_lower (t := t_critical) (a := (8 / 5 : ℝ)) (n := 5) ht ha hlog)

lemma prime_heat_envelope_two_le :
    prime_heat_envelope 2 ≤ prime_heat_envelope_ub 2 (69 / 100 : ℝ) (7 / 10 : ℝ) := by
  have hl0 : 0 ≤ (69 / 100 : ℝ) := by norm_num
  have hu0 : 0 ≤ (7 / 10 : ℝ) := by norm_num
  have hl : (69 / 100 : ℝ) ≤ Real.log 2 := (log_two_bounds).1
  have hu : Real.log 2 ≤ (7 / 10 : ℝ) := (log_two_bounds).2
  simpa using (prime_heat_envelope_le_of_log_bounds (n := 2) (l := (69 / 100 : ℝ))
    (u := (7 / 10 : ℝ)) hl0 hu0 hl hu)

lemma prime_heat_envelope_three_le :
    prime_heat_envelope 3 ≤ prime_heat_envelope_ub 3 (109 / 100 : ℝ) (11 / 10 : ℝ) := by
  have hl0 : 0 ≤ (109 / 100 : ℝ) := by norm_num
  have hu0 : 0 ≤ (11 / 10 : ℝ) := by norm_num
  have hl : (109 / 100 : ℝ) ≤ Real.log 3 := (log_three_bounds).1
  have hu : Real.log 3 ≤ (11 / 10 : ℝ) := (log_three_bounds).2
  simpa using (prime_heat_envelope_le_of_log_bounds (n := 3) (l := (109 / 100 : ℝ))
    (u := (11 / 10 : ℝ)) hl0 hu0 hl hu)

lemma prime_heat_envelope_five_le :
    prime_heat_envelope 5 ≤ prime_heat_envelope_ub 5 (8 / 5 : ℝ) (161 / 100 : ℝ) := by
  have hl0 : 0 ≤ (8 / 5 : ℝ) := by norm_num
  have hu0 : 0 ≤ (161 / 100 : ℝ) := by norm_num
  have hl : (8 / 5 : ℝ) ≤ Real.log 5 := (log_five_bounds).1
  have hu : Real.log 5 ≤ (161 / 100 : ℝ) := (log_five_bounds).2
  simpa using (prime_heat_envelope_le_of_log_bounds (n := 5) (l := (8 / 5 : ℝ))
    (u := (161 / 100 : ℝ)) hl0 hu0 hl hu)

lemma prime_heat_weight_term_le_pp_ub_of_bucket {n lo hi : ℕ}
    (hlo : 0 < lo) (hlo_n : lo ≤ n) (hn_hi : n ≤ hi)
    (h_ub :
      prime_heat_envelope_ub n (Real.log (lo : ℝ)) (Real.log (hi : ℝ)) ≤
        Full.prime_heat_pp_term_ub n) :
    prime_heat_weight_term n ≤ Full.prime_heat_pp_term_ub n := by
  have h_env :
      prime_heat_envelope n ≤
        prime_heat_envelope_ub n (Real.log (lo : ℝ)) (Real.log (hi : ℝ)) := by
    exact prime_heat_envelope_le_of_nat_bounds (n := n) (lo := lo) (hi := hi) hlo hlo_n hn_hi
  exact (prime_heat_weight_term_le_envelope n).trans (h_env.trans h_ub)

end Q3.Proofs.PrimeCert
