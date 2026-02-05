import Mathlib

/-!
Utility lemmas for interval-style numeric certificates.

This file isolates small, reusable facts about `Real.log`, `Real.exp`, and
casting rationals into reals. It is a foundation for future certified
numeric bounds (without `native_decide`).
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

lemma rat_cast_le {a b : ℚ} : (a : ℝ) ≤ b ↔ a ≤ b := by
  exact (Rat.cast_le (K := ℝ))

lemma rat_cast_lt {a b : ℚ} : (a : ℝ) < b ↔ a < b := by
  exact (Rat.cast_lt (K := ℝ))

lemma log_le_iff_le_exp {x y : ℝ} (hx : 0 < x) :
    Real.log x ≤ y ↔ x ≤ Real.exp y := by
  simpa using (Real.log_le_iff_le_exp hx)

lemma le_log_iff_exp_le {x y : ℝ} (hy : 0 < y) :
    x ≤ Real.log y ↔ Real.exp x ≤ y := by
  simpa using (Real.le_log_iff_exp_le hy)

lemma log_le_of_le_exp {x y : ℝ} (hx : 0 < x) (h : x ≤ Real.exp y) :
    Real.log x ≤ y := by
  exact (log_le_iff_le_exp (x := x) hx).2 h

lemma le_log_of_exp_le {x y : ℝ} (hy : 0 < y) (h : Real.exp x ≤ y) :
    x ≤ Real.log y := by
  exact (le_log_iff_exp_le (y := y) hy).2 h

lemma exp_le_exp_iff {x y : ℝ} : Real.exp x ≤ Real.exp y ↔ x ≤ y := by
  exact Real.exp_le_exp

lemma exp_lt_exp_iff {x y : ℝ} : Real.exp x < Real.exp y ↔ x < y := by
  exact Real.exp_lt_exp

lemma exp_eq_pow_div_nat (x : ℝ) {n : ℕ} (hn : 0 < n) :
    Real.exp x = Real.exp (x / n) ^ n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hx : (n : ℝ) * (x / n) = x := by
    calc
      (n : ℝ) * (x / n) = (n : ℝ) * x / n := by
        symm
        exact mul_div_assoc (n : ℝ) x (n : ℝ)
      _ = x := by
        simpa using (mul_div_cancel_left₀ x hn')
  calc
    Real.exp x = Real.exp ((n : ℝ) * (x / n)) := by simp [hx]
    _ = Real.exp (x / n) ^ n := by
      simpa using (Real.exp_nat_mul (x / n) n)

lemma exp_eq_pow_div_succ (x : ℝ) (n : ℕ) :
    Real.exp x = Real.exp (x / (n.succ)) ^ n.succ := by
  exact exp_eq_pow_div_nat x (Nat.succ_pos n)

lemma exp_le_pow_of_div_le {x b : ℝ} {n : ℕ} (hn : 0 < n)
    (h : Real.exp (x / n) ≤ b) : Real.exp x ≤ b ^ n := by
  have hx : Real.exp x = Real.exp (x / n) ^ n := exp_eq_pow_div_nat x hn
  have hpow : Real.exp (x / n) ^ n ≤ b ^ n := by
    exact pow_le_pow_left₀ (Real.exp_nonneg _) h _
  simpa [hx] using hpow

lemma pow_le_exp_of_le_div {x a : ℝ} {n : ℕ} (hn : 0 < n) (ha : 0 ≤ a)
    (h : a ≤ Real.exp (x / n)) : a ^ n ≤ Real.exp x := by
  have hx : Real.exp x = Real.exp (x / n) ^ n := exp_eq_pow_div_nat x hn
  have hpow : a ^ n ≤ Real.exp (x / n) ^ n := by
    exact pow_le_pow_left₀ ha h _
  simpa [hx] using hpow

lemma exp_le_of_taylor_bound {x b : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {n : ℕ} (hn : 0 < n)
    (h :
      (∑ m ∈ Finset.range n, x ^ m / (Nat.factorial m)) +
          x ^ n * (n + 1) / (Nat.factorial n * n) ≤ b) :
    Real.exp x ≤ b := by
  have hbound := Real.exp_bound' (x := x) hx0 hx1 (n := n) hn
  exact hbound.trans h

lemma exp_le_pow_of_taylor_bound_div {x b : ℝ} {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hx0 : 0 ≤ x) (hx1 : x / n ≤ 1)
    (h :
      (∑ m ∈ Finset.range k, (x / n) ^ m / (Nat.factorial m)) +
          (x / n) ^ k * (k + 1) / (Nat.factorial k * k) ≤ b) :
    Real.exp x ≤ b ^ n := by
  have hx0' : 0 ≤ x / n := by
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact div_nonneg hx0 (le_of_lt hn')
  have hbound : Real.exp (x / n) ≤ b := by
    exact exp_le_of_taylor_bound (x := x / n) (b := b) hx0' hx1 (n := k) hk h
  exact exp_le_pow_of_div_le (x := x) (b := b) (n := n) hn hbound

lemma exp_le_pow_of_taylor_bound_div_nat {x b : ℝ} {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hx0 : 0 ≤ x) (hx1 : x ≤ n)
    (h :
      (∑ m ∈ Finset.range k, (x / n) ^ m / (Nat.factorial m)) +
          (x / n) ^ k * (k + 1) / (Nat.factorial k * k) ≤ b) :
    Real.exp x ≤ b ^ n := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hx1' : x / n ≤ 1 := by
    have hx1' : x ≤ (n : ℝ) := by exact_mod_cast hx1
    -- divide by positive denominator
    have hdiv : x / (n : ℝ) ≤ (n : ℝ) / (n : ℝ) := by
      exact div_le_div_of_nonneg_right hx1' (le_of_lt hn')
    simpa [div_self (ne_of_gt hn')] using hdiv
  exact exp_le_pow_of_taylor_bound_div (x := x) (b := b) (n := n) (k := k) hn hk hx0 hx1' h

lemma exp_neg_mul_sq_le_of_le {t a b : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (-t * b ^ 2) ≤ Real.exp (-t * a ^ 2) := by
  have hsq : a ^ 2 ≤ b ^ 2 := by
    exact pow_le_pow_left₀ ha hab 2
  have hmul : t * a ^ 2 ≤ t * b ^ 2 := by
    exact mul_le_mul_of_nonneg_left hsq ht
  have hneg : -(t * b ^ 2) ≤ -(t * a ^ 2) := by
    exact neg_le_neg hmul
  have hexp : Real.exp (-(t * b ^ 2)) ≤ Real.exp (-(t * a ^ 2)) := by
    exact (Real.exp_le_exp).2 hneg
  simpa [mul_comm, mul_left_comm, mul_assoc] using hexp

lemma exp_neg_t_log_sq_le_of_log_lower {t a : ℝ} {n : ℕ} (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hlog : a ≤ Real.log (n : ℝ)) :
    Real.exp (-t * (Real.log (n : ℝ)) ^ 2) ≤ Real.exp (-t * a ^ 2) := by
  exact exp_neg_mul_sq_le_of_le (t := t) (a := a) (b := Real.log (n : ℝ)) ht ha hlog

lemma exp_neg_le_inv_sum {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n) :
    Real.exp (-c) ≤
      1 / (∑ m ∈ Finset.range n, c ^ m / (Nat.factorial m)) := by
  have hsum_le : (∑ m ∈ Finset.range n, c ^ m / (Nat.factorial m)) ≤ Real.exp c := by
    simpa using (Real.sum_le_exp_of_nonneg hc n)
  have hsum_pos : 0 < (∑ m ∈ Finset.range n, c ^ m / (Nat.factorial m)) := by
    have hmem : (0 : ℕ) ∈ Finset.range n := by
      simpa using (Finset.mem_range.mpr hn)
    have hnonneg : ∀ m ∈ Finset.range n, 0 ≤ c ^ m / (Nat.factorial m) := by
      intro m hm
      positivity
    have h1 : (1 : ℝ) ≤ ∑ m ∈ Finset.range n, c ^ m / (Nat.factorial m) := by
      simpa using
        (Finset.single_le_sum (f := fun m => c ^ m / (Nat.factorial m)) hnonneg hmem)
    exact lt_of_lt_of_le (by norm_num) h1
  have hinv : (1 / Real.exp c) ≤ 1 / (∑ m ∈ Finset.range n, c ^ m / (Nat.factorial m)) := by
    exact one_div_le_one_div_of_le hsum_pos hsum_le
  simpa [Real.exp_neg, one_div] using hinv

lemma log_nat_bounds_of_le {lo n hi : ℕ}
    (hlo : 0 < lo) (hlo_n : lo ≤ n) (hn_hi : n ≤ hi) :
    Real.log (lo : ℝ) ≤ Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ Real.log (hi : ℝ) := by
  have hlo' : 0 < (lo : ℝ) := by exact_mod_cast hlo
  have hn' : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le hlo hlo_n)
  have h1 : Real.log (lo : ℝ) ≤ Real.log (n : ℝ) := by
    exact Real.log_le_log hlo' (by exact_mod_cast hlo_n)
  have h2 : Real.log (n : ℝ) ≤ Real.log (hi : ℝ) := by
    exact Real.log_le_log hn' (by exact_mod_cast hn_hi)
  exact ⟨h1, h2⟩

lemma log_nat_le_iff_le_exp {n : ℕ} (hn : 0 < n) {y : ℝ} :
    Real.log (n : ℝ) ≤ y ↔ (n : ℝ) ≤ Real.exp y := by
  simpa using (log_le_iff_le_exp (x := (n : ℝ)) (by exact_mod_cast hn))

lemma le_log_nat_iff_exp_le {n : ℕ} (hn : 0 < n) {x : ℝ} :
    x ≤ Real.log (n : ℝ) ↔ Real.exp x ≤ (n : ℝ) := by
  simpa using (le_log_iff_exp_le (y := (n : ℝ)) (by exact_mod_cast hn))

lemma log_nat_le_of_le_exp {n : ℕ} (hn : 0 < n) {y : ℝ} (h : (n : ℝ) ≤ Real.exp y) :
    Real.log (n : ℝ) ≤ y := by
  exact (log_nat_le_iff_le_exp (n := n) hn).2 h

lemma le_log_nat_of_exp_le {n : ℕ} (hn : 0 < n) {x : ℝ} (h : Real.exp x ≤ (n : ℝ)) :
    x ≤ Real.log (n : ℝ) := by
  exact (le_log_nat_iff_exp_le (n := n) hn).2 h

end Q3.Proofs.PrimeCert
