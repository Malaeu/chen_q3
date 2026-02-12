import Mathlib
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_PrimePow_i19_Bridge
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_PrimePow_i19_Pointwise

/-!
`i = 19` prime-power cover scaffold.

This module rewrites the `h_pp_cover` obligation from bucket-level form
(`bucket_sum <= generated_bucket_sum`) to a pointwise prime-power term bound.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

lemma prime_b_grid_weight_term_eq_zero_of_not_prime_pow
    (i : Fin prime_b_grid_size) {n : ℕ} (hn : ¬ IsPrimePow n) :
    prime_b_grid_weight_term i n = 0 := by
  simp [prime_b_grid_weight_term, w_Q, ArithmeticFunction.vonMangoldt, hn]

lemma prime_b_grid_bucket_hi_le_N (k : Fin prime_b_grid_bucket_count) :
    prime_b_grid_bucket_hi k ≤ prime_cert_N := by
  have hk : k.1 + 1 ≤ prime_b_grid_bucket_count := Nat.succ_le_of_lt k.2
  have hmul :
      (k.1 + 1) * prime_b_grid_bucket_width ≤
        prime_b_grid_bucket_count * prime_b_grid_bucket_width := by
    exact Nat.mul_le_mul_right _ hk
  simpa [prime_b_grid_bucket_hi_eq, prime_b_grid_bucket_count_mul_width] using hmul

lemma prime_b_grid_bucket_sum_eq_filter_prime_pow
    (i : Fin prime_b_grid_size) (k : Fin prime_b_grid_bucket_count) :
    prime_b_grid_bucket_sum i k =
      ((prime_b_grid_bucket_range k).filter IsPrimePow).sum
        (fun n => prime_b_grid_weight_term i n) := by
  classical
  have hsum :
      prime_b_grid_bucket_sum i k =
        (prime_b_grid_bucket_range k).sum
          (fun n => if IsPrimePow n then prime_b_grid_weight_term i n else 0) := by
    simp [prime_b_grid_bucket_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    by_cases hpp : IsPrimePow n
    · simp [hpp]
    · simp [hpp, prime_b_grid_weight_term_eq_zero_of_not_prime_pow (i := i) hpp]
  have hfilter :
      ((prime_b_grid_bucket_range k).filter IsPrimePow).sum
          (fun n => prime_b_grid_weight_term i n) =
        (prime_b_grid_bucket_range k).sum
          (fun n => if IsPrimePow n then prime_b_grid_weight_term i n else 0) := by
    simpa using
      (Finset.sum_filter (s := prime_b_grid_bucket_range k)
        (p := IsPrimePow) (f := fun n => prime_b_grid_weight_term i n))
  calc
    prime_b_grid_bucket_sum i k =
        (prime_b_grid_bucket_range k).sum
          (fun n => if IsPrimePow n then prime_b_grid_weight_term i n else 0) := hsum
    _ =
        ((prime_b_grid_bucket_range k).filter IsPrimePow).sum
          (fun n => prime_b_grid_weight_term i n) := by
          simpa using hfilter.symm

def prime_b_grid_pp_i19_all_bucket_q_sum (k : Fin prime_b_grid_bucket_count) : ℚ :=
  ((prime_b_grid_bucket_range k).filter IsPrimePow).sum prime_b_grid_pp_i19_all_ub_q_get

def prime_b_grid_pp_i19_all_bucket_sum (k : Fin prime_b_grid_bucket_count) : ℝ :=
  (prime_b_grid_pp_i19_all_bucket_q_sum k : ℝ)

lemma prime_b_grid_pp_i19_all_bucket_sum_eq_sum
    (k : Fin prime_b_grid_bucket_count) :
    prime_b_grid_pp_i19_all_bucket_sum k =
      ((prime_b_grid_bucket_range k).filter IsPrimePow).sum prime_b_grid_pp_i19_all_ub := by
  classical
  simp [prime_b_grid_pp_i19_all_bucket_sum, prime_b_grid_pp_i19_all_bucket_q_sum,
    prime_b_grid_pp_i19_all_ub, Rat.cast_sum]

lemma prime_b_grid_pp_i19_all_bucket_q_sum_le_get
    (k : Fin prime_b_grid_bucket_count) :
    prime_b_grid_pp_i19_all_bucket_q_sum k ≤ prime_b_grid_pp_i19_all_ub_q_sum_get k := by
  fin_cases k <;> native_decide

lemma prime_b_grid_pp_i19_all_bucket_sum_le_get
    (k : Fin prime_b_grid_bucket_count) :
    prime_b_grid_pp_i19_all_bucket_sum k ≤
      ((prime_b_grid_pp_i19_all_ub_q_sum_get k : ℚ) : ℝ) := by
  change ((prime_b_grid_pp_i19_all_bucket_q_sum k : ℚ) : ℝ) ≤
    ((prime_b_grid_pp_i19_all_ub_q_sum_get k : ℚ) : ℝ)
  exact (Rat.cast_le (K := ℝ)).2 (prime_b_grid_pp_i19_all_bucket_q_sum_le_get k)

lemma prime_b_grid_bucket_sum_i19_le_pp_bucket_sum_of_term_bounds
    (h_term_ub :
      ∀ n : ℕ, IsPrimePow n → n ≤ prime_cert_N →
        prime_b_grid_weight_term prime_b_grid_i19 n ≤ prime_b_grid_pp_i19_all_ub n)
    (k : Fin prime_b_grid_bucket_count) :
    prime_b_grid_bucket_sum prime_b_grid_i19 k ≤
      prime_b_grid_pp_i19_all_bucket_sum k := by
  classical
  have hsum_le :
      ((prime_b_grid_bucket_range k).filter IsPrimePow).sum
          (fun n => prime_b_grid_weight_term prime_b_grid_i19 n) ≤
        ((prime_b_grid_bucket_range k).filter IsPrimePow).sum
          prime_b_grid_pp_i19_all_ub := by
    apply Finset.sum_le_sum
    intro n hn
    have hn_range : n ∈ prime_b_grid_bucket_range k := (Finset.mem_filter.mp hn).1
    have hn_pp : IsPrimePow n := (Finset.mem_filter.mp hn).2
    have hn_hi : n ≤ prime_b_grid_bucket_hi k := (Finset.mem_Icc.mp hn_range).2
    have hnN : n ≤ prime_cert_N := hn_hi.trans (prime_b_grid_bucket_hi_le_N k)
    exact h_term_ub n hn_pp hnN
  calc
    prime_b_grid_bucket_sum prime_b_grid_i19 k =
        ((prime_b_grid_bucket_range k).filter IsPrimePow).sum
          (fun n => prime_b_grid_weight_term prime_b_grid_i19 n) := by
            simpa using prime_b_grid_bucket_sum_eq_filter_prime_pow
              (i := prime_b_grid_i19) k
    _ ≤ ((prime_b_grid_bucket_range k).filter IsPrimePow).sum
          prime_b_grid_pp_i19_all_ub := hsum_le
    _ = prime_b_grid_pp_i19_all_bucket_sum k := by
          symm
          exact prime_b_grid_pp_i19_all_bucket_sum_eq_sum k

lemma prime_b_grid_bucket_sum_i19_le_pp_bucket_get_of_term_bounds
    (h_term_ub :
      ∀ n : ℕ, IsPrimePow n → n ≤ prime_cert_N →
        prime_b_grid_weight_term prime_b_grid_i19 n ≤ prime_b_grid_pp_i19_all_ub n) :
    ∀ k : Fin prime_b_grid_bucket_count,
      prime_b_grid_bucket_sum prime_b_grid_i19 k ≤
        ((prime_b_grid_pp_i19_all_ub_q_sum_get k : ℚ) : ℝ) := by
  intro k
  calc
    prime_b_grid_bucket_sum prime_b_grid_i19 k ≤
        prime_b_grid_pp_i19_all_bucket_sum k :=
          prime_b_grid_bucket_sum_i19_le_pp_bucket_sum_of_term_bounds h_term_ub k
    _ ≤ ((prime_b_grid_pp_i19_all_ub_q_sum_get k : ℚ) : ℝ) := by
          exact prime_b_grid_pp_i19_all_bucket_sum_le_get k

lemma prime_b_grid_weight_term_i19_le_pp_ub_of_term_bounds_gt2000
    (h_term_ub_gt2000 :
      ∀ n : ℕ, IsPrimePow n → 2001 ≤ n → n ≤ prime_cert_N →
        prime_b_grid_weight_term prime_b_grid_i19 n ≤ prime_b_grid_pp_i19_all_ub n) :
    ∀ n : ℕ, IsPrimePow n → n ≤ prime_cert_N →
      prime_b_grid_weight_term prime_b_grid_i19 n ≤ prime_b_grid_pp_i19_all_ub n := by
  intro n hn hnN
  by_cases hsmall : n ≤ 2000
  · have hlow : 1 ≤ n := Nat.le_trans (by decide : 1 ≤ 2) hn.two_le
    exact prime_b_grid_weight_term_i19_le_pp_ub_of_1_2000_primepow_all hn hlow hsmall
  · have hgt : 2001 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_not_ge hsmall)
    exact h_term_ub_gt2000 n hn hgt hnN

lemma prime_b_grid_bucket_sum_i19_le_pp_bucket_get_of_term_bounds_gt2000
    (h_term_ub_gt2000 :
      ∀ n : ℕ, IsPrimePow n → 2001 ≤ n → n ≤ prime_cert_N →
        prime_b_grid_weight_term prime_b_grid_i19 n ≤ prime_b_grid_pp_i19_all_ub n) :
    ∀ k : Fin prime_b_grid_bucket_count,
      prime_b_grid_bucket_sum prime_b_grid_i19 k ≤
        ((prime_b_grid_pp_i19_all_ub_q_sum_get k : ℚ) : ℝ) := by
  exact prime_b_grid_bucket_sum_i19_le_pp_bucket_get_of_term_bounds
    (prime_b_grid_weight_term_i19_le_pp_ub_of_term_bounds_gt2000 h_term_ub_gt2000)

lemma prime_b_grid_bucket_bounds_i19_of_term_bounds
    (h_term_ub :
      ∀ n : ℕ, IsPrimePow n → n ≤ prime_cert_N →
        prime_b_grid_weight_term prime_b_grid_i19 n ≤ prime_b_grid_pp_i19_all_ub n) :
    ∀ k : Fin prime_b_grid_bucket_count,
      prime_b_grid_bucket_sum prime_b_grid_i19 k ≤
        prime_b_grid_bucket_ub prime_b_grid_i19 k := by
  exact prime_b_grid_bucket_bounds_i19_of_pp_cover
    (prime_b_grid_bucket_sum_i19_le_pp_bucket_get_of_term_bounds h_term_ub)

lemma prime_b_grid_bucket_data_i19_of_term_bounds
    (h_term_ub :
      ∀ n : ℕ, IsPrimePow n → n ≤ prime_cert_N →
        prime_b_grid_weight_term prime_b_grid_i19 n ≤ prime_b_grid_pp_i19_all_ub n) :
    PrimeBGridBucketData prime_b_grid_i19 := by
  exact prime_b_grid_bucket_data_i19_of_pp_cover
    (prime_b_grid_bucket_sum_i19_le_pp_bucket_get_of_term_bounds h_term_ub)

lemma prime_b_grid_prime_sum_up_to_i19_le_of_term_bounds
    (h_term_ub :
      ∀ n : ℕ, IsPrimePow n → n ≤ prime_cert_N →
        prime_b_grid_weight_term prime_b_grid_i19 n ≤ prime_b_grid_pp_i19_all_ub n) :
    prime_b_grid_prime_sum_up_to prime_b_grid_i19 ≤
      prime_b_grid_prime_sum_ub prime_b_grid_i19 := by
  exact prime_b_grid_prime_sum_up_to_i19_le_of_pp_cover
    (prime_b_grid_bucket_sum_i19_le_pp_bucket_get_of_term_bounds h_term_ub)

lemma prime_b_grid_prime_sum_up_to_i19_le_table_of_term_bounds
    (h_term_ub :
      ∀ n : ℕ, IsPrimePow n → n ≤ prime_cert_N →
        prime_b_grid_weight_term prime_b_grid_i19 n ≤ prime_b_grid_pp_i19_all_ub n) :
    prime_b_grid_prime_sum_up_to prime_b_grid_i19 ≤
      prime_b_grid_prime_sum prime_b_grid_i19 := by
  exact prime_b_grid_prime_sum_up_to_i19_le_table_of_pp_cover
    (prime_b_grid_bucket_sum_i19_le_pp_bucket_get_of_term_bounds h_term_ub)

end Q3.Proofs.PrimeCert
