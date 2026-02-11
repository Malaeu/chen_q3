import Mathlib
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_Data
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_PrimePow_i19_AllBuckets_Check

/-!
Bridge lemmas for grid index `i = 19` that connect generated prime-power
bucket data to the existing bucket/partial-sum checker chain.

This module keeps the final missing gap explicit:
- we already have `generated_pp_bucket_sum <= interval_bucket_ub`;
- to close `prime_b_grid_bucket_bounds` for `i=19`, we still need a theorem
  of the form `bucket_sum <= generated_pp_bucket_sum` (pointwise cover).
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

lemma prime_b_grid_pp_i19_all_bucket_total_q_le_prime_sum_ub_q :
    (Finset.univ.sum (fun k : Fin prime_b_grid_bucket_count =>
      prime_b_grid_pp_i19_all_ub_q_sum_get k)) ≤
      prime_b_grid_prime_sum_ub_q_get prime_b_grid_i19 := by
  have h_interval_total :
      (Finset.univ.sum (fun k : Fin prime_b_grid_bucket_count =>
        prime_b_grid_bucket_ub_q_get prime_b_grid_i19 k)) =
        prime_b_grid_bucket_ub_sum_q_get prime_b_grid_i19 :=
    prime_b_grid_bucket_ub_sum_q_eq prime_b_grid_i19
  have h_bucket_sum_q_le_prime_sum_ub_q :
      prime_b_grid_bucket_ub_sum_q_get prime_b_grid_i19 ≤
        prime_b_grid_prime_sum_ub_q_get prime_b_grid_i19 := by
    have hreal :
        prime_b_grid_bucket_ub_sum prime_b_grid_i19 ≤
          prime_b_grid_prime_sum_ub prime_b_grid_i19 :=
      prime_b_grid_bucket_ub_sum_le prime_b_grid_i19
    exact (Rat.cast_le (K := ℝ)).1 (by
      simpa [prime_b_grid_bucket_ub_sum, prime_b_grid_prime_sum_ub] using hreal)
  calc
    (Finset.univ.sum (fun k : Fin prime_b_grid_bucket_count =>
      prime_b_grid_pp_i19_all_ub_q_sum_get k))
        ≤
      (Finset.univ.sum (fun k : Fin prime_b_grid_bucket_count =>
        prime_b_grid_bucket_ub_q_get prime_b_grid_i19 k)) :=
          prime_b_grid_pp_i19_all_bucket_total_q_le_interval_total_q
    _ = prime_b_grid_bucket_ub_sum_q_get prime_b_grid_i19 := h_interval_total
    _ ≤ prime_b_grid_prime_sum_ub_q_get prime_b_grid_i19 := h_bucket_sum_q_le_prime_sum_ub_q

lemma prime_b_grid_pp_i19_all_bucket_total_le_prime_sum_ub :
    ((Finset.univ.sum (fun k : Fin prime_b_grid_bucket_count =>
      prime_b_grid_pp_i19_all_ub_q_sum_get k) : ℚ) : ℝ) ≤
      prime_b_grid_prime_sum_ub prime_b_grid_i19 := by
  exact (Rat.cast_le (K := ℝ)).2 prime_b_grid_pp_i19_all_bucket_total_q_le_prime_sum_ub_q

lemma prime_b_grid_bucket_bounds_i19_of_pp_cover
    (h_pp_cover :
      ∀ k : Fin prime_b_grid_bucket_count,
        prime_b_grid_bucket_sum prime_b_grid_i19 k ≤
          ((prime_b_grid_pp_i19_all_ub_q_sum_get k : ℚ) : ℝ)) :
    ∀ k : Fin prime_b_grid_bucket_count,
      prime_b_grid_bucket_sum prime_b_grid_i19 k ≤
        prime_b_grid_bucket_ub prime_b_grid_i19 k := by
  intro k
  exact (h_pp_cover k).trans (prime_b_grid_pp_i19_all_bucket_sum_le_interval k)

lemma prime_b_grid_bucket_data_i19_of_pp_cover
    (h_pp_cover :
      ∀ k : Fin prime_b_grid_bucket_count,
        prime_b_grid_bucket_sum prime_b_grid_i19 k ≤
          ((prime_b_grid_pp_i19_all_ub_q_sum_get k : ℚ) : ℝ)) :
    PrimeBGridBucketData prime_b_grid_i19 := by
  refine ⟨?_, ?_⟩
  · exact prime_b_grid_bucket_bounds_i19_of_pp_cover h_pp_cover
  · exact prime_b_grid_bucket_sum_ub prime_b_grid_i19

lemma prime_b_grid_prime_sum_up_to_i19_le_of_pp_cover
    (h_pp_cover :
      ∀ k : Fin prime_b_grid_bucket_count,
        prime_b_grid_bucket_sum prime_b_grid_i19 k ≤
          ((prime_b_grid_pp_i19_all_ub_q_sum_get k : ℚ) : ℝ)) :
    prime_b_grid_prime_sum_up_to prime_b_grid_i19 ≤
      prime_b_grid_prime_sum_ub prime_b_grid_i19 := by
  exact prime_b_grid_prime_sum_le_of_bucket
    prime_b_grid_i19 (prime_b_grid_bucket_data_i19_of_pp_cover h_pp_cover)

lemma prime_b_grid_prime_sum_up_to_i19_le_table_of_pp_cover
    (h_pp_cover :
      ∀ k : Fin prime_b_grid_bucket_count,
        prime_b_grid_bucket_sum prime_b_grid_i19 k ≤
          ((prime_b_grid_pp_i19_all_ub_q_sum_get k : ℚ) : ℝ)) :
    prime_b_grid_prime_sum_up_to prime_b_grid_i19 ≤
      prime_b_grid_prime_sum prime_b_grid_i19 := by
  exact (prime_b_grid_prime_sum_up_to_i19_le_of_pp_cover h_pp_cover).trans
    (prime_b_grid_prime_sum_ub_le_table prime_b_grid_i19)

end Q3.Proofs.PrimeCert
