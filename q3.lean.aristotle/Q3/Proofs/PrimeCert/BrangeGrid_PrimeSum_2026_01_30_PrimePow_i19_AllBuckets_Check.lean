import Mathlib
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_Intervals
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_PrimePow_i19_AllBuckets

/-!
Sanity checks for generated prime-power UB bucket sums at grid index `i = 19`.

This verifies that every generated bucket upper-sum entry is below the existing
full-grid interval bucket UB table.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

def prime_b_grid_i19 : Fin prime_b_grid_size := ⟨19, by decide⟩

lemma prime_b_grid_pp_i19_all_bucket_sum_q_le_interval_q :
    ∀ k : Fin prime_b_grid_bucket_count,
      prime_b_grid_pp_i19_all_ub_q_sum_get k ≤
        prime_b_grid_bucket_ub_q_get prime_b_grid_i19 k := by
  intro k
  fin_cases k <;> native_decide

lemma prime_b_grid_pp_i19_all_bucket_sum_le_interval :
    ∀ k : Fin prime_b_grid_bucket_count,
      ((prime_b_grid_pp_i19_all_ub_q_sum_get k : ℚ) : ℝ) ≤
        prime_b_grid_bucket_ub prime_b_grid_i19 k := by
  intro k
  exact (Rat.cast_le (K := ℝ)).2 (prime_b_grid_pp_i19_all_bucket_sum_q_le_interval_q k)

lemma prime_b_grid_pp_i19_all_bucket_total_q_le_interval_total_q :
    (Finset.univ.sum (fun k : Fin prime_b_grid_bucket_count =>
      prime_b_grid_pp_i19_all_ub_q_sum_get k)) ≤
      (Finset.univ.sum (fun k : Fin prime_b_grid_bucket_count =>
        prime_b_grid_bucket_ub_q_get prime_b_grid_i19 k)) := by
  exact Finset.sum_le_sum (fun k _ => prime_b_grid_pp_i19_all_bucket_sum_q_le_interval_q k)

lemma prime_b_grid_pp_i19_all_bucket_total_le_interval_total :
    ((Finset.univ.sum (fun k : Fin prime_b_grid_bucket_count =>
      prime_b_grid_pp_i19_all_ub_q_sum_get k) : ℚ) : ℝ) ≤
      ((Finset.univ.sum (fun k : Fin prime_b_grid_bucket_count =>
        prime_b_grid_bucket_ub_q_get prime_b_grid_i19 k) : ℚ) : ℝ) := by
  exact (Rat.cast_le (K := ℝ)).2 prime_b_grid_pp_i19_all_bucket_total_q_le_interval_total_q

end Q3.Proofs.PrimeCert
