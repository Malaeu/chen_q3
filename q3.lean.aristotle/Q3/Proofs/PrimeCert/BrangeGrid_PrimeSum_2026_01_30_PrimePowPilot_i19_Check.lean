import Mathlib
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_Intervals
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_PrimePowPilot_i19_Buckets0_99

/-!
Pilot sanity checks for the generated prime-power UB data at grid index `i = 19`.

This file only checks that selected bucket sums from the generated per-term table
fit under the existing full-grid interval bucket UB table.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

def prime_b_grid_i19 : Fin prime_b_grid_size := ⟨19, by decide⟩

def prime_b_grid_bucket0 : Fin prime_b_grid_bucket_count := ⟨0, by decide⟩

def prime_b_grid_bucket99 : Fin prime_b_grid_bucket_count := ⟨99, by decide⟩

lemma prime_b_grid_pp_i19_pilot_bucket0_sum_q_le_interval_q :
    prime_b_grid_pp_i19_pilot_ub_q_sum_bucket_0 ≤
      prime_b_grid_bucket_ub_q_get prime_b_grid_i19 prime_b_grid_bucket0 := by
  native_decide

lemma prime_b_grid_pp_i19_pilot_bucket99_sum_q_le_interval_q :
    prime_b_grid_pp_i19_pilot_ub_q_sum_bucket_99 ≤
      prime_b_grid_bucket_ub_q_get prime_b_grid_i19 prime_b_grid_bucket99 := by
  native_decide

lemma prime_b_grid_pp_i19_pilot_bucket0_sum_le_interval :
    ((prime_b_grid_pp_i19_pilot_ub_q_sum_bucket_0 : ℚ) : ℝ) ≤
      prime_b_grid_bucket_ub prime_b_grid_i19 prime_b_grid_bucket0 := by
  exact (Rat.cast_le (K := ℝ)).2 prime_b_grid_pp_i19_pilot_bucket0_sum_q_le_interval_q

lemma prime_b_grid_pp_i19_pilot_bucket99_sum_le_interval :
    ((prime_b_grid_pp_i19_pilot_ub_q_sum_bucket_99 : ℚ) : ℝ) ≤
      prime_b_grid_bucket_ub prime_b_grid_i19 prime_b_grid_bucket99 := by
  exact (Rat.cast_le (K := ℝ)).2 prime_b_grid_pp_i19_pilot_bucket99_sum_q_le_interval_q

end Q3.Proofs.PrimeCert
