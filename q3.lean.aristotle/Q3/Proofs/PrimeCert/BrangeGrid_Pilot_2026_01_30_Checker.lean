import Mathlib
import Q3.Proofs.PrimeCert.IntervalChecker
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSumTail
import Q3.Proofs.PrimeCert.BrangeGrid_Pilot_2026_01_30_Intervals

/-!
Bucketed interval checker scaffold for the pilot B-grid points.

This file packages the hypotheses needed to derive the pilot partial-sum bounds
from bucketed interval data. It does not yet provide the numeric proofs for the
bucket bounds.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

def prime_b_grid_pilot_bucket_range (k : Fin pilot_bucket_count) : Finset ℕ :=
  Finset.Icc (prime_b_grid_pilot_bucket_lo k) (prime_b_grid_pilot_bucket_hi k)

def prime_b_grid_pilot_bucket_sum (i : Fin prime_b_grid_size) (k : Fin pilot_bucket_count) : ℝ :=
  (prime_b_grid_pilot_bucket_range k).sum (fun n => prime_b_grid_weight_term i n)

structure PrimeBGridPilotBucketData (i : Fin prime_b_grid_size) : Prop where
  h_bucket :
    ∀ k : Fin pilot_bucket_count,
      prime_b_grid_pilot_bucket_sum i k ≤ prime_b_grid_pilot_bucket_ub i k
  h_cover :
    prime_b_grid_prime_sum_up_to i =
      (Finset.univ.sum (fun k => prime_b_grid_pilot_bucket_sum i k))
  h_sum_ub :
    (Finset.univ.sum (fun k => prime_b_grid_pilot_bucket_ub i k)) ≤
      prime_b_grid_pilot_sum_ub i

lemma prime_b_grid_pilot_sum_le_of_bucket
    (i : Fin prime_b_grid_size) (h : PrimeBGridPilotBucketData i) :
    prime_b_grid_prime_sum_up_to i ≤ prime_b_grid_pilot_sum_ub i := by
  calc
    prime_b_grid_prime_sum_up_to i =
        (Finset.univ.sum (fun k => prime_b_grid_pilot_bucket_sum i k)) := h.h_cover
    _ ≤ Finset.univ.sum (fun k => prime_b_grid_pilot_bucket_ub i k) := by
        apply Finset.sum_le_sum
        intro k hk
        exact h.h_bucket k
    _ ≤ prime_b_grid_pilot_sum_ub i := h.h_sum_ub

end Q3.Proofs.PrimeCert
