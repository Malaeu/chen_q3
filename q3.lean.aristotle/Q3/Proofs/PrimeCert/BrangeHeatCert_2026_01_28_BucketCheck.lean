import Mathlib
import Q3.Proofs.PrimeCert.IntervalChecker
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_BucketDefs
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFull

/-!
Proof scaffold for prime-heat bucket bounds (t_critical, tau = 0).

This file isolates the non-numeric reasoning: how pointwise prime-power bounds
and per-bucket sum bounds imply the required `PrimeHeatBucketData`. The numeric
certificates should plug into the hypotheses below.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

namespace Full

def prime_heat_bucket_pp_sum_ub_q (k : Fin prime_heat_bucket_count) : ℚ :=
  ((prime_heat_bucket_range k).filter IsPrimePow).sum prime_heat_pp_term_ub_q_get

def prime_heat_bucket_pp_sum_ub (k : Fin prime_heat_bucket_count) : ℝ :=
  (prime_heat_bucket_pp_sum_ub_q k : ℝ)

lemma prime_heat_bucket_pp_sum_ub_eq_sum (k : Fin prime_heat_bucket_count) :
    prime_heat_bucket_pp_sum_ub k =
      ((prime_heat_bucket_range k).filter IsPrimePow).sum prime_heat_pp_term_ub := by
  classical
  simp [prime_heat_bucket_pp_sum_ub, prime_heat_bucket_pp_sum_ub_q,
    prime_heat_pp_term_ub, Rat.cast_sum]

end Full

lemma prime_heat_bucket_sum_le_pp_ub_of_pp_bounds
    (h_term_ub :
      ∀ n : ℕ, IsPrimePow n → n ≤ prime_cert_heat_N →
        prime_heat_weight_term n ≤ Full.prime_heat_pp_term_ub n)
    (k : Fin prime_heat_bucket_count) :
    prime_heat_bucket_sum k ≤ Full.prime_heat_bucket_pp_sum_ub k := by
  classical
  have hsum_le :
      ((prime_heat_bucket_range k).filter IsPrimePow).sum prime_heat_weight_term ≤
        ((prime_heat_bucket_range k).filter IsPrimePow).sum Full.prime_heat_pp_term_ub := by
    apply Finset.sum_le_sum
    intro n hn
    have hn_range : n ∈ prime_heat_bucket_range k := (Finset.mem_filter.mp hn).1
    have hn_pp : IsPrimePow n := (Finset.mem_filter.mp hn).2
    have hn_hi : n ≤ prime_heat_bucket_hi k := (Finset.mem_Icc.mp hn_range).2
    have hnN : n ≤ prime_cert_heat_N := hn_hi.trans (prime_heat_bucket_hi_le_N k)
    exact h_term_ub n hn_pp hnN
  calc
    prime_heat_bucket_sum k =
        ((prime_heat_bucket_range k).filter IsPrimePow).sum prime_heat_weight_term := by
          simpa using prime_heat_bucket_sum_eq_filter_prime_pow k
    _ ≤ ((prime_heat_bucket_range k).filter IsPrimePow).sum Full.prime_heat_pp_term_ub := hsum_le
    _ = Full.prime_heat_bucket_pp_sum_ub k := by
          symm
          exact Full.prime_heat_bucket_pp_sum_ub_eq_sum k

lemma prime_heat_bucket_sum_le_ub_of_pp_bounds
    (h_term_ub :
      ∀ n : ℕ, IsPrimePow n → n ≤ prime_cert_heat_N →
        prime_heat_weight_term n ≤ Full.prime_heat_pp_term_ub n)
    (h_bucket_ub :
      ∀ k : Fin prime_heat_bucket_count,
        Full.prime_heat_bucket_pp_sum_ub k ≤ prime_heat_bucket_ub k)
    (k : Fin prime_heat_bucket_count) :
    prime_heat_bucket_sum k ≤ prime_heat_bucket_ub k := by
  exact (prime_heat_bucket_sum_le_pp_ub_of_pp_bounds h_term_ub k).trans (h_bucket_ub k)

theorem prime_heat_bucket_data_of_pp_bounds
    (bound : ℝ)
    (h_term_ub :
      ∀ n : ℕ, IsPrimePow n → n ≤ prime_cert_heat_N →
        prime_heat_weight_term n ≤ Full.prime_heat_pp_term_ub n)
    (h_bucket_ub :
      ∀ k : Fin prime_heat_bucket_count,
        Full.prime_heat_bucket_pp_sum_ub k ≤ prime_heat_bucket_ub k)
    (h_sum_ub : (Finset.univ.sum (fun k => prime_heat_bucket_ub k)) ≤ bound) :
    PrimeHeatBucketData bound := by
  refine ⟨?_, h_sum_ub⟩
  intro k
  exact prime_heat_bucket_sum_le_ub_of_pp_bounds h_term_ub h_bucket_ub k

end Q3.Proofs.PrimeCert
