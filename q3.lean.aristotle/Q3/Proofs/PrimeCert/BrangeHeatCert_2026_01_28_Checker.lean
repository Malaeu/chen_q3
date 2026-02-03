import Mathlib
import Q3.Proofs.PrimeCert.IntervalChecker
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_BucketDefs
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowData

/-!
Bucketed interval checker scaffold for the prime-heat partial sum.

This file packages the hypotheses needed to derive the partial-sum bound from
bucketed interval data. It does not yet provide the numeric proofs for the
bucket bounds.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

/-! Prime-power term upper bounds (certificate-backed). -/

lemma prime_heat_pp_term_ub_nonneg (n : ℕ) : 0 ≤ prime_heat_pp_term_ub n := by
  have hq : 0 ≤ prime_heat_pp_term_ub_q_get n := by
    native_decide
  exact_mod_cast hq

/-- Pointwise bound from the prime-power interval certificate (n ≤ N). -/
axiom prime_heat_weight_term_le_pp_ub_of_prime_pow {n : ℕ}
    (hn : IsPrimePow n) (hN : n ≤ prime_cert_heat_N) :
    prime_heat_weight_term n ≤ prime_heat_pp_term_ub n

lemma prime_heat_weight_term_le_pp_ub {n : ℕ} (hN : n ≤ prime_cert_heat_N) :
    prime_heat_weight_term n ≤ prime_heat_pp_term_ub n := by
  by_cases hpp : IsPrimePow n
  · exact prime_heat_weight_term_le_pp_ub_of_prime_pow hpp hN
  · have h0 : prime_heat_weight_term n = 0 :=
        prime_heat_weight_term_eq_zero_of_not_prime_pow hpp
    have hnonneg : 0 ≤ prime_heat_pp_term_ub n :=
      prime_heat_pp_term_ub_nonneg n
    simpa [h0] using hnonneg

def prime_heat_bucket_pp_sum_ub_q (k : Fin prime_heat_bucket_count) : ℚ :=
  (prime_heat_bucket_range k).sum prime_heat_pp_term_ub_q_get

def prime_heat_bucket_pp_sum_ub (k : Fin prime_heat_bucket_count) : ℝ :=
  (prime_heat_bucket_pp_sum_ub_q k : ℝ)

lemma prime_heat_bucket_pp_sum_ub_eq_sum (k : Fin prime_heat_bucket_count) :
    prime_heat_bucket_pp_sum_ub k =
      (prime_heat_bucket_range k).sum prime_heat_pp_term_ub := by
  classical
  simp [prime_heat_bucket_pp_sum_ub, prime_heat_bucket_pp_sum_ub_q,
    prime_heat_pp_term_ub, Rat.cast_sum]

lemma prime_heat_bucket_pp_sum_ub_q_le (k : Fin prime_heat_bucket_count) :
    prime_heat_bucket_pp_sum_ub_q k ≤ prime_heat_bucket_ub_q_get k := by
  native_decide

lemma prime_heat_bucket_pp_sum_ub_le_bucket (k : Fin prime_heat_bucket_count) :
    prime_heat_bucket_pp_sum_ub k ≤ prime_heat_bucket_ub k := by
  have hq :
      prime_heat_bucket_pp_sum_ub_q k ≤ prime_heat_bucket_ub_q_get k :=
    prime_heat_bucket_pp_sum_ub_q_le k
  exact_mod_cast hq

lemma prime_heat_bucket_sum_le_pp_ub (k : Fin prime_heat_bucket_count) :
    prime_heat_bucket_sum k ≤ prime_heat_bucket_pp_sum_ub k := by
  classical
  have hsum :
      prime_heat_bucket_sum k ≤ (prime_heat_bucket_range k).sum prime_heat_pp_term_ub := by
    apply Finset.sum_le_sum
    intro n hn
    have hn_hi : n ≤ prime_heat_bucket_hi k := (Finset.mem_Icc.mp hn).2
    have hnN : n ≤ prime_cert_heat_N := hn_hi.trans (prime_heat_bucket_hi_le_N k)
    exact prime_heat_weight_term_le_pp_ub hnN
  simpa [prime_heat_bucket_pp_sum_ub_eq_sum] using hsum

end Q3.Proofs.PrimeCert
