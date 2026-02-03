import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_BucketDefs
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowPilot
set_option maxHeartbeats 0


/-!
Pilot bucket bounds for the prime-heat partial sum (t_critical, tau = 0).

This file is a staging area for two buckets (0 and 99) to validate the
interval-certificate workflow without `native_decide`.
It is intentionally *not* imported into the main chain.
-/


noncomputable section

namespace Q3.Proofs.PrimeCert

/-- Pilot bucket indices (lowest + highest). -/
def prime_heat_bucket_pilot_0 : Fin prime_heat_bucket_count := ⟨0, by decide⟩

def prime_heat_bucket_pilot_99 : Fin prime_heat_bucket_count := ⟨99, by decide⟩

structure PrimeHeatBucketPilotData : Prop where
  h0 : prime_heat_bucket_sum prime_heat_bucket_pilot_0 ≤
    prime_heat_bucket_ub prime_heat_bucket_pilot_0
  h99 : prime_heat_bucket_sum prime_heat_bucket_pilot_99 ≤
    prime_heat_bucket_ub prime_heat_bucket_pilot_99

/-- Pilot bucket sums (rational), filtered to prime powers. -/
def prime_heat_bucket_pp_sum_ub_q (k : Fin prime_heat_bucket_count) : ℚ :=
  ((prime_heat_bucket_range k).filter IsPrimePow).sum Pilot.prime_heat_pp_term_ub_q_get

/-- Pilot bucket sums (real), filtered to prime powers. -/
def prime_heat_bucket_pp_sum_ub (k : Fin prime_heat_bucket_count) : ℝ :=
  (prime_heat_bucket_pp_sum_ub_q k : ℝ)

/-- Pilot pointwise certificate: prime-power terms are bounded by the interval checker output. -/
axiom prime_heat_weight_term_le_pp_ub_of_prime_pow_pilot {n : ℕ}
    (hn : IsPrimePow n) (hN : n ≤ prime_cert_heat_N) :
    prime_heat_weight_term n ≤ Pilot.prime_heat_pp_term_ub n

lemma prime_heat_bucket_pp_sum_ub_eq_sum (k : Fin prime_heat_bucket_count) :
    prime_heat_bucket_pp_sum_ub k =
      ((prime_heat_bucket_range k).filter IsPrimePow).sum Pilot.prime_heat_pp_term_ub := by
  classical
  simp [prime_heat_bucket_pp_sum_ub, prime_heat_bucket_pp_sum_ub_q,
    Pilot.prime_heat_pp_term_ub, Rat.cast_sum]

lemma prime_heat_bucket_sum_le_pp_ub_pilot (k : Fin prime_heat_bucket_count) :
    prime_heat_bucket_sum k ≤ prime_heat_bucket_pp_sum_ub k := by
  classical
  have hsum_le :
      ((prime_heat_bucket_range k).filter IsPrimePow).sum prime_heat_weight_term ≤
        ((prime_heat_bucket_range k).filter IsPrimePow).sum Pilot.prime_heat_pp_term_ub := by
    apply Finset.sum_le_sum
    intro n hn
    have hn_range : n ∈ prime_heat_bucket_range k := (Finset.mem_filter.mp hn).1
    have hn_pp : IsPrimePow n := (Finset.mem_filter.mp hn).2
    have hn_hi : n ≤ prime_heat_bucket_hi k := (Finset.mem_Icc.mp hn_range).2
    have hnN : n ≤ prime_cert_heat_N := hn_hi.trans (prime_heat_bucket_hi_le_N k)
    exact prime_heat_weight_term_le_pp_ub_of_prime_pow_pilot hn_pp hnN
  calc
    prime_heat_bucket_sum k =
        ((prime_heat_bucket_range k).filter IsPrimePow).sum prime_heat_weight_term := by
          simpa using prime_heat_bucket_sum_eq_filter_prime_pow k
    _ ≤ ((prime_heat_bucket_range k).filter IsPrimePow).sum Pilot.prime_heat_pp_term_ub := hsum_le
    _ = prime_heat_bucket_pp_sum_ub k := by
          symm
          exact prime_heat_bucket_pp_sum_ub_eq_sum k

/-- Pilot certificate: bucketed per-term sums are bounded by the interval checker output. -/
axiom prime_heat_bucket_pp_sum_ub_le_bucket_pilot_0 :
    prime_heat_bucket_pp_sum_ub prime_heat_bucket_pilot_0 ≤
      prime_heat_bucket_ub prime_heat_bucket_pilot_0

axiom prime_heat_bucket_pp_sum_ub_le_bucket_pilot_99 :
    prime_heat_bucket_pp_sum_ub prime_heat_bucket_pilot_99 ≤
      prime_heat_bucket_ub prime_heat_bucket_pilot_99

lemma prime_heat_bucket_sum_le_ub_pilot_0 :
    prime_heat_bucket_sum prime_heat_bucket_pilot_0 ≤
      prime_heat_bucket_ub prime_heat_bucket_pilot_0 := by
  exact (prime_heat_bucket_sum_le_pp_ub_pilot _).trans
    prime_heat_bucket_pp_sum_ub_le_bucket_pilot_0

lemma prime_heat_bucket_sum_le_ub_pilot_99 :
    prime_heat_bucket_sum prime_heat_bucket_pilot_99 ≤
      prime_heat_bucket_ub prime_heat_bucket_pilot_99 := by
  exact (prime_heat_bucket_sum_le_pp_ub_pilot _).trans
    prime_heat_bucket_pp_sum_ub_le_bucket_pilot_99

end Q3.Proofs.PrimeCert
