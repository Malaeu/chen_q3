import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_Checker
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_Intervals

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

lemma prime_heat_bucket_sum_le_pp_ub_pilot_0 :
    prime_heat_bucket_sum prime_heat_bucket_pilot_0 ≤
      prime_heat_bucket_pp_sum_ub prime_heat_bucket_pilot_0 := by
  simpa using prime_heat_bucket_sum_le_pp_ub prime_heat_bucket_pilot_0

lemma prime_heat_bucket_sum_le_pp_ub_pilot_99 :
    prime_heat_bucket_sum prime_heat_bucket_pilot_99 ≤
      prime_heat_bucket_pp_sum_ub prime_heat_bucket_pilot_99 := by
  simpa using prime_heat_bucket_sum_le_pp_ub prime_heat_bucket_pilot_99

lemma prime_heat_bucket_sum_le_ub_pilot_0 :
    prime_heat_bucket_sum prime_heat_bucket_pilot_0 ≤
      prime_heat_bucket_ub prime_heat_bucket_pilot_0 := by
  exact (prime_heat_bucket_sum_le_pp_ub prime_heat_bucket_pilot_0).trans
    (prime_heat_bucket_pp_sum_ub_le_bucket prime_heat_bucket_pilot_0)

lemma prime_heat_bucket_sum_le_ub_pilot_99 :
    prime_heat_bucket_sum prime_heat_bucket_pilot_99 ≤
      prime_heat_bucket_ub prime_heat_bucket_pilot_99 := by
  exact (prime_heat_bucket_sum_le_pp_ub prime_heat_bucket_pilot_99).trans
    (prime_heat_bucket_pp_sum_ub_le_bucket prime_heat_bucket_pilot_99)

/-!
Numeric pilot data will be supplied by the interval checker output and
formalized without `native_decide`. For now, we keep this file as a
placeholder scaffold to wire in the two bucket proofs once available.
-/

end Q3.Proofs.PrimeCert
