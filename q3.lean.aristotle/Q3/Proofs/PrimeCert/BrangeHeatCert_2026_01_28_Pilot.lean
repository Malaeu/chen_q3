import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_BucketDefs
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowPilotSums
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

/-- Pilot bucket sums (rational). -/
def prime_heat_bucket_pp_sum_ub_pilot_q (k : Fin prime_heat_bucket_count) : ℚ :=
  match k.1 with
  | 0 => PilotSums.prime_heat_pp_term_ub_q_sum_bucket_0
  | 99 => PilotSums.prime_heat_pp_term_ub_q_sum_bucket_99
  | _ => 0

/-- Pilot bucket sums (real). -/
def prime_heat_bucket_pp_sum_ub_pilot (k : Fin prime_heat_bucket_count) : ℝ :=
  (prime_heat_bucket_pp_sum_ub_pilot_q k : ℝ)

/-- Pilot certificate: bucket sums are bounded by the interval checker output. -/
axiom prime_heat_bucket_sum_le_pp_ub_pilot_0 :
    prime_heat_bucket_sum prime_heat_bucket_pilot_0 ≤
      prime_heat_bucket_pp_sum_ub_pilot prime_heat_bucket_pilot_0

axiom prime_heat_bucket_sum_le_pp_ub_pilot_99 :
    prime_heat_bucket_sum prime_heat_bucket_pilot_99 ≤
      prime_heat_bucket_pp_sum_ub_pilot prime_heat_bucket_pilot_99

lemma prime_heat_bucket_pp_sum_ub_pilot_q_le_bucket_0 :
    PilotSums.prime_heat_pp_term_ub_q_sum_bucket_0 ≤
      prime_heat_bucket_ub_q_get prime_heat_bucket_pilot_0 := by
  change PilotSums.prime_heat_pp_term_ub_q_sum_bucket_0 ≤ (4.00453633676041 : ℚ)
  simp [PilotSums.prime_heat_pp_term_ub_q_sum_bucket_0, PilotSums.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_bucket_pp_sum_ub_pilot_q_le_bucket_99 :
    PilotSums.prime_heat_pp_term_ub_q_sum_bucket_99 ≤
      prime_heat_bucket_ub_q_get prime_heat_bucket_pilot_99 := by
  change PilotSums.prime_heat_pp_term_ub_q_sum_bucket_99 ≤ (0.00000000001651 : ℚ)
  simp [PilotSums.prime_heat_pp_term_ub_q_sum_bucket_99, PilotSums.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_bucket_pp_sum_ub_pilot_le_bucket_0 :
    prime_heat_bucket_pp_sum_ub_pilot prime_heat_bucket_pilot_0 ≤
      prime_heat_bucket_ub prime_heat_bucket_pilot_0 := by
  have hq :
      PilotSums.prime_heat_pp_term_ub_q_sum_bucket_0 ≤
        prime_heat_bucket_ub_q_get prime_heat_bucket_pilot_0 :=
    prime_heat_bucket_pp_sum_ub_pilot_q_le_bucket_0
  have hq' :
      (PilotSums.prime_heat_pp_term_ub_q_sum_bucket_0 : ℝ) ≤
        (prime_heat_bucket_ub_q_get prime_heat_bucket_pilot_0 : ℝ) := by
    exact_mod_cast hq
  simpa [prime_heat_bucket_pp_sum_ub_pilot, prime_heat_bucket_pp_sum_ub_pilot_q,
    prime_heat_bucket_ub] using hq'

lemma prime_heat_bucket_pp_sum_ub_pilot_le_bucket_99 :
    prime_heat_bucket_pp_sum_ub_pilot prime_heat_bucket_pilot_99 ≤
      prime_heat_bucket_ub prime_heat_bucket_pilot_99 := by
  have hq :
      PilotSums.prime_heat_pp_term_ub_q_sum_bucket_99 ≤
        prime_heat_bucket_ub_q_get prime_heat_bucket_pilot_99 :=
    prime_heat_bucket_pp_sum_ub_pilot_q_le_bucket_99
  have hq' :
      (PilotSums.prime_heat_pp_term_ub_q_sum_bucket_99 : ℝ) ≤
        (prime_heat_bucket_ub_q_get prime_heat_bucket_pilot_99 : ℝ) := by
    exact_mod_cast hq
  simpa [prime_heat_bucket_pp_sum_ub_pilot, prime_heat_bucket_pp_sum_ub_pilot_q,
    prime_heat_bucket_ub] using hq'

lemma prime_heat_bucket_sum_le_ub_pilot_0 :
    prime_heat_bucket_sum prime_heat_bucket_pilot_0 ≤
      prime_heat_bucket_ub prime_heat_bucket_pilot_0 := by
  exact (prime_heat_bucket_sum_le_pp_ub_pilot_0).trans
    (prime_heat_bucket_pp_sum_ub_pilot_le_bucket_0)

lemma prime_heat_bucket_sum_le_ub_pilot_99 :
    prime_heat_bucket_sum prime_heat_bucket_pilot_99 ≤
      prime_heat_bucket_ub prime_heat_bucket_pilot_99 := by
  exact (prime_heat_bucket_sum_le_pp_ub_pilot_99).trans
    (prime_heat_bucket_pp_sum_ub_pilot_le_bucket_99)

end Q3.Proofs.PrimeCert
