import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_Data

/-!
Prime-heat pilot bucket sums (t_critical, tau = 0).

These are extracted from the prime-power interval certificate and record only
bucket-level sums for the pilot buckets (0 and 99).
-/

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace PilotSums

/-- Common denominator for prime-power term bounds. -/
def prime_heat_pp_term_ub_den : ℚ := 100000000000000000000

/-- Prime-power bucket sums (rational). -/
def prime_heat_pp_term_ub_q_sum_bucket_0 : ℚ :=
  (400453633675995038081 : ℚ) / prime_heat_pp_term_ub_den

def prime_heat_pp_term_ub_q_sum_bucket_99 : ℚ :=
  (1650848424 : ℚ) / prime_heat_pp_term_ub_den

end PilotSums
end Q3.Proofs.PrimeCert
