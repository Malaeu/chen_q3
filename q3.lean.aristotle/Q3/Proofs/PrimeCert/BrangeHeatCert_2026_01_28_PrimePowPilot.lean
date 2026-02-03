import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowPilotBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowPilotBucket0
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowPilotBucket99
set_option maxHeartbeats 0

/-!
Prime-heat prime-power term bounds (t_critical, tau = 0).

This file wires the bucketed lookup tables into a single accessor.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Pilot

/-- Upper bounds for prime-power terms (rational). -/
def prime_heat_pp_term_ub_q_get (n : ℕ) : ℚ :=
  match prime_heat_pp_term_bucket_index n with
  | 0 => prime_heat_pp_term_ub_q_get_bucket_0 n
  | 99 => prime_heat_pp_term_ub_q_get_bucket_99 n
  | _ => 0

/-- Upper bounds for prime-power terms (real). -/
def prime_heat_pp_term_ub (n : ℕ) : ℝ :=
  (prime_heat_pp_term_ub_q_get n : ℝ)

/-- Prime-power bucket sums (rational). -/
def prime_heat_pp_term_ub_q_sum_bucket_0 : ℚ := (400453633675995038081 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_99 : ℚ := (1650848424 : ℚ) / prime_heat_pp_term_ub_den

end Pilot
end Q3.Proofs.PrimeCert
