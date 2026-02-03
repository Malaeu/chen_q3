import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowPilotBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowPilotBucket99Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowPilotBucket99Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowPilotBucket99Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowPilotBucket99Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Pilot

/-- Upper bounds for prime-power terms (rational), bucket 99. -/
def prime_heat_pp_term_ub_q_get_bucket_99 (n : ℕ) : ℚ :=
  if n ≤ 992441 then prime_heat_pp_term_ub_q_get_bucket_99_part1 n
  else if n ≤ 994991 then prime_heat_pp_term_ub_q_get_bucket_99_part2 n
  else if n ≤ 997427 then prime_heat_pp_term_ub_q_get_bucket_99_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_99_part4 n

end Pilot
end Q3.Proofs.PrimeCert
