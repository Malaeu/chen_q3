import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket22Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket22Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket22Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket22Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 22. -/
def prime_heat_pp_term_ub_q_get_bucket_22 (n : ℕ) : ℚ :=
  if n ≤ 222557 then prime_heat_pp_term_ub_q_get_bucket_22_part1 n
  else if n ≤ 225109 then prime_heat_pp_term_ub_q_get_bucket_22_part2 n
  else if n ≤ 227593 then prime_heat_pp_term_ub_q_get_bucket_22_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_22_part4 n

end Full
end Q3.Proofs.PrimeCert
