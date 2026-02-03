import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket50Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket50Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket50Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket50Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 50. -/
def prime_heat_pp_term_ub_q_get_bucket_50 (n : ℕ) : ℚ :=
  if n ≤ 502517 then prime_heat_pp_term_ub_q_get_bucket_50_part1 n
  else if n ≤ 505049 then prime_heat_pp_term_ub_q_get_bucket_50_part2 n
  else if n ≤ 507491 then prime_heat_pp_term_ub_q_get_bucket_50_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_50_part4 n

end Full
end Q3.Proofs.PrimeCert
