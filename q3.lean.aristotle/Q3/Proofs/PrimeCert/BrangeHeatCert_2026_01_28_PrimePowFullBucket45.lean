import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket45Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket45Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket45Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket45Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 45. -/
def prime_heat_pp_term_ub_q_get_bucket_45 (n : ℕ) : ℚ :=
  if n ≤ 452279 then prime_heat_pp_term_ub_q_get_bucket_45_part1 n
  else if n ≤ 454973 then prime_heat_pp_term_ub_q_get_bucket_45_part2 n
  else if n ≤ 457367 then prime_heat_pp_term_ub_q_get_bucket_45_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_45_part4 n

end Full
end Q3.Proofs.PrimeCert
