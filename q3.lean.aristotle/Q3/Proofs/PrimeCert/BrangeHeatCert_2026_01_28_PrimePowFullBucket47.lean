import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket47Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket47Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket47Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket47Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 47. -/
def prime_heat_pp_term_ub_q_get_bucket_47 (n : ℕ) : ℚ :=
  if n ≤ 472369 then prime_heat_pp_term_ub_q_get_bucket_47_part1 n
  else if n ≤ 474937 then prime_heat_pp_term_ub_q_get_bucket_47_part2 n
  else if n ≤ 477481 then prime_heat_pp_term_ub_q_get_bucket_47_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_47_part4 n

end Full
end Q3.Proofs.PrimeCert
