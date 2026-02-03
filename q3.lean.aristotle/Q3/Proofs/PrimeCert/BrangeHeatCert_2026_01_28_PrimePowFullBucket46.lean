import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket46Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket46Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket46Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket46Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 46. -/
def prime_heat_pp_term_ub_q_get_bucket_46 (n : ℕ) : ℚ :=
  if n ≤ 462607 then prime_heat_pp_term_ub_q_get_bucket_46_part1 n
  else if n ≤ 465007 then prime_heat_pp_term_ub_q_get_bucket_46_part2 n
  else if n ≤ 467611 then prime_heat_pp_term_ub_q_get_bucket_46_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_46_part4 n

end Full
end Q3.Proofs.PrimeCert
