import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket78Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket78Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket78Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket78Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 78. -/
def prime_heat_pp_term_ub_q_get_bucket_78 (n : ℕ) : ℚ :=
  if n ≤ 782387 then prime_heat_pp_term_ub_q_get_bucket_78_part1 n
  else if n ≤ 784961 then prime_heat_pp_term_ub_q_get_bucket_78_part2 n
  else if n ≤ 787513 then prime_heat_pp_term_ub_q_get_bucket_78_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_78_part4 n

end Full
end Q3.Proofs.PrimeCert
