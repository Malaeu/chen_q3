import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket28Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket28Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket28Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket28Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 28. -/
def prime_heat_pp_term_ub_q_get_bucket_28 (n : ℕ) : ℚ :=
  if n ≤ 282313 then prime_heat_pp_term_ub_q_get_bucket_28_part1 n
  else if n ≤ 284803 then prime_heat_pp_term_ub_q_get_bucket_28_part2 n
  else if n ≤ 287387 then prime_heat_pp_term_ub_q_get_bucket_28_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_28_part4 n

end Full
end Q3.Proofs.PrimeCert
