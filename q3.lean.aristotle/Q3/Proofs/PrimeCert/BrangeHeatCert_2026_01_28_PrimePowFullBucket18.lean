import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket18Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket18Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket18Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket18Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 18. -/
def prime_heat_pp_term_ub_q_get_bucket_18 (n : ℕ) : ℚ :=
  if n ≤ 182617 then prime_heat_pp_term_ub_q_get_bucket_18_part1 n
  else if n ≤ 185131 then prime_heat_pp_term_ub_q_get_bucket_18_part2 n
  else if n ≤ 187471 then prime_heat_pp_term_ub_q_get_bucket_18_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_18_part4 n

end Full
end Q3.Proofs.PrimeCert
