import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket25Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket25Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket25Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket25Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 25. -/
def prime_heat_pp_term_ub_q_get_bucket_25 (n : ℕ) : ℚ :=
  if n ≤ 252463 then prime_heat_pp_term_ub_q_get_bucket_25_part1 n
  else if n ≤ 255019 then prime_heat_pp_term_ub_q_get_bucket_25_part2 n
  else if n ≤ 257501 then prime_heat_pp_term_ub_q_get_bucket_25_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_25_part4 n

end Full
end Q3.Proofs.PrimeCert
