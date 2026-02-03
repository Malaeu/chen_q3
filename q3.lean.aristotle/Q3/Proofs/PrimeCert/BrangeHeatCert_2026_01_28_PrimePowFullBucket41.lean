import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket41Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket41Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket41Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket41Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 41. -/
def prime_heat_pp_term_ub_q_get_bucket_41 (n : ℕ) : ℚ :=
  if n ≤ 412457 then prime_heat_pp_term_ub_q_get_bucket_41_part1 n
  else if n ≤ 414991 then prime_heat_pp_term_ub_q_get_bucket_41_part2 n
  else if n ≤ 417581 then prime_heat_pp_term_ub_q_get_bucket_41_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_41_part4 n

end Full
end Q3.Proofs.PrimeCert
