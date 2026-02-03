import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket52Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket52Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket52Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket52Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 52. -/
def prime_heat_pp_term_ub_q_get_bucket_52 (n : ℕ) : ℚ :=
  if n ≤ 522439 then prime_heat_pp_term_ub_q_get_bucket_52_part1 n
  else if n ≤ 525001 then prime_heat_pp_term_ub_q_get_bucket_52_part2 n
  else if n ≤ 527393 then prime_heat_pp_term_ub_q_get_bucket_52_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_52_part4 n

end Full
end Q3.Proofs.PrimeCert
