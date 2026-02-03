import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket30Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket30Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket30Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket30Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 30. -/
def prime_heat_pp_term_ub_q_get_bucket_30 (n : ℕ) : ℚ :=
  if n ≤ 302563 then prime_heat_pp_term_ub_q_get_bucket_30_part1 n
  else if n ≤ 304883 then prime_heat_pp_term_ub_q_get_bucket_30_part2 n
  else if n ≤ 307301 then prime_heat_pp_term_ub_q_get_bucket_30_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_30_part4 n

end Full
end Q3.Proofs.PrimeCert
