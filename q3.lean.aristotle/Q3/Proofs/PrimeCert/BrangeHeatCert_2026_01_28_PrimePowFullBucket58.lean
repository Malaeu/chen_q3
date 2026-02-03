import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket58Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket58Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket58Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket58Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 58. -/
def prime_heat_pp_term_ub_q_get_bucket_58 (n : ℕ) : ℚ :=
  if n ≤ 582541 then prime_heat_pp_term_ub_q_get_bucket_58_part1 n
  else if n ≤ 585043 then prime_heat_pp_term_ub_q_get_bucket_58_part2 n
  else if n ≤ 587441 then prime_heat_pp_term_ub_q_get_bucket_58_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_58_part4 n

end Full
end Q3.Proofs.PrimeCert
