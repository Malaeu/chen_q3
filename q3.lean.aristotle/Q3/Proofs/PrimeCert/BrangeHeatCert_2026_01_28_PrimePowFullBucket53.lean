import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket53Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket53Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket53Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket53Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 53. -/
def prime_heat_pp_term_ub_q_get_bucket_53 (n : ℕ) : ℚ :=
  if n ≤ 532453 then prime_heat_pp_term_ub_q_get_bucket_53_part1 n
  else if n ≤ 534971 then prime_heat_pp_term_ub_q_get_bucket_53_part2 n
  else if n ≤ 537343 then prime_heat_pp_term_ub_q_get_bucket_53_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_53_part4 n

end Full
end Q3.Proofs.PrimeCert
