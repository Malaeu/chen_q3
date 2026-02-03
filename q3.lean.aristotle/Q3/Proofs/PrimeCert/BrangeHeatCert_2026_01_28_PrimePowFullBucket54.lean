import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket54Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket54Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket54Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket54Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 54. -/
def prime_heat_pp_term_ub_q_get_bucket_54 (n : ℕ) : ℚ :=
  if n ≤ 542467 then prime_heat_pp_term_ub_q_get_bucket_54_part1 n
  else if n ≤ 544961 then prime_heat_pp_term_ub_q_get_bucket_54_part2 n
  else if n ≤ 547559 then prime_heat_pp_term_ub_q_get_bucket_54_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_54_part4 n

end Full
end Q3.Proofs.PrimeCert
