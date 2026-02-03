import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket87Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket87Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket87Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket87Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 87. -/
def prime_heat_pp_term_ub_q_get_bucket_87 (n : ℕ) : ℚ :=
  if n ≤ 872477 then prime_heat_pp_term_ub_q_get_bucket_87_part1 n
  else if n ≤ 875201 then prime_heat_pp_term_ub_q_get_bucket_87_part2 n
  else if n ≤ 877543 then prime_heat_pp_term_ub_q_get_bucket_87_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_87_part4 n

end Full
end Q3.Proofs.PrimeCert
