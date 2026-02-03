import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket14Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket14Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket14Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket14Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 14. -/
def prime_heat_pp_term_ub_q_get_bucket_14 (n : ℕ) : ℚ :=
  if n ≤ 142433 then prime_heat_pp_term_ub_q_get_bucket_14_part1 n
  else if n ≤ 145063 then prime_heat_pp_term_ub_q_get_bucket_14_part2 n
  else if n ≤ 147547 then prime_heat_pp_term_ub_q_get_bucket_14_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_14_part4 n

end Full
end Q3.Proofs.PrimeCert
