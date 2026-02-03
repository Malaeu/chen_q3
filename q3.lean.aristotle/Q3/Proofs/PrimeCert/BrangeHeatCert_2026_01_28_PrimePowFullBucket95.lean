import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket95Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket95Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket95Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket95Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 95. -/
def prime_heat_pp_term_ub_q_get_bucket_95 (n : ℕ) : ℚ :=
  if n ≤ 952397 then prime_heat_pp_term_ub_q_get_bucket_95_part1 n
  else if n ≤ 954917 then prime_heat_pp_term_ub_q_get_bucket_95_part2 n
  else if n ≤ 957547 then prime_heat_pp_term_ub_q_get_bucket_95_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_95_part4 n

end Full
end Q3.Proofs.PrimeCert
