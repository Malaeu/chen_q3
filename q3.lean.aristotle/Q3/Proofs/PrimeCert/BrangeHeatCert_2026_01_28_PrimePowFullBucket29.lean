import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket29Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket29Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket29Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket29Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 29. -/
def prime_heat_pp_term_ub_q_get_bucket_29 (n : ℕ) : ℚ :=
  if n ≤ 292441 then prime_heat_pp_term_ub_q_get_bucket_29_part1 n
  else if n ≤ 294947 then prime_heat_pp_term_ub_q_get_bucket_29_part2 n
  else if n ≤ 297467 then prime_heat_pp_term_ub_q_get_bucket_29_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_29_part4 n

end Full
end Q3.Proofs.PrimeCert
