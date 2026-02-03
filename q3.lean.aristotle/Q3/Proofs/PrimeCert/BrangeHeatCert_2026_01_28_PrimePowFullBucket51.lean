import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket51Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket51Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket51Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket51Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 51. -/
def prime_heat_pp_term_ub_q_get_bucket_51 (n : ℕ) : ℚ :=
  if n ≤ 512597 then prime_heat_pp_term_ub_q_get_bucket_51_part1 n
  else if n ≤ 515089 then prime_heat_pp_term_ub_q_get_bucket_51_part2 n
  else if n ≤ 517499 then prime_heat_pp_term_ub_q_get_bucket_51_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_51_part4 n

end Full
end Q3.Proofs.PrimeCert
