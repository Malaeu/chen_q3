import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket76Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket76Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket76Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket76Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 76. -/
def prime_heat_pp_term_ub_q_get_bucket_76 (n : ℕ) : ℚ :=
  if n ≤ 762491 then prime_heat_pp_term_ub_q_get_bucket_76_part1 n
  else if n ≤ 765031 then prime_heat_pp_term_ub_q_get_bucket_76_part2 n
  else if n ≤ 767489 then prime_heat_pp_term_ub_q_get_bucket_76_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_76_part4 n

end Full
end Q3.Proofs.PrimeCert
