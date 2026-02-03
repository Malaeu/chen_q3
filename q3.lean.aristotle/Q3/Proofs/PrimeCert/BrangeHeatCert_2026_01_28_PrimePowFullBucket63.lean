import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket63Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket63Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket63Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket63Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 63. -/
def prime_heat_pp_term_ub_q_get_bucket_63 (n : ℕ) : ℚ :=
  if n ≤ 632389 then prime_heat_pp_term_ub_q_get_bucket_63_part1 n
  else if n ≤ 634861 then prime_heat_pp_term_ub_q_get_bucket_63_part2 n
  else if n ≤ 637309 then prime_heat_pp_term_ub_q_get_bucket_63_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_63_part4 n

end Full
end Q3.Proofs.PrimeCert
