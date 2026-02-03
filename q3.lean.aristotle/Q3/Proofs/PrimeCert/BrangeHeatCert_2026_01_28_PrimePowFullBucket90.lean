import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket90Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket90Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket90Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket90Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 90. -/
def prime_heat_pp_term_ub_q_get_bucket_90 (n : ℕ) : ℚ :=
  if n ≤ 902597 then prime_heat_pp_term_ub_q_get_bucket_90_part1 n
  else if n ≤ 905189 then prime_heat_pp_term_ub_q_get_bucket_90_part2 n
  else if n ≤ 907663 then prime_heat_pp_term_ub_q_get_bucket_90_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_90_part4 n

end Full
end Q3.Proofs.PrimeCert
