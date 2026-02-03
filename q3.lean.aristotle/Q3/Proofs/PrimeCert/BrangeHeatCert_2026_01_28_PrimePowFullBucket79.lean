import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket79Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket79Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket79Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket79Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 79. -/
def prime_heat_pp_term_ub_q_get_bucket_79 (n : ℕ) : ℚ :=
  if n ≤ 792443 then prime_heat_pp_term_ub_q_get_bucket_79_part1 n
  else if n ≤ 794953 then prime_heat_pp_term_ub_q_get_bucket_79_part2 n
  else if n ≤ 797383 then prime_heat_pp_term_ub_q_get_bucket_79_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_79_part4 n

end Full
end Q3.Proofs.PrimeCert
