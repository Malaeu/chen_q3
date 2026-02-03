import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket32Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket32Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket32Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket32Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 32. -/
def prime_heat_pp_term_ub_q_get_bucket_32 (n : ℕ) : ℚ :=
  if n ≤ 322501 then prime_heat_pp_term_ub_q_get_bucket_32_part1 n
  else if n ≤ 324997 then prime_heat_pp_term_ub_q_get_bucket_32_part2 n
  else if n ≤ 327479 then prime_heat_pp_term_ub_q_get_bucket_32_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_32_part4 n

end Full
end Q3.Proofs.PrimeCert
