import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket48Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket48Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket48Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket48Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 48. -/
def prime_heat_pp_term_ub_q_get_bucket_48 (n : ℕ) : ℚ :=
  if n ≤ 482423 then prime_heat_pp_term_ub_q_get_bucket_48_part1 n
  else if n ≤ 485041 then prime_heat_pp_term_ub_q_get_bucket_48_part2 n
  else if n ≤ 487637 then prime_heat_pp_term_ub_q_get_bucket_48_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_48_part4 n

end Full
end Q3.Proofs.PrimeCert
