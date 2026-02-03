import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket59Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket59Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket59Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket59Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 59. -/
def prime_heat_pp_term_ub_q_get_bucket_59 (n : ℕ) : ℚ :=
  if n ≤ 592597 then prime_heat_pp_term_ub_q_get_bucket_59_part1 n
  else if n ≤ 594989 then prime_heat_pp_term_ub_q_get_bucket_59_part2 n
  else if n ≤ 597437 then prime_heat_pp_term_ub_q_get_bucket_59_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_59_part4 n

end Full
end Q3.Proofs.PrimeCert
