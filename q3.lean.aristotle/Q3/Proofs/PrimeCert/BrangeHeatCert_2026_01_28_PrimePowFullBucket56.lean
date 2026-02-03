import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket56Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket56Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket56Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket56Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 56. -/
def prime_heat_pp_term_ub_q_get_bucket_56 (n : ℕ) : ℚ :=
  if n ≤ 562517 then prime_heat_pp_term_ub_q_get_bucket_56_part1 n
  else if n ≤ 564989 then prime_heat_pp_term_ub_q_get_bucket_56_part2 n
  else if n ≤ 567533 then prime_heat_pp_term_ub_q_get_bucket_56_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_56_part4 n

end Full
end Q3.Proofs.PrimeCert
