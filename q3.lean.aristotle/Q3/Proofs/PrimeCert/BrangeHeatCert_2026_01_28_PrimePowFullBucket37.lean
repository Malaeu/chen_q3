import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket37Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket37Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket37Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket37Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 37. -/
def prime_heat_pp_term_ub_q_get_bucket_37 (n : ℕ) : ℚ :=
  if n ≤ 372637 then prime_heat_pp_term_ub_q_get_bucket_37_part1 n
  else if n ≤ 375083 then prime_heat_pp_term_ub_q_get_bucket_37_part2 n
  else if n ≤ 377521 then prime_heat_pp_term_ub_q_get_bucket_37_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_37_part4 n

end Full
end Q3.Proofs.PrimeCert
