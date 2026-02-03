import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket74Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket74Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket74Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket74Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 74. -/
def prime_heat_pp_term_ub_q_get_bucket_74 (n : ℕ) : ℚ :=
  if n ≤ 742507 then prime_heat_pp_term_ub_q_get_bucket_74_part1 n
  else if n ≤ 745103 then prime_heat_pp_term_ub_q_get_bucket_74_part2 n
  else if n ≤ 747599 then prime_heat_pp_term_ub_q_get_bucket_74_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_74_part4 n

end Full
end Q3.Proofs.PrimeCert
