import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket62Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket62Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket62Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket62Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 62. -/
def prime_heat_pp_term_ub_q_get_bucket_62 (n : ℕ) : ℚ :=
  if n ≤ 622477 then prime_heat_pp_term_ub_q_get_bucket_62_part1 n
  else if n ≤ 624829 then prime_heat_pp_term_ub_q_get_bucket_62_part2 n
  else if n ≤ 627449 then prime_heat_pp_term_ub_q_get_bucket_62_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_62_part4 n

end Full
end Q3.Proofs.PrimeCert
