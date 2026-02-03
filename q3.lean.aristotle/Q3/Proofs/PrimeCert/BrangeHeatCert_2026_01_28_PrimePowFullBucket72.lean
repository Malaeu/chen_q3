import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket72Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket72Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket72Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket72Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 72. -/
def prime_heat_pp_term_ub_q_get_bucket_72 (n : ℕ) : ℚ :=
  if n ≤ 722411 then prime_heat_pp_term_ub_q_get_bucket_72_part1 n
  else if n ≤ 724853 then prime_heat_pp_term_ub_q_get_bucket_72_part2 n
  else if n ≤ 727459 then prime_heat_pp_term_ub_q_get_bucket_72_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_72_part4 n

end Full
end Q3.Proofs.PrimeCert
