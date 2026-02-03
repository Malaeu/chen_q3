import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket81Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket81Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket81Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket81Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 81. -/
def prime_heat_pp_term_ub_q_get_bucket_81 (n : ℕ) : ℚ :=
  if n ≤ 812393 then prime_heat_pp_term_ub_q_get_bucket_81_part1 n
  else if n ≤ 814939 then prime_heat_pp_term_ub_q_get_bucket_81_part2 n
  else if n ≤ 817463 then prime_heat_pp_term_ub_q_get_bucket_81_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_81_part4 n

end Full
end Q3.Proofs.PrimeCert
