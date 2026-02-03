import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket70Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket70Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket70Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket70Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 70. -/
def prime_heat_pp_term_ub_q_get_bucket_70 (n : ℕ) : ℚ :=
  if n ≤ 702523 then prime_heat_pp_term_ub_q_get_bucket_70_part1 n
  else if n ≤ 704969 then prime_heat_pp_term_ub_q_get_bucket_70_part2 n
  else if n ≤ 707563 then prime_heat_pp_term_ub_q_get_bucket_70_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_70_part4 n

end Full
end Q3.Proofs.PrimeCert
