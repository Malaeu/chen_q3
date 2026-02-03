import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket94Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket94Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket94Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket94Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 94. -/
def prime_heat_pp_term_ub_q_get_bucket_94 (n : ℕ) : ℚ :=
  if n ≤ 942317 then prime_heat_pp_term_ub_q_get_bucket_94_part1 n
  else if n ≤ 944773 then prime_heat_pp_term_ub_q_get_bucket_94_part2 n
  else if n ≤ 947423 then prime_heat_pp_term_ub_q_get_bucket_94_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_94_part4 n

end Full
end Q3.Proofs.PrimeCert
