import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket84Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket84Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket84Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket84Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 84. -/
def prime_heat_pp_term_ub_q_get_bucket_84 (n : ℕ) : ℚ :=
  if n ≤ 842449 then prime_heat_pp_term_ub_q_get_bucket_84_part1 n
  else if n ≤ 844897 then prime_heat_pp_term_ub_q_get_bucket_84_part2 n
  else if n ≤ 847493 then prime_heat_pp_term_ub_q_get_bucket_84_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_84_part4 n

end Full
end Q3.Proofs.PrimeCert
