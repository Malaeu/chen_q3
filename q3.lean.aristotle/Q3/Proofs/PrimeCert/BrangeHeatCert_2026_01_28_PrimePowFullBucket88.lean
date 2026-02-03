import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket88Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket88Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket88Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket88Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 88. -/
def prime_heat_pp_term_ub_q_get_bucket_88 (n : ℕ) : ℚ :=
  if n ≤ 882451 then prime_heat_pp_term_ub_q_get_bucket_88_part1 n
  else if n ≤ 885061 then prime_heat_pp_term_ub_q_get_bucket_88_part2 n
  else if n ≤ 887483 then prime_heat_pp_term_ub_q_get_bucket_88_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_88_part4 n

end Full
end Q3.Proofs.PrimeCert
