import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket11Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket11Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket11Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket11Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 11. -/
def prime_heat_pp_term_ub_q_get_bucket_11 (n : ℕ) : ℚ :=
  if n ≤ 112543 then prime_heat_pp_term_ub_q_get_bucket_11_part1 n
  else if n ≤ 115061 then prime_heat_pp_term_ub_q_get_bucket_11_part2 n
  else if n ≤ 117517 then prime_heat_pp_term_ub_q_get_bucket_11_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_11_part4 n

end Full
end Q3.Proofs.PrimeCert
