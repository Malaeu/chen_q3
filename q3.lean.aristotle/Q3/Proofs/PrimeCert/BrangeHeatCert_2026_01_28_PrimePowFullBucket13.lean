import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket13Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket13Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket13Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket13Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 13. -/
def prime_heat_pp_term_ub_q_get_bucket_13 (n : ℕ) : ℚ :=
  if n ≤ 132527 then prime_heat_pp_term_ub_q_get_bucket_13_part1 n
  else if n ≤ 135059 then prime_heat_pp_term_ub_q_get_bucket_13_part2 n
  else if n ≤ 137443 then prime_heat_pp_term_ub_q_get_bucket_13_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_13_part4 n

end Full
end Q3.Proofs.PrimeCert
