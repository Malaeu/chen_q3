import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket38Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket38Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket38Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket38Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 38. -/
def prime_heat_pp_term_ub_q_get_bucket_38 (n : ℕ) : ℚ :=
  if n ≤ 382621 then prime_heat_pp_term_ub_q_get_bucket_38_part1 n
  else if n ≤ 385013 then prime_heat_pp_term_ub_q_get_bucket_38_part2 n
  else if n ≤ 387503 then prime_heat_pp_term_ub_q_get_bucket_38_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_38_part4 n

end Full
end Q3.Proofs.PrimeCert
