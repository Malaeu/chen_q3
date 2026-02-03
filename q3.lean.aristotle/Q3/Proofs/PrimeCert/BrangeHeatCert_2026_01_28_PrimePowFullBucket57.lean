import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket57Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket57Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket57Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket57Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 57. -/
def prime_heat_pp_term_ub_q_get_bucket_57 (n : ℕ) : ℚ :=
  if n ≤ 572437 then prime_heat_pp_term_ub_q_get_bucket_57_part1 n
  else if n ≤ 574969 then prime_heat_pp_term_ub_q_get_bucket_57_part2 n
  else if n ≤ 577483 then prime_heat_pp_term_ub_q_get_bucket_57_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_57_part4 n

end Full
end Q3.Proofs.PrimeCert
