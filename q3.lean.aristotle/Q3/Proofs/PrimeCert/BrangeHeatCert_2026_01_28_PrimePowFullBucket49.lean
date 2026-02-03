import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket49Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket49Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket49Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket49Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 49. -/
def prime_heat_pp_term_ub_q_get_bucket_49 (n : ℕ) : ℚ :=
  if n ≤ 492587 then prime_heat_pp_term_ub_q_get_bucket_49_part1 n
  else if n ≤ 495037 then prime_heat_pp_term_ub_q_get_bucket_49_part2 n
  else if n ≤ 497507 then prime_heat_pp_term_ub_q_get_bucket_49_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_49_part4 n

end Full
end Q3.Proofs.PrimeCert
