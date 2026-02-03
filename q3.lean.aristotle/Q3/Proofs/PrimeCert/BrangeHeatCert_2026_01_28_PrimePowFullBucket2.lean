import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket2Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket2Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket2Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket2Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 2. -/
def prime_heat_pp_term_ub_q_get_bucket_2 (n : ℕ) : ℚ :=
  if n ≤ 22433 then prime_heat_pp_term_ub_q_get_bucket_2_part1 n
  else if n ≤ 24919 then prime_heat_pp_term_ub_q_get_bucket_2_part2 n
  else if n ≤ 27457 then prime_heat_pp_term_ub_q_get_bucket_2_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_2_part4 n

end Full
end Q3.Proofs.PrimeCert
