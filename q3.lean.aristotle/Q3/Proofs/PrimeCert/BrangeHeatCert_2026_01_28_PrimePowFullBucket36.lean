import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket36Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket36Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket36Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket36Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 36. -/
def prime_heat_pp_term_ub_q_get_bucket_36 (n : ℕ) : ℚ :=
  if n ≤ 362459 then prime_heat_pp_term_ub_q_get_bucket_36_part1 n
  else if n ≤ 364979 then prime_heat_pp_term_ub_q_get_bucket_36_part2 n
  else if n ≤ 367309 then prime_heat_pp_term_ub_q_get_bucket_36_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_36_part4 n

end Full
end Q3.Proofs.PrimeCert
