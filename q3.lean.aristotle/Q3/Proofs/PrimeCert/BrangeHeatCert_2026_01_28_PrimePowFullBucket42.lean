import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket42Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket42Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket42Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket42Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 42. -/
def prime_heat_pp_term_ub_q_get_bucket_42 (n : ℕ) : ℚ :=
  if n ≤ 422563 then prime_heat_pp_term_ub_q_get_bucket_42_part1 n
  else if n ≤ 424939 then prime_heat_pp_term_ub_q_get_bucket_42_part2 n
  else if n ≤ 427523 then prime_heat_pp_term_ub_q_get_bucket_42_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_42_part4 n

end Full
end Q3.Proofs.PrimeCert
