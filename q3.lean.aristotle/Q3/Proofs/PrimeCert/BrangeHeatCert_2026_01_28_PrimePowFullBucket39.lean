import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket39Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket39Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket39Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket39Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 39. -/
def prime_heat_pp_term_ub_q_get_bucket_39 (n : ℕ) : ℚ :=
  if n ≤ 392363 then prime_heat_pp_term_ub_q_get_bucket_39_part1 n
  else if n ≤ 394829 then prime_heat_pp_term_ub_q_get_bucket_39_part2 n
  else if n ≤ 397519 then prime_heat_pp_term_ub_q_get_bucket_39_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_39_part4 n

end Full
end Q3.Proofs.PrimeCert
