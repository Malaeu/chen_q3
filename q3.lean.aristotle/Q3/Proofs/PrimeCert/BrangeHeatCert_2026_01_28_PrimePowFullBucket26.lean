import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket26Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket26Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket26Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket26Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 26. -/
def prime_heat_pp_term_ub_q_get_bucket_26 (n : ℕ) : ℚ :=
  if n ≤ 262597 then prime_heat_pp_term_ub_q_get_bucket_26_part1 n
  else if n ≤ 265123 then prime_heat_pp_term_ub_q_get_bucket_26_part2 n
  else if n ≤ 267521 then prime_heat_pp_term_ub_q_get_bucket_26_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_26_part4 n

end Full
end Q3.Proofs.PrimeCert
