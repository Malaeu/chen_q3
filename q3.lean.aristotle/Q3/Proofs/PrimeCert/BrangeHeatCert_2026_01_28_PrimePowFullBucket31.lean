import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket31Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket31Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket31Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket31Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 31. -/
def prime_heat_pp_term_ub_q_get_bucket_31 (n : ℕ) : ℚ :=
  if n ≤ 312589 then prime_heat_pp_term_ub_q_get_bucket_31_part1 n
  else if n ≤ 315097 then prime_heat_pp_term_ub_q_get_bucket_31_part2 n
  else if n ≤ 317593 then prime_heat_pp_term_ub_q_get_bucket_31_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_31_part4 n

end Full
end Q3.Proofs.PrimeCert
