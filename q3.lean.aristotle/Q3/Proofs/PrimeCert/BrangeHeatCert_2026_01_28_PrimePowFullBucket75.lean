import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket75Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket75Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket75Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket75Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 75. -/
def prime_heat_pp_term_ub_q_get_bucket_75 (n : ℕ) : ℚ :=
  if n ≤ 752431 then prime_heat_pp_term_ub_q_get_bucket_75_part1 n
  else if n ≤ 754921 then prime_heat_pp_term_ub_q_get_bucket_75_part2 n
  else if n ≤ 757553 then prime_heat_pp_term_ub_q_get_bucket_75_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_75_part4 n

end Full
end Q3.Proofs.PrimeCert
