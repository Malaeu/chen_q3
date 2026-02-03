import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket16Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket16Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket16Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket16Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Twenty

/-- Upper bounds for prime-power terms (rational), bucket 16. -/
def prime_heat_pp_term_ub_q_get_bucket_16 (n : ℕ) : ℚ :=
  if n ≤ 162499 then prime_heat_pp_term_ub_q_get_bucket_16_part1 n
  else if n ≤ 164911 then prime_heat_pp_term_ub_q_get_bucket_16_part2 n
  else if n ≤ 167407 then prime_heat_pp_term_ub_q_get_bucket_16_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_16_part4 n

end Twenty
end Q3.Proofs.PrimeCert
