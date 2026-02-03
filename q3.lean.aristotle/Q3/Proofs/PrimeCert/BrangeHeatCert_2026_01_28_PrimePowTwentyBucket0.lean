import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket0Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket0Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket0Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket0Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Twenty

/-- Upper bounds for prime-power terms (rational), bucket 0. -/
def prime_heat_pp_term_ub_q_get_bucket_0 (n : ℕ) : ℚ :=
  if n ≤ 1889 then prime_heat_pp_term_ub_q_get_bucket_0_part1 n
  else if n ≤ 4409 then prime_heat_pp_term_ub_q_get_bucket_0_part2 n
  else if n ≤ 7121 then prime_heat_pp_term_ub_q_get_bucket_0_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_0_part4 n

end Twenty
end Q3.Proofs.PrimeCert
