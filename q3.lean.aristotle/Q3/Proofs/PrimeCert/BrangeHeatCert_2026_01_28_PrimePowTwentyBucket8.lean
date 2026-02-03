import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket8Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket8Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket8Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket8Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Twenty

/-- Upper bounds for prime-power terms (rational), bucket 8. -/
def prime_heat_pp_term_ub_q_get_bucket_8 (n : ℕ) : ℚ :=
  if n ≤ 82387 then prime_heat_pp_term_ub_q_get_bucket_8_part1 n
  else if n ≤ 84967 then prime_heat_pp_term_ub_q_get_bucket_8_part2 n
  else if n ≤ 87509 then prime_heat_pp_term_ub_q_get_bucket_8_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_8_part4 n

end Twenty
end Q3.Proofs.PrimeCert
