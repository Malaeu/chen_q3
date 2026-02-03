import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket10Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket10Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket10Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket10Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Twenty

/-- Upper bounds for prime-power terms (rational), bucket 10. -/
def prime_heat_pp_term_ub_q_get_bucket_10 (n : ℕ) : ℚ :=
  if n ≤ 102409 then prime_heat_pp_term_ub_q_get_bucket_10_part1 n
  else if n ≤ 104971 then prime_heat_pp_term_ub_q_get_bucket_10_part2 n
  else if n ≤ 107581 then prime_heat_pp_term_ub_q_get_bucket_10_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_10_part4 n

end Twenty
end Q3.Proofs.PrimeCert
