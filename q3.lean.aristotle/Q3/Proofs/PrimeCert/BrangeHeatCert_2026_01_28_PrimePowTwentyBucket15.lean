import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket15Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket15Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket15Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket15Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Twenty

/-- Upper bounds for prime-power terms (rational), bucket 15. -/
def prime_heat_pp_term_ub_q_get_bucket_15 (n : ℕ) : ℚ :=
  if n ≤ 152393 then prime_heat_pp_term_ub_q_get_bucket_15_part1 n
  else if n ≤ 154883 then prime_heat_pp_term_ub_q_get_bucket_15_part2 n
  else if n ≤ 157393 then prime_heat_pp_term_ub_q_get_bucket_15_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_15_part4 n

end Twenty
end Q3.Proofs.PrimeCert
