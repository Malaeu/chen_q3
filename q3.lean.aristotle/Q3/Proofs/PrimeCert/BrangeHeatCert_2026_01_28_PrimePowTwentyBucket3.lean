import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket3Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket3Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket3Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket3Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Twenty

/-- Upper bounds for prime-power terms (rational), bucket 3. -/
def prime_heat_pp_term_ub_q_get_bucket_3 (n : ℕ) : ℚ :=
  if n ≤ 32479 then prime_heat_pp_term_ub_q_get_bucket_3_part1 n
  else if n ≤ 34883 then prime_heat_pp_term_ub_q_get_bucket_3_part2 n
  else if n ≤ 37441 then prime_heat_pp_term_ub_q_get_bucket_3_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_3_part4 n

end Twenty
end Q3.Proofs.PrimeCert
