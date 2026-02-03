import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket9Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket9Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket9Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket9Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Twenty

/-- Upper bounds for prime-power terms (rational), bucket 9. -/
def prime_heat_pp_term_ub_q_get_bucket_9 (n : ℕ) : ℚ :=
  if n ≤ 92467 then prime_heat_pp_term_ub_q_get_bucket_9_part1 n
  else if n ≤ 94949 then prime_heat_pp_term_ub_q_get_bucket_9_part2 n
  else if n ≤ 97453 then prime_heat_pp_term_ub_q_get_bucket_9_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_9_part4 n

end Twenty
end Q3.Proofs.PrimeCert
