import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket6Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket6Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket6Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket6Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Twenty

/-- Upper bounds for prime-power terms (rational), bucket 6. -/
def prime_heat_pp_term_ub_q_get_bucket_6 (n : ℕ) : ℚ :=
  if n ≤ 62507 then prime_heat_pp_term_ub_q_get_bucket_6_part1 n
  else if n ≤ 65029 then prime_heat_pp_term_ub_q_get_bucket_6_part2 n
  else if n ≤ 67427 then prime_heat_pp_term_ub_q_get_bucket_6_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_6_part4 n

end Twenty
end Q3.Proofs.PrimeCert
