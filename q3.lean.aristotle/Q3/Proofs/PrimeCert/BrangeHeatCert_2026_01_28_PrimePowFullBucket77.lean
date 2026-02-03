import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket77Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket77Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket77Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket77Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 77. -/
def prime_heat_pp_term_ub_q_get_bucket_77 (n : ℕ) : ℚ :=
  if n ≤ 772441 then prime_heat_pp_term_ub_q_get_bucket_77_part1 n
  else if n ≤ 774931 then prime_heat_pp_term_ub_q_get_bucket_77_part2 n
  else if n ≤ 777541 then prime_heat_pp_term_ub_q_get_bucket_77_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_77_part4 n

end Full
end Q3.Proofs.PrimeCert
