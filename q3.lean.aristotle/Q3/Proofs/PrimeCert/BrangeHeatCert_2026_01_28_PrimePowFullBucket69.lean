import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket69Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket69Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket69Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket69Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 69. -/
def prime_heat_pp_term_ub_q_get_bucket_69 (n : ℕ) : ℚ :=
  if n ≤ 692521 then prime_heat_pp_term_ub_q_get_bucket_69_part1 n
  else if n ≤ 694997 then prime_heat_pp_term_ub_q_get_bucket_69_part2 n
  else if n ≤ 697387 then prime_heat_pp_term_ub_q_get_bucket_69_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_69_part4 n

end Full
end Q3.Proofs.PrimeCert
