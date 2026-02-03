import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket61Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket61Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket61Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket61Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 61. -/
def prime_heat_pp_term_ub_q_get_bucket_61 (n : ℕ) : ℚ :=
  if n ≤ 612583 then prime_heat_pp_term_ub_q_get_bucket_61_part1 n
  else if n ≤ 615101 then prime_heat_pp_term_ub_q_get_bucket_61_part2 n
  else if n ≤ 617387 then prime_heat_pp_term_ub_q_get_bucket_61_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_61_part4 n

end Full
end Q3.Proofs.PrimeCert
