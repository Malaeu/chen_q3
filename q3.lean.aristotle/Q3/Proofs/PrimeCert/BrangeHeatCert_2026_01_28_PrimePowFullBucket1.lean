import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket1Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket1Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket1Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket1Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 1. -/
def prime_heat_pp_term_ub_q_get_bucket_1 (n : ℕ) : ℚ :=
  if n ≤ 12451 then prime_heat_pp_term_ub_q_get_bucket_1_part1 n
  else if n ≤ 14897 then prime_heat_pp_term_ub_q_get_bucket_1_part2 n
  else if n ≤ 17417 then prime_heat_pp_term_ub_q_get_bucket_1_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_1_part4 n

end Full
end Q3.Proofs.PrimeCert
