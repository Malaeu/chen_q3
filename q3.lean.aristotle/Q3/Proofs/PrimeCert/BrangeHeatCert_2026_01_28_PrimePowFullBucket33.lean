import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket33Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket33Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket33Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket33Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 33. -/
def prime_heat_pp_term_ub_q_get_bucket_33 (n : ℕ) : ℚ :=
  if n ≤ 332441 then prime_heat_pp_term_ub_q_get_bucket_33_part1 n
  else if n ≤ 334963 then prime_heat_pp_term_ub_q_get_bucket_33_part2 n
  else if n ≤ 337367 then prime_heat_pp_term_ub_q_get_bucket_33_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_33_part4 n

end Full
end Q3.Proofs.PrimeCert
