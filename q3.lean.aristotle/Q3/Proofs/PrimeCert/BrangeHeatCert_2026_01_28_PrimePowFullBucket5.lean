import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket5Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket5Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket5Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket5Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 5. -/
def prime_heat_pp_term_ub_q_get_bucket_5 (n : ℕ) : ℚ :=
  if n ≤ 52517 then prime_heat_pp_term_ub_q_get_bucket_5_part1 n
  else if n ≤ 55049 then prime_heat_pp_term_ub_q_get_bucket_5_part2 n
  else if n ≤ 57487 then prime_heat_pp_term_ub_q_get_bucket_5_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_5_part4 n

end Full
end Q3.Proofs.PrimeCert
