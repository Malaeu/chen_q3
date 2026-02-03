import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket67Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket67Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket67Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket67Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 67. -/
def prime_heat_pp_term_ub_q_get_bucket_67 (n : ℕ) : ℚ :=
  if n ≤ 672473 then prime_heat_pp_term_ub_q_get_bucket_67_part1 n
  else if n ≤ 674987 then prime_heat_pp_term_ub_q_get_bucket_67_part2 n
  else if n ≤ 677561 then prime_heat_pp_term_ub_q_get_bucket_67_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_67_part4 n

end Full
end Q3.Proofs.PrimeCert
