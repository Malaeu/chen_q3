import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket43Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket43Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket43Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket43Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 43. -/
def prime_heat_pp_term_ub_q_get_bucket_43 (n : ℕ) : ℚ :=
  if n ≤ 432433 then prime_heat_pp_term_ub_q_get_bucket_43_part1 n
  else if n ≤ 434857 then prime_heat_pp_term_ub_q_get_bucket_43_part2 n
  else if n ≤ 437321 then prime_heat_pp_term_ub_q_get_bucket_43_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_43_part4 n

end Full
end Q3.Proofs.PrimeCert
