import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket24Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket24Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket24Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket24Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 24. -/
def prime_heat_pp_term_ub_q_get_bucket_24 (n : ℕ) : ℚ :=
  if n ≤ 242453 then prime_heat_pp_term_ub_q_get_bucket_24_part1 n
  else if n ≤ 244957 then prime_heat_pp_term_ub_q_get_bucket_24_part2 n
  else if n ≤ 247579 then prime_heat_pp_term_ub_q_get_bucket_24_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_24_part4 n

end Full
end Q3.Proofs.PrimeCert
