import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket66Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket66Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket66Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket66Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 66. -/
def prime_heat_pp_term_ub_q_get_bucket_66 (n : ℕ) : ℚ :=
  if n ≤ 662449 then prime_heat_pp_term_ub_q_get_bucket_66_part1 n
  else if n ≤ 664843 then prime_heat_pp_term_ub_q_get_bucket_66_part2 n
  else if n ≤ 667417 then prime_heat_pp_term_ub_q_get_bucket_66_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_66_part4 n

end Full
end Q3.Proofs.PrimeCert
