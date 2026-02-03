import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket82Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket82Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket82Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket82Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 82. -/
def prime_heat_pp_term_ub_q_get_bucket_82 (n : ℕ) : ℚ :=
  if n ≤ 822517 then prime_heat_pp_term_ub_q_get_bucket_82_part1 n
  else if n ≤ 824911 then prime_heat_pp_term_ub_q_get_bucket_82_part2 n
  else if n ≤ 827327 then prime_heat_pp_term_ub_q_get_bucket_82_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_82_part4 n

end Full
end Q3.Proofs.PrimeCert
