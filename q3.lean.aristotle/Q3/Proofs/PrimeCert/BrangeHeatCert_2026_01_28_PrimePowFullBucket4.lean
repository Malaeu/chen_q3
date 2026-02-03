import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket4Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket4Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket4Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket4Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 4. -/
def prime_heat_pp_term_ub_q_get_bucket_4 (n : ℕ) : ℚ :=
  if n ≤ 42433 then prime_heat_pp_term_ub_q_get_bucket_4_part1 n
  else if n ≤ 44927 then prime_heat_pp_term_ub_q_get_bucket_4_part2 n
  else if n ≤ 47533 then prime_heat_pp_term_ub_q_get_bucket_4_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_4_part4 n

end Full
end Q3.Proofs.PrimeCert
