import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket98Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket98Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket98Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket98Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 98. -/
def prime_heat_pp_term_ub_q_get_bucket_98 (n : ℕ) : ℚ :=
  if n ≤ 982489 then prime_heat_pp_term_ub_q_get_bucket_98_part1 n
  else if n ≤ 985007 then prime_heat_pp_term_ub_q_get_bucket_98_part2 n
  else if n ≤ 987391 then prime_heat_pp_term_ub_q_get_bucket_98_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_98_part4 n

end Full
end Q3.Proofs.PrimeCert
