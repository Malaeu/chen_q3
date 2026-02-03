import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket60Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket60Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket60Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket60Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 60. -/
def prime_heat_pp_term_ub_q_get_bucket_60 (n : ℕ) : ℚ :=
  if n ≤ 602477 then prime_heat_pp_term_ub_q_get_bucket_60_part1 n
  else if n ≤ 604997 then prime_heat_pp_term_ub_q_get_bucket_60_part2 n
  else if n ≤ 607531 then prime_heat_pp_term_ub_q_get_bucket_60_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_60_part4 n

end Full
end Q3.Proofs.PrimeCert
