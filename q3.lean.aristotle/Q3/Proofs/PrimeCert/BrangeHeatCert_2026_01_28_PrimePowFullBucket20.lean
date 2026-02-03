import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket20Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket20Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket20Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket20Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 20. -/
def prime_heat_pp_term_ub_q_get_bucket_20 (n : ℕ) : ℚ :=
  if n ≤ 202567 then prime_heat_pp_term_ub_q_get_bucket_20_part1 n
  else if n ≤ 205157 then prime_heat_pp_term_ub_q_get_bucket_20_part2 n
  else if n ≤ 207569 then prime_heat_pp_term_ub_q_get_bucket_20_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_20_part4 n

end Full
end Q3.Proofs.PrimeCert
