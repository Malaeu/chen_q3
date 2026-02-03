import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket7Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket7Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket7Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket7Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 7. -/
def prime_heat_pp_term_ub_q_get_bucket_7 (n : ℕ) : ℚ :=
  if n ≤ 72361 then prime_heat_pp_term_ub_q_get_bucket_7_part1 n
  else if n ≤ 74897 then prime_heat_pp_term_ub_q_get_bucket_7_part2 n
  else if n ≤ 77491 then prime_heat_pp_term_ub_q_get_bucket_7_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_7_part4 n

end Full
end Q3.Proofs.PrimeCert
