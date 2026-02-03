import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket71Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket71Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket71Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket71Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 71. -/
def prime_heat_pp_term_ub_q_get_bucket_71 (n : ℕ) : ℚ :=
  if n ≤ 712417 then prime_heat_pp_term_ub_q_get_bucket_71_part1 n
  else if n ≤ 714943 then prime_heat_pp_term_ub_q_get_bucket_71_part2 n
  else if n ≤ 717397 then prime_heat_pp_term_ub_q_get_bucket_71_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_71_part4 n

end Full
end Q3.Proofs.PrimeCert
