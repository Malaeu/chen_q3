import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket86Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket86Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket86Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket86Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 86. -/
def prime_heat_pp_term_ub_q_get_bucket_86 (n : ℕ) : ℚ :=
  if n ≤ 862399 then prime_heat_pp_term_ub_q_get_bucket_86_part1 n
  else if n ≤ 865003 then prime_heat_pp_term_ub_q_get_bucket_86_part2 n
  else if n ≤ 867509 then prime_heat_pp_term_ub_q_get_bucket_86_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_86_part4 n

end Full
end Q3.Proofs.PrimeCert
