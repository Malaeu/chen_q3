import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket27Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket27Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket27Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket27Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 27. -/
def prime_heat_pp_term_ub_q_get_bucket_27 (n : ℕ) : ℚ :=
  if n ≤ 272369 then prime_heat_pp_term_ub_q_get_bucket_27_part1 n
  else if n ≤ 274961 then prime_heat_pp_term_ub_q_get_bucket_27_part2 n
  else if n ≤ 277411 then prime_heat_pp_term_ub_q_get_bucket_27_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_27_part4 n

end Full
end Q3.Proofs.PrimeCert
