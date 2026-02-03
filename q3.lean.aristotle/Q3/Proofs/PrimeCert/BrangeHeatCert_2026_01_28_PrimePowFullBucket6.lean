import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket6Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket6Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket6Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket6Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 6. -/
def prime_heat_pp_term_ub_q_get_bucket_6 (n : ℕ) : ℚ :=
  if n ≤ 62507 then prime_heat_pp_term_ub_q_get_bucket_6_part1 n
  else if n ≤ 65029 then prime_heat_pp_term_ub_q_get_bucket_6_part2 n
  else if n ≤ 67427 then prime_heat_pp_term_ub_q_get_bucket_6_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_6_part4 n

end Full
end Q3.Proofs.PrimeCert
