import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket80Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket80Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket80Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket80Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 80. -/
def prime_heat_pp_term_ub_q_get_bucket_80 (n : ℕ) : ℚ :=
  if n ≤ 802463 then prime_heat_pp_term_ub_q_get_bucket_80_part1 n
  else if n ≤ 804983 then prime_heat_pp_term_ub_q_get_bucket_80_part2 n
  else if n ≤ 807473 then prime_heat_pp_term_ub_q_get_bucket_80_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_80_part4 n

end Full
end Q3.Proofs.PrimeCert
