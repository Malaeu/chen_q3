import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket40Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket40Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket40Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket40Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 40. -/
def prime_heat_pp_term_ub_q_get_bucket_40 (n : ℕ) : ℚ :=
  if n ≤ 402583 then prime_heat_pp_term_ub_q_get_bucket_40_part1 n
  else if n ≤ 405211 then prime_heat_pp_term_ub_q_get_bucket_40_part2 n
  else if n ≤ 407669 then prime_heat_pp_term_ub_q_get_bucket_40_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_40_part4 n

end Full
end Q3.Proofs.PrimeCert
