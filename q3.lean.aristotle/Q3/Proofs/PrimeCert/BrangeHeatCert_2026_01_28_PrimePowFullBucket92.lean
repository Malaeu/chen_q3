import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket92Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket92Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket92Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket92Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 92. -/
def prime_heat_pp_term_ub_q_get_bucket_92 (n : ℕ) : ℚ :=
  if n ≤ 922511 then prime_heat_pp_term_ub_q_get_bucket_92_part1 n
  else if n ≤ 924907 then prime_heat_pp_term_ub_q_get_bucket_92_part2 n
  else if n ≤ 927431 then prime_heat_pp_term_ub_q_get_bucket_92_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_92_part4 n

end Full
end Q3.Proofs.PrimeCert
