import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket17Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket17Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket17Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket17Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 17. -/
def prime_heat_pp_term_ub_q_get_bucket_17 (n : ℕ) : ℚ :=
  if n ≤ 172489 then prime_heat_pp_term_ub_q_get_bucket_17_part1 n
  else if n ≤ 175067 then prime_heat_pp_term_ub_q_get_bucket_17_part2 n
  else if n ≤ 177601 then prime_heat_pp_term_ub_q_get_bucket_17_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_17_part4 n

end Full
end Q3.Proofs.PrimeCert
