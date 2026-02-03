import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket96Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket96Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket96Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket96Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 96. -/
def prime_heat_pp_term_ub_q_get_bucket_96 (n : ℕ) : ℚ :=
  if n ≤ 962447 then prime_heat_pp_term_ub_q_get_bucket_96_part1 n
  else if n ≤ 964889 then prime_heat_pp_term_ub_q_get_bucket_96_part2 n
  else if n ≤ 967493 then prime_heat_pp_term_ub_q_get_bucket_96_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_96_part4 n

end Full
end Q3.Proofs.PrimeCert
