import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket97Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket97Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket97Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket97Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 97. -/
def prime_heat_pp_term_ub_q_get_bucket_97 (n : ℕ) : ℚ :=
  if n ≤ 972277 then prime_heat_pp_term_ub_q_get_bucket_97_part1 n
  else if n ≤ 974837 then prime_heat_pp_term_ub_q_get_bucket_97_part2 n
  else if n ≤ 977363 then prime_heat_pp_term_ub_q_get_bucket_97_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_97_part4 n

end Full
end Q3.Proofs.PrimeCert
