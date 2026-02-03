import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket73Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket73Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket73Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket73Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 73. -/
def prime_heat_pp_term_ub_q_get_bucket_73 (n : ℕ) : ℚ :=
  if n ≤ 732533 then prime_heat_pp_term_ub_q_get_bucket_73_part1 n
  else if n ≤ 735071 then prime_heat_pp_term_ub_q_get_bucket_73_part2 n
  else if n ≤ 737563 then prime_heat_pp_term_ub_q_get_bucket_73_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_73_part4 n

end Full
end Q3.Proofs.PrimeCert
