import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket19Part1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket19Part2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket19Part3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFullBucket19Part4
set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Full

/-- Upper bounds for prime-power terms (rational), bucket 19. -/
def prime_heat_pp_term_ub_q_get_bucket_19 (n : ℕ) : ℚ :=
  if n ≤ 192557 then prime_heat_pp_term_ub_q_get_bucket_19_part1 n
  else if n ≤ 195047 then prime_heat_pp_term_ub_q_get_bucket_19_part2 n
  else if n ≤ 197521 then prime_heat_pp_term_ub_q_get_bucket_19_part3 n
  else prime_heat_pp_term_ub_q_get_bucket_19_part4 n

end Full
end Q3.Proofs.PrimeCert
