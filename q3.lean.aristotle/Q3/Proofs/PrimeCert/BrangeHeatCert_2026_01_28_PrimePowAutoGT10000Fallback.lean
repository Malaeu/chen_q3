import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFull

/-!
Fallback interface for the `n > 10000` prime-power interval bound.

This isolates the auto-generated GT10000 shard chain behind a single statement so
the PrimeCert mainline can continue integrating SumData/Partial updates while
the shard proofs are stabilized.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

axiom prime_heat_weight_term_le_pp_ub_of_10001_1000000_primepow_all {n : ℕ}
    (hn : IsPrimePow n) (hlo : 10001 ≤ n) (hN : n ≤ prime_cert_heat_N) :
    prime_heat_weight_term n ≤ Full.prime_heat_pp_term_ub n

end Q3.Proofs.PrimeCert
