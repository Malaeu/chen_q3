import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBase
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket0
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket1
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket2
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket3
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket4
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket5
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket6
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket7
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket8
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket9
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket10
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket11
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket12
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket13
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket14
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket15
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket16
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket17
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket18
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwentyBucket19
set_option maxHeartbeats 0

/-!
Prime-heat prime-power term bounds (t_critical, tau = 0).

This file wires the bucketed lookup tables into a single accessor.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert
namespace Twenty

/-- Upper bounds for prime-power terms (rational). -/
def prime_heat_pp_term_ub_q_get (n : ℕ) : ℚ :=
  match prime_heat_pp_term_bucket_index n with
  | 0 => prime_heat_pp_term_ub_q_get_bucket_0 n
  | 1 => prime_heat_pp_term_ub_q_get_bucket_1 n
  | 2 => prime_heat_pp_term_ub_q_get_bucket_2 n
  | 3 => prime_heat_pp_term_ub_q_get_bucket_3 n
  | 4 => prime_heat_pp_term_ub_q_get_bucket_4 n
  | 5 => prime_heat_pp_term_ub_q_get_bucket_5 n
  | 6 => prime_heat_pp_term_ub_q_get_bucket_6 n
  | 7 => prime_heat_pp_term_ub_q_get_bucket_7 n
  | 8 => prime_heat_pp_term_ub_q_get_bucket_8 n
  | 9 => prime_heat_pp_term_ub_q_get_bucket_9 n
  | 10 => prime_heat_pp_term_ub_q_get_bucket_10 n
  | 11 => prime_heat_pp_term_ub_q_get_bucket_11 n
  | 12 => prime_heat_pp_term_ub_q_get_bucket_12 n
  | 13 => prime_heat_pp_term_ub_q_get_bucket_13 n
  | 14 => prime_heat_pp_term_ub_q_get_bucket_14 n
  | 15 => prime_heat_pp_term_ub_q_get_bucket_15 n
  | 16 => prime_heat_pp_term_ub_q_get_bucket_16 n
  | 17 => prime_heat_pp_term_ub_q_get_bucket_17 n
  | 18 => prime_heat_pp_term_ub_q_get_bucket_18 n
  | 19 => prime_heat_pp_term_ub_q_get_bucket_19 n
  | _ => 0

/-- Upper bounds for prime-power terms (real). -/
def prime_heat_pp_term_ub (n : ℕ) : ℝ :=
  (prime_heat_pp_term_ub_q_get n : ℝ)

/-- Prime-power bucket sums (rational). -/
def prime_heat_pp_term_ub_q_sum_bucket_0 : ℚ := (4004536336759950374440556483561 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_1 : ℚ := (307614838055265815479054325 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_2 : ℚ := (47214309414476376242617858 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_3 : ℚ := (13958586990243127483923045 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_4 : ℚ := (5508403915090045490806506 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_5 : ℚ := (2653206104299084185223349 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_6 : ℚ := (1371323107009263723806835 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_7 : ℚ := (832341945412508429326823 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_8 : ℚ := (505317443548733832444757 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_9 : ℚ := (333799705232523699516630 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_10 : ℚ := (223183796557760202201394 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_11 : ℚ := (155061244122201976632848 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_12 : ℚ := (114247400995480790637820 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_13 : ℚ := (83938243706289196258126 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_14 : ℚ := (62561464902035876240602 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_15 : ℚ := (48110390664936106944238 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_16 : ℚ := (36657348204423361754470 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_17 : ℚ := (30093057962624001943359 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_18 : ℚ := (23630379239678549830904 : ℚ) / prime_heat_pp_term_ub_den
def prime_heat_pp_term_ub_q_sum_bucket_19 : ℚ := (18859001182835027867310 : ℚ) / prime_heat_pp_term_ub_den

end Twenty
end Q3.Proofs.PrimeCert
