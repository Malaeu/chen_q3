/-
Minimal Aristotle sandbox file for heat‑weighted Lipschitz lemmas.
No Q3.Axioms imports. Do not integrate directly; copy proof bodies only.

Goal: Prove the stated Lipschitz lemma(s). Other lemmas are marked `admit`
so Aristotle focuses on a single target.
-/


import Mathlib
import Q3.Basic.Defs
import Q3.Proofs.Params_Critical
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical Pointwise
open MeasureTheory

noncomputable section

/-- Local copy to avoid importing A3_Floor_Bounds (which pulls axioms). -/
def B_min : ℝ := 3

lemma B_min_pos : 0 < B_min := by
  norm_num [B_min]

namespace Q3

/-- Local copy of phi_shift (avoids Q3.Proofs.ShiftedWindows import). -/
def phi_shift (B t tau : ℝ) (xi : ℝ) : ℝ :=
  fejer_heat_window B t (xi - tau)

end Q3

namespace Q3.Proofs.PrimeCert

open Q3

/-- Shorthand for the test function at t_critical, tau = 0. -/
def phi_shift_critical_tau0 (B : ℝ) : ℝ → ℝ :=
  fun ξ => Q3.phi_shift B t_critical 0 ξ

/-- Heat-weighted factor used in the Lipschitz bound. -/
def heat_weight (xi : ℝ) : ℝ :=
  Real.exp (-4 * Real.pi ^ 2 * t_critical * xi ^ 2) * |xi|

/-- Margin function at t_critical, tau = 0 (local copy). -/
def margin_tau0 (B : ℝ) : ℝ :=
  arch_term (phi_shift_critical_tau0 B) -
    prime_term (phi_shift_critical_tau0 B)

lemma abs_max0_sub_max0_le (u v : ℝ) : |max 0 u - max 0 v| ≤ |u - v| := by
  by_cases hu : u ≤ 0
  · have hmaxu : max 0 u = 0 := max_eq_left hu
    by_cases hv : v ≤ 0
    · have hmaxv : max 0 v = 0 := max_eq_left hv
      simp [hmaxu, hmaxv]
    · have hv' : 0 < v := lt_of_not_ge hv
      have hmaxv : max 0 v = v := max_eq_right (le_of_lt hv')
      have hneg : u - v ≤ 0 := by linarith [hu, hv']
      calc
        |max 0 u - max 0 v| = |0 - v| := by simp [hmaxu, hmaxv]
        _ = v := by simp [abs_of_pos hv']
        _ ≤ v - u := by linarith [hu]
        _ = |u - v| := by
          have : |u - v| = -(u - v) := by simpa [abs_of_nonpos hneg]
          simp [this]
  · have hu' : 0 < u := lt_of_not_ge hu
    have hmaxu : max 0 u = u := max_eq_right (le_of_lt hu')
    by_cases hv : v ≤ 0
    · have hmaxv : max 0 v = 0 := max_eq_left hv
      have hpos : 0 ≤ u - v := by linarith [hv, hu']
      calc
        |max 0 u - max 0 v| = |u - 0| := by simp [hmaxu, hmaxv]
        _ = u := by simp [abs_of_pos hu']
        _ ≤ u - v := by linarith [hv]
        _ = |u - v| := by
          have : |u - v| = u - v := by simpa [abs_of_nonneg hpos]
          simp [this]
    · have hv' : 0 < v := lt_of_not_ge hv
      have hmaxv : max 0 v = v := max_eq_right (le_of_lt hv')
      simp [hmaxu, hmaxv]

lemma abs_inv_sub_inv_le (B1 B2 : ℝ) (hB1 : B_min ≤ B1) (hB2 : B_min ≤ B2) :
    |1 / B1 - 1 / B2| ≤ |B1 - B2| / (B_min ^ 2) := by
  have hBmin : 0 < B_min := B_min_pos
  have hB1pos : 0 < B1 := lt_of_lt_of_le hBmin hB1
  have hB2pos : 0 < B2 := lt_of_lt_of_le hBmin hB2
  have hprod_pos : 0 < B1 * B2 := mul_pos hB1pos hB2pos
  have hmin_le_prod : B_min ^ 2 ≤ B1 * B2 := by
    have hBmin_nonneg : 0 ≤ B_min := le_of_lt hBmin
    have hB1_nonneg : 0 ≤ B1 := le_of_lt hB1pos
    have hB2_nonneg : 0 ≤ B2 := le_of_lt hB2pos
    have hmul : B_min * B_min ≤ B1 * B2 := by
      exact mul_le_mul hB1 hB2 hBmin_nonneg hB1_nonneg
    simpa [pow_two] using hmul
  calc
    |1 / B1 - 1 / B2| = |(B2 - B1) / (B1 * B2)| := by
      field_simp [hB1pos.ne', hB2pos.ne']
    _ = |B1 - B2| / (B1 * B2) := by
      have hdiv : |(B2 - B1) / (B1 * B2)| = |B2 - B1| / |B1 * B2| := by
        exact (abs_div (B2 - B1) (B1 * B2))
      have habs : |B2 - B1| = |B1 - B2| := by
        simpa [abs_sub_comm]
      calc
        |(B2 - B1) / (B1 * B2)| = |B2 - B1| / |B1 * B2| := hdiv
        _ = |B1 - B2| / |B1 * B2| := by simpa [habs]
        _ = |B1 - B2| / (B1 * B2) := by simp [abs_of_pos hprod_pos]
    _ ≤ |B1 - B2| / (B_min ^ 2) := by
      have hnum_nonneg : 0 ≤ |B1 - B2| := abs_nonneg _
      have h_inv : (1 / (B1 * B2)) ≤ 1 / (B_min ^ 2) := by
        have hmin_pos' : 0 < (B_min ^ 2) := by nlinarith [hBmin]
        exact one_div_le_one_div_of_le hmin_pos' hmin_le_prod
      have : |B1 - B2| / (B1 * B2) = |B1 - B2| * (1 / (B1 * B2)) := by
        simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      have : |B1 - B2| / (B_min ^ 2) = |B1 - B2| * (1 / (B_min ^ 2)) := by
        simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      nlinarith [hnum_nonneg, h_inv]

lemma fejer_heat_window_lipschitz_B_exp (B1 B2 t xi : ℝ)
    (hB1 : B_min ≤ B1) (hB2 : B_min ≤ B2) (ht : 0 ≤ t) :
    |fejer_heat_window B1 t xi - fejer_heat_window B2 t xi| ≤
      Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2) * |xi| * |B1 - B2| / (B_min ^ 2) := by
  have hmax :
      |max 0 (1 - |xi| / B1) - max 0 (1 - |xi| / B2)| ≤
        |(1 - |xi| / B1) - (1 - |xi| / B2)| := by
    simpa using (abs_max0_sub_max0_le (1 - |xi| / B1) (1 - |xi| / B2))
  have hdiff :
      |(1 - |xi| / B1) - (1 - |xi| / B2)| = |xi| * |1 / B1 - 1 / B2| := by
    have h :
        (1 - |xi| / B1) - (1 - |xi| / B2) = |xi| * (1 / B2 - 1 / B1) := by
      ring_nf
    calc
      |(1 - |xi| / B1) - (1 - |xi| / B2)|
          = |(|xi| * (1 / B2 - 1 / B1))| := by simpa [h]
      _ = |xi| * |1 / B2 - 1 / B1| := by simp [abs_mul]
      _ = |xi| * |1 / B1 - 1 / B2| := by simpa [abs_sub_comm]
  have hbound_inv : |1 / B1 - 1 / B2| ≤ |B1 - B2| / (B_min ^ 2) :=
    abs_inv_sub_inv_le B1 B2 hB1 hB2
  have hmax_le :
      |max 0 (1 - |xi| / B1) - max 0 (1 - |xi| / B2)| ≤
        |xi| * |B1 - B2| / (B_min ^ 2) := by
    calc
      |max 0 (1 - |xi| / B1) - max 0 (1 - |xi| / B2)|
          ≤ |(1 - |xi| / B1) - (1 - |xi| / B2)| := hmax
      _ = |xi| * |1 / B1 - 1 / B2| := hdiff
      _ ≤ |xi| * (|B1 - B2| / (B_min ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hbound_inv (abs_nonneg xi)
      _ = |xi| * |B1 - B2| / (B_min ^ 2) := by
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  -- apply exp factor (≤ 1)
  have hexp_nonneg : 0 ≤ Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2) := by
    exact Real.exp_nonneg _
  set E : ℝ := Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2)
  have hfej1 : fejer_heat_window B1 t xi = max 0 (1 - |xi| / B1) * E := by
    simp [fejer_heat_window, E, mul_comm, mul_left_comm, mul_assoc]
  have hfej2 : fejer_heat_window B2 t xi = max 0 (1 - |xi| / B2) * E := by
    simp [fejer_heat_window, E, mul_comm, mul_left_comm, mul_assoc]
  calc
    |fejer_heat_window B1 t xi - fejer_heat_window B2 t xi|
        = |(max 0 (1 - |xi| / B1) * E) - (max 0 (1 - |xi| / B2) * E)| := by
          simp [hfej1, hfej2]
    _ = |(max 0 (1 - |xi| / B1) - max 0 (1 - |xi| / B2)) * E| := by
          ring_nf
    _ = E * |max 0 (1 - |xi| / B1) - max 0 (1 - |xi| / B2)| := by
          simp [abs_mul, abs_of_nonneg hexp_nonneg, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ E * (|xi| * |B1 - B2| / (B_min ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hmax_le hexp_nonneg
    _ = Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2) * |xi| * |B1 - B2| / (B_min ^ 2) := by
          simp [E, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

lemma phi_shift_lipschitz_B_exp (B1 B2 xi : ℝ)
    (hB1 : B_min ≤ B1) (hB2 : B_min ≤ B2) :
    |Q3.phi_shift B1 t_critical 0 xi - Q3.phi_shift B2 t_critical 0 xi| ≤
      Real.exp (-4 * Real.pi ^ 2 * t_critical * xi ^ 2) * |xi| * |B1 - B2| / (B_min ^ 2) := by
  simpa [Q3.phi_shift] using
    (fejer_heat_window_lipschitz_B_exp (B1:=B1) (B2:=B2) (t:=t_critical) (xi:=xi)
      hB1 hB2 (le_of_lt Q3.t_critical_pos))

/--
Given bounds on the heat-weighted arch integral, show Lipschitz in B.

PROVIDED SOLUTION
1) Use `phi_shift_lipschitz_B_exp` to get pointwise bound on
   `|phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ|`.
2) Rewrite `arch_term` difference as integral of `a_star ξ * (Φ1-Φ2)`.
3) Apply `abs_integral_le_integral_abs` and bound integrand by
   `|a_star ξ| * heat_weight ξ * |B1-B2|/(B_min^2)`.
4) Pull out constant `|B1-B2|/(B_min^2)` and apply `h_arch_heat`.
-/
lemma arch_term_Lipschitz_heat
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_arch_heat :
      ∫ ξ, |a_star ξ| * heat_weight ξ ≤ prime_cert_L_arch_heat_raw) :
    |arch_term (phi_shift_critical_tau0 B1) -
      arch_term (phi_shift_critical_tau0 B2)| ≤
      (prime_cert_L_arch_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
  sorry

/--
Prime-term Lipschitz bound under heat-weighted sum control.

PROVIDED SOLUTION
1) Use `phi_shift_lipschitz_B_exp` at `xi_n n` to bound pointwise.
2) Use `w_Q_nonneg` to drop absolute values on weights.
3) Apply `abs_tsum_le_tsum_abs` + `tsum_le_tsum` to bound by
   `(|B1-B2|/(B_min^2)) * ∑' n, w_Q n * heat_weight (xi_n n)`.
4) Apply `h_prime_heat`.
-/
lemma prime_term_Lipschitz_heat
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_prime_heat :
      ∑' n, w_Q n * heat_weight (xi_n n) ≤ prime_cert_L_prime_heat_raw) :
    |prime_term (phi_shift_critical_tau0 B1) -
      prime_term (phi_shift_critical_tau0 B2)| ≤
      (prime_cert_L_prime_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
  sorry

/--
Combine arch/prime bounds into a margin Lipschitz bound.

PROVIDED SOLUTION
Use the two Lipschitz bounds and triangle inequality,
then apply `h_total` to simplify constants.
-/
lemma margin_Lipschitz_heat_of_bounds
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_arch_heat :
      ∫ ξ, |a_star ξ| * heat_weight ξ ≤ prime_cert_L_arch_heat_raw)
    (h_prime_heat :
      ∑' n, w_Q n * heat_weight (xi_n n) ≤ prime_cert_L_prime_heat_raw)
    (h_total :
      (prime_cert_L_arch_heat_raw + prime_cert_L_prime_heat_raw) / (B_min ^ 2) ≤
        prime_cert_L_total_heat_ub) :
    |margin_tau0 B1 - margin_tau0 B2| ≤
      prime_cert_L_total_heat_ub * |B1 - B2| := by
  sorry

end Q3.Proofs.PrimeCert
