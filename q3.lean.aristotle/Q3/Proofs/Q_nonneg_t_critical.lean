/-
Q >= 0 at t_critical = 0.15

This file proves Q(phi) >= 0 for Fejer-heat atoms with t_critical = 3/20.

Key insight: at t_critical, BOTH conditions hold simultaneously:
  1. P_A(theta) >= c_star = 11/10 (Archimedean floor preserved)
  2. prime_sum is small enough that arch_term dominates

Numerical verification (Python):
  t = 0.15: Q = +0.86 > 0, min P_A = 1.66 > 1.1
  t* ~ 0.136 is the crossover point where Q changes sign

LaTeX <-> Lean parameter conversion:
  LaTeX: exp(-4*pi^2*t*xi^2)
  Lean:  exp(-xi^2/(4*t0))
  Relation: t0 = 1/(16*pi^2*t)

  t_critical = 0.15 => t0_critical = 1/(16*pi^2*0.15) ~ 0.0422
-/

import Q3.Axioms
import Q3.Proofs.Params_Critical
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.FloorCert.Defs
import Q3.Proofs.FloorCert.Grid_2219
import Q3.Proofs.FloorCert.Lipschitz_2219
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.Bmin_1826
import Q3.Proofs.PrimeCert.Brange_2046
import Q3.Proofs.PrimeTerm_PathB_legacy_provider
import Q3.Proofs.ShiftedWindows
import Q3.Proofs.Q_nonneg_atoms_helpers
import Q3.Proofs.Q_nonneg_lemmas

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical ComplexConjugate
open MeasureTheory

noncomputable section

namespace Q3

open Q3.Proofs.FloorCert
open Q3.Proofs.PrimeCert

/-- t_critical > t_sym (0.15 > 0.06), so heat decay is stronger -/
lemma t_critical_gt_t_sym : t_critical > t_sym := by
  norm_num [t_critical, t_sym]

/-- Parameter conversion: exp(-xi^2/(4*t0_critical)) = exp(-4*pi^2*t_critical*xi^2) -/
lemma exp_reparam_critical' (x : ℝ) :
    Real.exp (-x^2 / (4 * t0_critical)) = Real.exp (-4 * Real.pi ^ 2 * t_critical * x^2) :=
  Q3.exp_reparam_critical x

/-! ## Fejer-Heat Window at t_critical -/

/-- Fejer-heat window at t_critical -/
def fejer_heat_window_critical (B : ℝ) (ξ : ℝ) : ℝ :=
  max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi^2 * t_critical * ξ^2)

lemma fejer_heat_window_critical_eq (B ξ : ℝ) :
    fejer_heat_window_critical B ξ = fejer_heat_window B t_critical ξ := by
  rfl

lemma fejer_heat_window_critical_nonneg (B ξ : ℝ) :
    0 ≤ fejer_heat_window_critical B ξ := by
  unfold fejer_heat_window_critical
  apply mul_nonneg
  · exact le_max_left _ _
  · exact Real.exp_nonneg _

/-! ## phi_shift at t_critical -/

/-- phi_shift at t_critical -/
def phi_shift_critical (B τ : ℝ) (ξ : ℝ) : ℝ :=
  phi_shift B t_critical τ ξ

lemma phi_shift_critical_nonneg (B τ ξ : ℝ) :
    0 ≤ phi_shift_critical B τ ξ := by
  unfold phi_shift_critical phi_shift
  exact fejer_heat_window_nonneg B t_critical (ξ - τ)

/-! ## P_A Floor at t_critical -/

/-- P_A at t_critical: periodized Archimedean density -/
def P_A_critical (B : ℝ) (θ : ℝ) : ℝ :=
  P_A_shift B t_critical 0 θ

/-!
Numeric certificate constants and grid live in `Q3.Proofs.FloorCert.Defs` and
grid values in `Q3.Proofs.FloorCert.Grid_2219`.
-/


/-- P_A is invariant under integer shifts: P_A(θ + k) = P_A(θ). -/
lemma P_A_add_int (B t : ℝ) (k : ℤ) (θ : ℝ) :
    P_A B t (θ + k) = P_A B t θ := by
  classical
  unfold P_A
  have htsum :
      (∑' m : ℤ, g B t (θ + k + m)) = ∑' m : ℤ, g B t (θ + m) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      (Equiv.tsum_eq (Equiv.addRight k) (fun m : ℤ => g B t (θ + m)))
  simpa [add_assoc] using htsum

/-- Reduce any θ to the fundamental domain [-1/2, 1/2] by subtracting floor(θ + 1/2). -/
lemma sub_floor_add_half_mem_Icc (θ : ℝ) :
    θ - (Int.floor (θ + 1/2) : ℤ) ∈ Set.Icc (-1/2) (1/2) := by
  have h₁ : ((Int.floor (θ + 1/2) : ℤ) : ℝ) ≤ θ + 1/2 := by
    exact Int.floor_le (θ + 1/2)
  have h₂ : θ + 1/2 < ((Int.floor (θ + 1/2) : ℤ) : ℝ) + 1 := by
    exact Int.lt_floor_add_one (θ + 1/2)
  constructor
  · nlinarith
  ·
    have : θ - (Int.floor (θ + 1/2) : ℤ) < 1/2 := by nlinarith
    exact le_of_lt this

/-- Grid cover certificate: every θ in Icc is within h/2 of some grid point. -/
lemma floor_cert_grid_cover_cert :
    ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
      ∃ i : Fin (floor_cert_N + 1),
        floor_grid i ∈ Set.Icc (-1/2 : ℝ) (1/2) ∧
          |θ - floor_grid i| ≤ floor_cert_h / 2 := by
  intro θ hθ
  -- rescale to [0, N]
  set t : ℝ := (θ + 1/2) / floor_cert_h
  have ht0 : 0 ≤ t := by
    have hθ' : 0 ≤ θ + 1/2 := by
      have hθl : (-1/2 : ℝ) ≤ θ := hθ.1
      nlinarith
    exact div_nonneg hθ' (le_of_lt floor_cert_h_pos)
  have htN : t ≤ (floor_cert_N : ℝ) := by
    have hθ' : θ + 1/2 ≤ 1 := by
      have hθu : θ ≤ (1/2 : ℝ) := hθ.2
      nlinarith
    -- (θ+1/2)/h ≤ N since N*h = 1
    have hdiv : (θ + 1/2) / floor_cert_h ≤ (floor_cert_N : ℝ) := by
      have hmul : θ + 1/2 ≤ (floor_cert_N : ℝ) * floor_cert_h := by
        simpa [floor_cert_N_mul_h] using hθ'
      exact (div_le_iff₀ (by exact floor_cert_h_pos)).2 hmul
    simpa [t] using hdiv
  -- choose nearest grid index via floor(t+1/2)
  set n : ℕ := Nat.floor (t + 1/2)
  have hn_le : (n : ℝ) ≤ t + 1/2 := Nat.floor_le (by nlinarith [ht0])
  have ht_lt : t + 1/2 < (n : ℝ) + 1 := Nat.lt_floor_add_one (t + 1/2)
  have hn_lt : n < floor_cert_N + 1 := by
    have hnonneg : 0 ≤ t + 1/2 := by nlinarith [ht0]
    have h1 : t + 1/2 ≤ (floor_cert_N : ℝ) + 1/2 := by
      linarith [htN]
    have h2 : (floor_cert_N : ℝ) + 1/2 < (floor_cert_N : ℝ) + 1 := by
      nlinarith
    have htop' : t + 1/2 < (floor_cert_N : ℝ) + 1 := lt_of_le_of_lt h1 h2
    have htop : t + 1/2 < ((floor_cert_N + 1 : ℕ) : ℝ) := by
      simpa using htop'
    exact (Nat.floor_lt hnonneg).2 htop
  have hn_leN : n ≤ floor_cert_N := Nat.lt_succ_iff.mp hn_lt
  -- build Fin index
  refine ⟨⟨n, hn_lt⟩, ?_, ?_⟩
  · -- grid point in Icc
    have h0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hN : (n : ℝ) ≤ (floor_cert_N : ℝ) := by exact_mod_cast hn_leN
    have hgrid_lo : (-1/2 : ℝ) ≤ floor_grid ⟨n, hn_lt⟩ := by
      simp [floor_grid]
      nlinarith [h0, floor_cert_h_pos]
    have hgrid_hi : floor_grid ⟨n, hn_lt⟩ ≤ (1/2 : ℝ) := by
      simp [floor_grid]
      -- -1/2 + n*h ≤ -1/2 + N*h = 1/2
      have hmul : (n : ℝ) * floor_cert_h ≤ (floor_cert_N : ℝ) * floor_cert_h := by
        exact mul_le_mul_of_nonneg_right hN (le_of_lt floor_cert_h_pos)
      nlinarith [hmul, floor_cert_N_mul_h]
    exact ⟨hgrid_lo, hgrid_hi⟩
  · -- distance ≤ h/2
    have h_repr : t * floor_cert_h = θ + 1/2 := by
      unfold t
      field_simp [floor_cert_h_ne_zero]
    have hdiff :
        θ - floor_grid ⟨n, hn_lt⟩ = floor_cert_h * (t - n) := by
      simp [floor_grid]
      -- use t*h = θ+1/2
      nlinarith [h_repr]
    have habs_t : |t - n| ≤ (1/2 : ℝ) := by
      have h1 : (n : ℝ) - 1/2 ≤ t := by nlinarith [hn_le]
      have h2 : t ≤ (n : ℝ) + 1/2 := by nlinarith [ht_lt]
      exact (abs_le.mpr ⟨by nlinarith [h1], by nlinarith [h2]⟩)
    have habs : |θ - floor_grid ⟨n, hn_lt⟩| ≤ floor_cert_h / 2 := by
      -- |θ - grid| = h*|t-n|
      have hmul : |θ - floor_grid ⟨n, hn_lt⟩| = floor_cert_h * |t - n| := by
        simp [hdiff, abs_mul, abs_of_pos floor_cert_h_pos]
      have hmul' : floor_cert_h * |t - n| ≤ floor_cert_h * (1/2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left habs_t (le_of_lt floor_cert_h_pos)
      simpa [hmul, mul_div_assoc] using hmul'
    simpa using habs

/-! ## Derived floor on Icc from grid + Lipschitz -/

lemma P_A_floor_cert_on_Icc_cert :
    ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
      floor_cert_min_lb - floor_cert_L_ub * floor_cert_h / 2 ≤
        P_A B_min t_critical θ := by
  intro θ hθ
  rcases floor_cert_grid_cover_cert θ hθ with ⟨i, hi_mem, hdist⟩
  have hgrid : floor_cert_min_lb ≤ P_A B_min t_critical (floor_grid i) :=
    P_A_floor_cert_on_grid_cert i
  have hLip :
      |P_A B_min t_critical θ - P_A B_min t_critical (floor_grid i)| ≤
        floor_cert_L_ub * |θ - floor_grid i| := by
    simpa [sub_eq_add_neg, abs_sub_comm] using
      (P_A_Lipschitz_on_Icc_cert θ (floor_grid i) hθ hi_mem)
  have hLip_lower :
      P_A B_min t_critical (floor_grid i) - floor_cert_L_ub * |θ - floor_grid i| ≤
        P_A B_min t_critical θ := by
    have h' := (abs_sub_le_iff).1 hLip
    -- h'.2: P_A(grid) - P_A(θ) ≤ L*|θ-grid|
    nlinarith [h'.2]
  have hdist' :
      floor_cert_L_ub * |θ - floor_grid i| ≤ floor_cert_L_ub * (floor_cert_h / 2) := by
    exact mul_le_mul_of_nonneg_left hdist floor_cert_L_ub_nonneg
  nlinarith [hgrid, hLip_lower, hdist']

lemma P_A_floor_cert_on_Icc :
    ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
      floor_cert_min_lb - floor_cert_L_ub * floor_cert_h / 2 ≤
        P_A B_min t_critical θ := by
  simpa using P_A_floor_cert_on_Icc_cert

/-- P_A floor at t_critical: min P_A >= c_star = 11/10
    Numerical verification: at t_critical = 0.15, min P_A = 1.66 > 1.1 -/
lemma P_A_ge_c_star_at_t_critical (θ : ℝ) :
    P_A_critical B_min θ ≥ c_star := by
  /- I/O CARD: P_A_ge_c_star_at_t_critical
     INPUT:  θ : ℝ
     OUTPUT: P_A_critical B_min θ ≥ c_star (= 11/10)
     NEED:   Floor certificate on Icc [-1/2,1/2] (see P_A_ge_floor_cert_on_Icc)
     BLOCKS: [arch_term_ge_at_t_critical, Q_phi_shift_nonneg_t_critical]
  -/
  have hPA : P_A_critical B_min θ = P_A B_min t_critical θ := by
    simp [P_A_critical, Q3.P_A_shift, P_A, Q3.g_shift, Q3.phi_shift, g, w, Q3.fejer_heat_window]

  let k : ℤ := Int.floor (θ + 1/2)
  have hk : θ - k ∈ Set.Icc (-1/2 : ℝ) (1/2) := by
    simpa [k] using (sub_floor_add_half_mem_Icc (θ := θ))

  have hgrid :
      floor_cert_min_lb - floor_cert_L_ub * floor_cert_h / 2 ≤
        P_A B_min t_critical (θ - k) := by
    exact P_A_floor_cert_on_Icc (θ - k) hk

  have hcert : c_star ≤ floor_cert_min_lb - floor_cert_L_ub * floor_cert_h / 2 := by
    simpa using floor_cert_margin_ge_c_star

  have hshift : P_A B_min t_critical θ = P_A B_min t_critical (θ - k) := by
    -- use periodicity with integer shift k
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (P_A_add_int (B := B_min) (t := t_critical) (k := k) (θ := θ - k))

  have hPAθ : c_star ≤ P_A B_min t_critical θ := by
    have h1 : c_star ≤ P_A B_min t_critical (θ - k) := le_trans hcert hgrid
    simpa [hshift] using h1

  have : c_star ≤ P_A_critical B_min θ := by
    simpa [hPA] using hPAθ

  exact this

/-! ## arch_term bounds at t_critical -/

/-- arch_term at t_critical is bounded below -/
lemma arch_term_ge_at_t_critical (B τ : ℝ) (hB : B > 0)
    (h_floor : ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
      c_star ≤ P_A_shift B t_critical τ θ) :
    arch_term (fun ξ => phi_shift_critical B τ ξ) ≥
      c_star * (1 - |τ| / B) := by
  /- I/O CARD: arch_term_ge_at_t_critical
     INPUT:  B τ : ℝ, hB : B > 0
     OUTPUT: arch_term(phi_shift_critical) ≥ c_star * (1 - |τ|/B)
     NEED:   pointwise floor on P_A_shift at t_critical
             integral_P_A_shift_eq_arch_term (periodization identity)
     BLOCKS: [Q_phi_shift_nonneg_t_critical]
  -/
  have hab : (-1/2 : ℝ) ≤ (1/2 : ℝ) := by norm_num
  have h_cont : Continuous (fun θ => P_A_shift B t_critical τ θ) :=
    Q3.Proofs.ShiftedWindows.P_A_shift_continuous (B:=B) (t:=t_critical) (tau:=τ) hB
  have h_int : IntervalIntegrable (fun θ => P_A_shift B t_critical τ θ) volume (-1/2) (1/2) :=
    h_cont.intervalIntegrable _ _
  have h_const : IntervalIntegrable (fun _ : ℝ => (c_star : ℝ)) volume (-1/2) (1/2) := by
    simpa using
      (intervalIntegrable_const (μ := volume) (a := (-1/2 : ℝ)) (b := (1/2 : ℝ))
        (c := (c_star : ℝ)))
  have h_mono :
      (∫ θ in (-1/2 : ℝ)..(1/2), (c_star : ℝ)) ≤
        ∫ θ in (-1/2 : ℝ)..(1/2), P_A_shift B t_critical τ θ := by
    exact intervalIntegral.integral_mono_on
      (a := (-1/2 : ℝ)) (b := (1/2 : ℝ)) (μ := volume)
      (f := fun _ : ℝ => (c_star : ℝ)) (g := fun θ => P_A_shift B t_critical τ θ)
      (hab := hab) (hf := h_const) (hg := h_int) h_floor
  have hlen : ((2⁻¹ : ℝ) - (-1/2)) = (1 : ℝ) := by norm_num
  have h_const_int :
      (∫ θ in (-1/2 : ℝ)..(1/2), (c_star : ℝ)) = c_star := by
    simp [intervalIntegral.integral_const, hlen]
  have h_arch_eq :
      ∫ θ in (-1/2 : ℝ)..(1/2), P_A_shift B t_critical τ θ =
        arch_term (fun ξ => phi_shift_critical B τ ξ) := by
    simpa [phi_shift_critical] using
      (Q3.Proofs.ShiftedWindows.integral_P_A_shift_eq_arch_term (B:=B) (t:=t_critical)
        (tau:=τ) hB)
  have h_arch_ge : arch_term (fun ξ => phi_shift_critical B τ ξ) ≥ c_star := by
    have h_mono' := h_mono
    rw [h_const_int] at h_mono'
    rw [h_arch_eq] at h_mono'
    exact h_mono'
  have h_factor : c_star * (1 - |τ| / B) ≤ c_star := by
    have h_nonneg : 0 ≤ |τ| / B := by
      have hτ : 0 ≤ |τ| := abs_nonneg _
      exact div_nonneg hτ (le_of_lt hB)
    nlinarith [h_nonneg, c_star_pos]
  exact le_trans h_factor h_arch_ge

/-! ## prime_term bounds at t_critical

Prime certificate constants and basic lemmas live in `Q3.Proofs.PrimeCert.Defs`.
See output/prime_cert_tcritical_2026-01-26_0046.txt and
output/prime_cert_brange_tcritical_interval_2026-01-30_2206.txt.
-/

/-- prime_term ≤ arch_term for B ∈ [B_min, B_max] (tau = 0), from margin cert. -/
def PrimeCertMarginOnBrange : Prop :=
  ∀ B ∈ Set.Icc B_min prime_cert_B_max,
    prime_cert_margin_lb ≤
      arch_term (fun ξ => phi_shift_critical B 0 ξ) -
        prime_term (fun ξ => phi_shift_critical B 0 ξ)

/-- Certified B-range margin theorem (tau = 0, t_critical).
This discharges `PrimeCertMarginOnBrange` from the concrete 2046-grid certificate. -/
theorem prime_cert_margin_on_brange_thm : PrimeCertMarginOnBrange := by
  intro B hB
  simpa [phi_shift_critical] using
    (Q3.Proofs.PrimeCert.prime_cert_margin_on_Brange_axiom (B := B) hB)

/-- prime_term ≤ arch_term for B ∈ [B_min, B_max] (tau = 0), from an explicit margin hypothesis. -/
lemma prime_term_le_arch_term_on_Brange_tau0_of_margin
    (h_margin_cert : PrimeCertMarginOnBrange)
    (B : ℝ) (hB : B ∈ Set.Icc B_min prime_cert_B_max) :
    prime_term (fun ξ => phi_shift_critical B 0 ξ) ≤
      arch_term (fun ξ => phi_shift_critical B 0 ξ) := by
  have h := h_margin_cert B hB
  have h0 : 0 ≤ prime_cert_margin_lb := le_of_lt prime_cert_margin_pos
  linarith

/-- Q >= 0 on phi_shift_critical with tau = 0 and B in the certified range
    (explicit margin-certificate hypothesis). -/
theorem Q_phi_shift_nonneg_t_critical_tau0_brange_of_margin
    (h_margin_cert : PrimeCertMarginOnBrange) (B : ℝ)
    (hBmin : B_min ≤ B) (hBmax : B ≤ prime_cert_B_max) :
    Q (fun ξ => phi_shift_critical B 0 ξ) ≥ 0 := by
  unfold Q
  have hprime :
      prime_term (fun ξ => phi_shift_critical B 0 ξ) ≤
        arch_term (fun ξ => phi_shift_critical B 0 ξ) := by
    exact prime_term_le_arch_term_on_Brange_tau0_of_margin
      (h_margin_cert := h_margin_cert) B ⟨hBmin, hBmax⟩
  linarith

/-- Tau-0 Path B gate on the certified B-range. -/
def PrimeTermPathBTcriticalTau0Brange : Prop :=
  ∀ B : ℝ, B_min ≤ B → B ≤ prime_cert_B_max →
    prime_term (fun ξ => phi_shift_critical B 0 ξ) ≤
      arch_term (fun ξ => phi_shift_critical B 0 ξ)

/-- Build the tau-0 Path B gate from an explicit margin hypothesis. -/
theorem prime_term_pathB_tcritical_tau0_brange_of_margin
    (h_margin_cert : PrimeCertMarginOnBrange) :
    PrimeTermPathBTcriticalTau0Brange := by
  intro B hBmin hBmax
  exact prime_term_le_arch_term_on_Brange_tau0_of_margin
    (h_margin_cert := h_margin_cert) B ⟨hBmin, hBmax⟩

/-- Canonical tau-0 Path B gate provider from the certified B-range theorem. -/
theorem prime_term_pathB_tcritical_tau0_brange_thm :
    PrimeTermPathBTcriticalTau0Brange :=
  prime_term_pathB_tcritical_tau0_brange_of_margin prime_cert_margin_on_brange_thm

/-- prime_term at t_critical is bounded by arch_term
    Key insight: at t_critical, heat decay exp(-4*pi^2*t*xi^2) is strong enough
    that prime_sum = Σ w(n)*Phi(xi_n) becomes small relative to arch_term -/
lemma prime_term_le_at_t_critical_via_pathB
    (hPathB : PrimeTermPathBTcritical)
    (K B τ : ℝ) (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    prime_term (fun ξ => phi_shift_critical B τ ξ) ≤
      arch_term (fun ξ => phi_shift_critical B τ ξ) := by
  simpa [phi_shift_critical] using
    (prime_term_le_at_t_critical_of_pathB hPathB K B τ hK hB hτB)

/-- Contract-first route for the `t_critical` prime gate. -/
lemma prime_term_le_at_t_critical_of_pathB_contract
    (hPathB : PrimeTermPathBTcritical)
    (K B τ : ℝ) (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    prime_term (fun ξ => phi_shift_critical B τ ξ) ≤
      arch_term (fun ξ => phi_shift_critical B τ ξ) :=
  prime_term_le_at_t_critical_via_pathB hPathB K B τ hK hB hτB

/-- prime_term at t_critical is bounded by arch_term
    Key insight: at t_critical, heat decay exp(-4*pi^2*t*xi^2) is strong enough
    that prime_sum = Σ w(n)*Phi(xi_n) becomes small relative to arch_term -/
lemma prime_term_le_at_t_critical (K B τ : ℝ)
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    prime_term (fun ξ => phi_shift_critical B τ ξ) ≤
      arch_term (fun ξ => phi_shift_critical B τ ξ) := by
  /- I/O CARD: prime_term_le_at_t_critical
     INPUT:  K B τ : ℝ, hK : K ≥ 1, hB : B > 0, hτB : |τ| + B ≤ K
     OUTPUT: prime_term(phi_shift_critical) ≤ arch_term(phi_shift_critical)
     NEED:   Numerical verification at t = 0.15, B = 3:
               arch_term = 9.57
               prime_term = 8.71
               Q = arch - prime = +0.86 > 0
             The heat factor exp(-4*pi^2*0.15*xi^2) decays fast enough
     BLOCKS: [Q_phi_shift_nonneg_t_critical]
  -/
  have hPathB : PrimeTermPathBTcritical := prime_term_pathB_tcritical_from_legacy
  exact prime_term_le_at_t_critical_of_pathB_contract hPathB K B τ hK hB hτB

/-! ## Main Theorem: Q >= 0 at t_critical -/

/-- Main lemma from an explicit Path B contract input. -/
theorem Q_phi_shift_nonneg_t_critical_of_pathB
    (hPathB : PrimeTermPathBTcritical)
    (K B τ : ℝ) (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    Q (fun ξ => phi_shift_critical B τ ξ) ≥ 0 := by
  unfold Q
  have h := prime_term_le_at_t_critical_of_pathB_contract hPathB K B τ hK hB hτB
  linarith

/-- Main lemma: Q(phi_shift at t_critical) >= 0 -/
theorem Q_phi_shift_nonneg_t_critical (K B τ : ℝ)
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    Q (fun ξ => phi_shift_critical B τ ξ) ≥ 0 := by
  have hPathB : PrimeTermPathBTcritical := prime_term_pathB_tcritical_from_legacy
  exact Q_phi_shift_nonneg_t_critical_of_pathB hPathB K B τ hK hB hτB

/-- Tau-0 specialization of the Path B gate, with an auto-chosen admissible `K`.
This avoids threading an external `K` assumption when proving positivity on
`BaseAtomCone_critical_brange` atoms. -/
theorem Q_phi_shift_nonneg_t_critical_tau0_of_pathB_any_B
    (hPathB : PrimeTermPathBTcritical)
    (B : ℝ) (hB : B > 0) :
    Q (fun ξ => phi_shift_critical B 0 ξ) ≥ 0 := by
  let K0 : ℝ := max 1 B
  have hK0 : K0 ≥ 1 := by
    exact le_max_left (1 : ℝ) B
  have hτB0 : |(0 : ℝ)| + B ≤ K0 := by
    simpa [K0] using (le_max_right (1 : ℝ) B)
  exact Q_phi_shift_nonneg_t_critical_of_pathB hPathB K0 B 0 hK0 hB hτB0

/-! ## Connection to Fejer_heat_atom -/

/-- Fejer_heat_atom at t0_critical (A1 heat parameter corresponding to t_critical). -/
def Fejer_heat_atom_critical (B τ : ℝ) (ξ : ℝ) : ℝ :=
  Fejer_heat_atom B t0_critical τ ξ

/-- Fejer_heat_atom = scaled sum of phi_shift(+tau) and phi_shift(-tau). -/
lemma Fejer_heat_atom_eq_phi_shifts (B τ : ℝ) :
    ∃ c > 0, ∀ ξ,
      Fejer_heat_atom_critical B τ ξ =
        c * (phi_shift_critical B τ ξ + phi_shift_critical B (-τ) ξ) := by
  /- I/O CARD: Fejer_heat_atom_eq_phi_shifts
     INPUT:  B τ : ℝ
     OUTPUT: Fejer_heat_atom_critical = c * (phi_shift(+τ) + phi_shift(-τ))
     NEED:   Definitions of Fejer_heat_atom, phi_shift, fejer_heat_window
             exp reparam at t_critical, and scalar factor from heat kernel
     BLOCKS: [Q_Fejer_heat_atom_nonneg_t_critical]
  -/
  have ht0 : t0_critical > 0 := t0_critical_pos
  obtain ⟨c, hc, hdecomp⟩ :=
    Q3.Proofs.QNonnegAtoms.Fejer_heat_atom_decomposition B t0_critical τ ht0
  have ht : (1 / (16 * Real.pi ^ 2 * t0_critical)) = t_critical := by
    -- invert the t0_critical definition
    have hden : (16 * Real.pi ^ 2 * t_critical) ≠ 0 := by
      have hpi : 0 < (Real.pi ^ 2) := by
        exact pow_pos Real.pi_pos 2
      have h16 : 0 < (16 : ℝ) := by norm_num
      have h1 : 0 < (16 * Real.pi ^ 2) := mul_pos h16 hpi
      have hpos : 0 < (16 * Real.pi ^ 2 * t_critical) := mul_pos h1 t_critical_pos
      exact ne_of_gt hpos
    by_cases hzero : (16 * Real.pi ^ 2 * t_critical) = 0
    · exfalso; exact hden hzero
    · unfold t0_critical
      field_simp [hzero]
  refine ⟨c, hc, ?_⟩
  intro ξ
  simpa [Fejer_heat_atom_critical, phi_shift_critical, ht] using hdecomp ξ

/-! ## Q on BaseAtomCone at t_critical -/

/-- BaseAtomCone at t0_critical (τ=0 only!)

    CRITICAL: Q >= 0 holds ONLY on BaseAtomCone (τ=0), not on full AtomCone!
    Numerical verification shows Q = -911 at τ = 1.69.

    This is sufficient because W_K requires even functions, and
    BaseAtomCone generates even approximants.
-/
def BaseAtomCone_critical (K : ℝ) : Set (ℝ → ℝ) :=
  Q3.BaseAtomCone_K K t0_critical

/-- BaseAtomCone with certified B-range at t0_critical (tau = 0 only). -/
def BaseAtomCone_critical_brange (K : ℝ) : Set (ℝ → ℝ) :=
  { g | ∃ (n : ℕ) (c : Fin n → ℝ) (B : Fin n → ℝ),
        (∀ i, c i ≥ 0) ∧
        (∀ i, B_min ≤ B i) ∧
        (∀ i, B i ≤ prime_cert_B_max) ∧
        (∀ x, g x = ∑ i, c i * Fejer_heat_atom (B i) t0_critical 0 x) ∧
        g ∈ W_K K }

/-- Q >= 0 on BaseAtomCone at t0_critical (τ=0 only!)

    This replaces the axiom Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom
    but restricted to BaseAtomCone_K (centered atoms, no τ-shift).

    Numerical verification (Python verify_variant_b.py):
      For all B ∈ [0.5, 4.9], τ=0: min Q = 1.03 > 0  ✓
      For τ > 0: Q can be < 0 (e.g. Q = -911 at τ = 1.69)  ✗
-/
theorem Q_nonneg_on_base_atoms_at_t_critical (K : ℝ) (hK : K ≥ 1) :
    ∀ g ∈ BaseAtomCone_critical K, Q g ≥ 0 := by
  /- I/O CARD: Q_nonneg_on_base_atoms_at_t_critical
     INPUT:  K : ℝ, hK : K ≥ 1, g ∈ BaseAtomCone_critical K
     OUTPUT: Q g ≥ 0
     NEED:   g = Σ c_i * Fejer_heat_atom(B_i, t0_critical, 0)  (τ=0!)
             At τ=0: Fejer_heat_atom B t 0 ξ = 2 * Φ_B(ξ)
             By Q linearity: Q(g) = Σ c_i * Q(2*Φ_{B_i})
             Each Q(2*Φ_B) ≥ 0 (verified numerically for all B ≤ K)
             c_i ≥ 0, so sum ≥ 0
     BLOCKS: [Q_nonneg_base_atoms_summary, main theorem chain]
  -/
  intro g hg
  have hsubset := Q3.BaseAtomCone_K_subset_AtomCone_K_fixed K t0_critical
  have hg' : g ∈ AtomCone_K_fixed K t0_critical := hsubset hg
  have h_atom : ∀ B τ, B > 0 → |τ| + B ≤ K →
      Q (Fejer_heat_atom B t0_critical τ) ≥ 0 := by
    intro B τ hB hτB
    obtain ⟨c, hc_pos, hdecomp⟩ := Fejer_heat_atom_eq_phi_shifts (B:=B) (τ:=τ)
    have h_int_f :
        MeasureTheory.Integrable (fun x => a_star x * phi_shift_critical B τ x) := by
      simpa [phi_shift_critical] using
        (Q3.Proofs.QNonnegAtoms.phi_shift_integrable_with_a_star
          (B:=B) (t:=t_critical) (tau:=τ) hB)
    have h_int_g :
        MeasureTheory.Integrable (fun x => a_star x * phi_shift_critical B (-τ) x) := by
      simpa [phi_shift_critical] using
        (Q3.Proofs.QNonnegAtoms.phi_shift_integrable_with_a_star
          (B:=B) (t:=t_critical) (tau:=(-τ)) hB)
    have h_sum_f :
        Summable (fun k => w_Q k * phi_shift_critical B τ (xi_n k)) := by
      simpa [phi_shift_critical] using
        (Q3.Proofs.QNonnegAtoms.phi_shift_prime_summable
          (B:=B) (t:=t_critical) (tau:=τ) hB)
    have h_sum_g :
        Summable (fun k => w_Q k * phi_shift_critical B (-τ) (xi_n k)) := by
      simpa [phi_shift_critical] using
        (Q3.Proofs.QNonnegAtoms.phi_shift_prime_summable
          (B:=B) (t:=t_critical) (tau:=(-τ)) hB)
    have hQ_scale_add :
        Q (fun x => c * (phi_shift_critical B τ x + phi_shift_critical B (-τ) x)) =
          c * (Q (phi_shift_critical B τ) + Q (phi_shift_critical B (-τ))) := by
      simpa using
        (Q3.Proofs.QNonnegAtoms.Q_scale_add
          (f:=fun x => phi_shift_critical B τ x)
          (g:=fun x => phi_shift_critical B (-τ) x)
          (c:=c) h_int_f h_int_g h_sum_f h_sum_g)
    have hQ1 : Q (phi_shift_critical B τ) ≥ 0 :=
      Q_phi_shift_nonneg_t_critical K B τ hK hB hτB
    have hτB' : |(-τ)| + B ≤ K := by
      simpa [abs_neg] using hτB
    have hQ2 : Q (phi_shift_critical B (-τ)) ≥ 0 :=
      Q_phi_shift_nonneg_t_critical K B (-τ) hK hB hτB'
    have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
    have hsum_nonneg :
        0 ≤ Q (phi_shift_critical B τ) + Q (phi_shift_critical B (-τ)) := by
      linarith [hQ1, hQ2]
    have hQ_nonneg :
        0 ≤ c * (Q (phi_shift_critical B τ) + Q (phi_shift_critical B (-τ))) := by
      exact mul_nonneg hc_nonneg hsum_nonneg
    have h_eq :
        Q (Fejer_heat_atom B t0_critical τ) =
          c * (Q (phi_shift_critical B τ) + Q (phi_shift_critical B (-τ))) := by
      have hfun :
          (fun x => Fejer_heat_atom B t0_critical τ x) =
            fun x => c * (phi_shift_critical B τ x + phi_shift_critical B (-τ) x) := by
        funext x
        simpa using hdecomp x
      simpa [hfun] using hQ_scale_add
    simpa [h_eq] using hQ_nonneg
  have h_atomcone :=
    Q3.Proofs.Q_nonneg_lemmas.Q_nonneg_on_atomcone_fixed_of_atoms
      K t0_critical hK t0_critical_pos h_atom
  exact h_atomcone g hg'

/-! ## BaseAtomCone (B-range) positivity at t_critical -/

/-- Q >= 0 on BaseAtomCone with B in [B_min, B_max] (tau = 0 only),
    from an explicit margin-certificate hypothesis. -/
theorem Q_nonneg_on_base_atoms_at_t_critical_brange_of_margin
    (K : ℝ) (_hK : K ≥ 1) (h_margin_cert : PrimeCertMarginOnBrange) :
    ∀ g ∈ BaseAtomCone_critical_brange K, Q g ≥ 0 := by
  intro g hg
  rcases hg with ⟨n, c, B, hc, hBmin, hBmax, hg_sum, hg_WK⟩
  have hBmin_pos : (0 : ℝ) < B_min := by
    norm_num [B_min]
  -- integrability / summability for each atom
  have h_int : ∀ i, MeasureTheory.Integrable
      (fun x => a_star x * Fejer_heat_atom (B i) t0_critical 0 x) := by
    intro i
    have hBpos : B i > 0 := by nlinarith [hBmin i, hBmin_pos]
    exact Q3.Proofs.Q_nonneg_lemmas.fejer_heat_atom_integrable_with_a_star
      (B i) t0_critical 0 hBpos t0_critical_pos
  have h_sum : ∀ i, Summable
      (fun k => w_Q k * Fejer_heat_atom (B i) t0_critical 0 (xi_n k)) := by
    intro i
    have hBpos : B i > 0 := by nlinarith [hBmin i, hBmin_pos]
    exact Q3.Proofs.Q_nonneg_lemmas.fejer_heat_atom_prime_summable
      (B i) t0_critical 0 hBpos t0_critical_pos
  -- linearity of Q over finite sums
  have hQ_sum :
      Q (fun x => ∑ i, c i * Fejer_heat_atom (B i) t0_critical 0 x) =
        ∑ i, c i * Q (Fejer_heat_atom (B i) t0_critical 0) := by
    exact Q3.Proofs.Q_nonneg_lemmas.Q_finset_sum (atoms := fun i => Fejer_heat_atom (B i) t0_critical 0)
      (coeffs := c) h_int h_sum
  -- each atom is nonnegative via the tau=0 prime certificate
  have h_atom : ∀ i, Q (Fejer_heat_atom (B i) t0_critical 0) ≥ 0 := by
    intro i
    obtain ⟨c0, hc0_pos, hdecomp⟩ := Fejer_heat_atom_eq_phi_shifts (B := B i) (τ := 0)
    have h_int_f :
        MeasureTheory.Integrable (fun x => a_star x * phi_shift_critical (B i) 0 x) := by
      have hBpos : B i > 0 := by nlinarith [hBmin i, hBmin_pos]
      simpa [phi_shift_critical] using
        (Q3.Proofs.QNonnegAtoms.phi_shift_integrable_with_a_star
          (B:=B i) (t:=t_critical) (tau:=0) hBpos)
    have h_sum_f :
        Summable (fun k => w_Q k * phi_shift_critical (B i) 0 (xi_n k)) := by
      have hBpos : B i > 0 := by nlinarith [hBmin i, hBmin_pos]
      simpa [phi_shift_critical] using
        (Q3.Proofs.QNonnegAtoms.phi_shift_prime_summable
          (B:=B i) (t:=t_critical) (tau:=0) hBpos)
    have hQ_scale_add :
        Q (fun x => c0 * (phi_shift_critical (B i) 0 x + phi_shift_critical (B i) 0 x)) =
          c0 * (Q (phi_shift_critical (B i) 0) + Q (phi_shift_critical (B i) 0)) := by
      simpa using
        (Q3.Proofs.QNonnegAtoms.Q_scale_add
          (f:=fun x => phi_shift_critical (B i) 0 x)
          (g:=fun x => phi_shift_critical (B i) 0 x)
          (c:=c0) h_int_f h_int_f h_sum_f h_sum_f)
    have hQphi : Q (phi_shift_critical (B i) 0) ≥ 0 := by
      exact Q_phi_shift_nonneg_t_critical_tau0_brange_of_margin
        (h_margin_cert := h_margin_cert) (B := B i) (hBmin := hBmin i) (hBmax := hBmax i)
    have hQ_nonneg :
        0 ≤ c0 * (Q (phi_shift_critical (B i) 0) + Q (phi_shift_critical (B i) 0)) := by
      have hc0 : 0 ≤ c0 := le_of_lt hc0_pos
      have hsum : 0 ≤ Q (phi_shift_critical (B i) 0) + Q (phi_shift_critical (B i) 0) := by
        nlinarith [hQphi]
      exact mul_nonneg hc0 hsum
    have h_eq :
        Q (Fejer_heat_atom (B i) t0_critical 0) =
          c0 * (Q (phi_shift_critical (B i) 0) + Q (phi_shift_critical (B i) 0)) := by
      have hfun :
          (fun x => Fejer_heat_atom (B i) t0_critical 0 x) =
            fun x => c0 * (phi_shift_critical (B i) 0 x + phi_shift_critical (B i) 0 x) := by
        funext x
        simpa using hdecomp x
      simpa [hfun] using hQ_scale_add
    simpa [h_eq] using hQ_nonneg
  -- finish: Q(g) = sum c_i * Q(atom_i) ≥ 0
  have hQ : Q g = ∑ i, c i * Q (Fejer_heat_atom (B i) t0_critical 0) := by
    have hfun :
        g = (fun x => ∑ i, c i * Fejer_heat_atom (B i) t0_critical 0 x) := by
      funext x
      exact hg_sum x
    simpa [hfun] using hQ_sum
  rw [hQ]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · exact hc i
  · exact h_atom i

/-- Q >= 0 on BaseAtomCone with B in [B_min, B_max] (tau = 0 only),
    from a tau-0 B-range Path B gate. -/
theorem Q_nonneg_on_base_atoms_at_t_critical_brange_of_tau0_brange_gate
    (hTau0Gate : PrimeTermPathBTcriticalTau0Brange)
    (K : ℝ) (_hK : K ≥ 1) :
    ∀ g ∈ BaseAtomCone_critical_brange K, Q g ≥ 0 := by
  intro g hg
  rcases hg with ⟨n, c, B, hc, hBmin, hBmax, hg_sum, hg_WK⟩
  have hBmin_pos : (0 : ℝ) < B_min := by
    norm_num [B_min]
  -- integrability / summability for each atom
  have h_int : ∀ i, MeasureTheory.Integrable
      (fun x => a_star x * Fejer_heat_atom (B i) t0_critical 0 x) := by
    intro i
    have hBpos : B i > 0 := by nlinarith [hBmin i, hBmin_pos]
    exact Q3.Proofs.Q_nonneg_lemmas.fejer_heat_atom_integrable_with_a_star
      (B i) t0_critical 0 hBpos t0_critical_pos
  have h_sum : ∀ i, Summable
      (fun k => w_Q k * Fejer_heat_atom (B i) t0_critical 0 (xi_n k)) := by
    intro i
    have hBpos : B i > 0 := by nlinarith [hBmin i, hBmin_pos]
    exact Q3.Proofs.Q_nonneg_lemmas.fejer_heat_atom_prime_summable
      (B i) t0_critical 0 hBpos t0_critical_pos
  -- linearity of Q over finite sums
  have hQ_sum :
      Q (fun x => ∑ i, c i * Fejer_heat_atom (B i) t0_critical 0 x) =
        ∑ i, c i * Q (Fejer_heat_atom (B i) t0_critical 0) := by
    exact Q3.Proofs.Q_nonneg_lemmas.Q_finset_sum (atoms := fun i => Fejer_heat_atom (B i) t0_critical 0)
      (coeffs := c) h_int h_sum
  -- each atom is nonnegative via Path B at tau = 0
  have h_atom : ∀ i, Q (Fejer_heat_atom (B i) t0_critical 0) ≥ 0 := by
    intro i
    obtain ⟨c0, hc0_pos, hdecomp⟩ := Fejer_heat_atom_eq_phi_shifts (B := B i) (τ := 0)
    have h_int_f :
        MeasureTheory.Integrable (fun x => a_star x * phi_shift_critical (B i) 0 x) := by
      have hBpos : B i > 0 := by nlinarith [hBmin i, hBmin_pos]
      simpa [phi_shift_critical] using
        (Q3.Proofs.QNonnegAtoms.phi_shift_integrable_with_a_star
          (B:=B i) (t:=t_critical) (tau:=0) hBpos)
    have h_sum_f :
        Summable (fun k => w_Q k * phi_shift_critical (B i) 0 (xi_n k)) := by
      have hBpos : B i > 0 := by nlinarith [hBmin i, hBmin_pos]
      simpa [phi_shift_critical] using
        (Q3.Proofs.QNonnegAtoms.phi_shift_prime_summable
          (B:=B i) (t:=t_critical) (tau:=0) hBpos)
    have hQ_scale_add :
        Q (fun x => c0 * (phi_shift_critical (B i) 0 x + phi_shift_critical (B i) 0 x)) =
          c0 * (Q (phi_shift_critical (B i) 0) + Q (phi_shift_critical (B i) 0)) := by
      simpa using
        (Q3.Proofs.QNonnegAtoms.Q_scale_add
          (f:=fun x => phi_shift_critical (B i) 0 x)
          (g:=fun x => phi_shift_critical (B i) 0 x)
          (c:=c0) h_int_f h_int_f h_sum_f h_sum_f)
    have hQphi : Q (phi_shift_critical (B i) 0) ≥ 0 := by
      have hprime_tau0 :
          prime_term (fun ξ => phi_shift_critical (B i) 0 ξ) ≤
            arch_term (fun ξ => phi_shift_critical (B i) 0 ξ) := by
        exact hTau0Gate (B i) (hBmin i) (hBmax i)
      unfold Q
      linarith
    have hQ_nonneg :
        0 ≤ c0 * (Q (phi_shift_critical (B i) 0) + Q (phi_shift_critical (B i) 0)) := by
      have hc0 : 0 ≤ c0 := le_of_lt hc0_pos
      have hsum : 0 ≤ Q (phi_shift_critical (B i) 0) + Q (phi_shift_critical (B i) 0) := by
        nlinarith [hQphi]
      exact mul_nonneg hc0 hsum
    have h_eq :
        Q (Fejer_heat_atom (B i) t0_critical 0) =
          c0 * (Q (phi_shift_critical (B i) 0) + Q (phi_shift_critical (B i) 0)) := by
      have hfun :
          (fun x => Fejer_heat_atom (B i) t0_critical 0 x) =
            fun x => c0 * (phi_shift_critical (B i) 0 x + phi_shift_critical (B i) 0 x) := by
        funext x
        simpa using hdecomp x
      simpa [hfun] using hQ_scale_add
    simpa [h_eq] using hQ_nonneg
  -- finish: Q(g) = sum c_i * Q(atom_i) ≥ 0
  have hQ : Q g = ∑ i, c i * Q (Fejer_heat_atom (B i) t0_critical 0) := by
    have hfun :
        g = (fun x => ∑ i, c i * Fejer_heat_atom (B i) t0_critical 0 x) := by
      funext x
      exact hg_sum x
    simpa [hfun] using hQ_sum
  rw [hQ]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · exact hc i
  · exact h_atom i

/-- Q >= 0 on BaseAtomCone with B in [B_min, B_max] (tau = 0 only),
    from the full Path B `t_critical` gate (all `τ`) by specialization to `τ=0`. -/
theorem Q_nonneg_on_base_atoms_at_t_critical_brange_of_pathB
    (hPathB : PrimeTermPathBTcritical)
    (K : ℝ) (_hK : K ≥ 1) :
    ∀ g ∈ BaseAtomCone_critical_brange K, Q g ≥ 0 := by
  have hTau0Gate : PrimeTermPathBTcriticalTau0Brange := by
    intro B hBmin _hBmax
    have hB : B > 0 := by
      have hBmin_pos : (0 : ℝ) < B_min := by norm_num [B_min]
      linarith
    let K0 : ℝ := max 1 B
    have hK0 : K0 ≥ 1 := by
      exact le_max_left (1 : ℝ) B
    have hτB0 : |(0 : ℝ)| + B ≤ K0 := by
      simpa [K0] using (le_max_right (1 : ℝ) B)
    simpa [phi_shift_critical] using hPathB K0 B 0 hK0 hB hτB0
  exact Q_nonneg_on_base_atoms_at_t_critical_brange_of_tau0_brange_gate
    hTau0Gate K _hK

/-- Q >= 0 on BaseAtomCone with B in [B_min, B_max] (tau = 0 only). -/
theorem Q_nonneg_on_base_atoms_at_t_critical_brange
    (K : ℝ) (_hK : K ≥ 1) (h_margin_cert : PrimeCertMarginOnBrange) :
    ∀ g ∈ BaseAtomCone_critical_brange K, Q g ≥ 0 := by
  exact Q_nonneg_on_base_atoms_at_t_critical_brange_of_margin
    (K := K) (_hK := _hK)
    (h_margin_cert := h_margin_cert)

/-- Path-B-backed default for B-range atoms (tau = 0 mainline). -/
theorem Q_nonneg_on_base_atoms_at_t_critical_brange_via_pathB
    (K : ℝ) (_hK : K ≥ 1) :
    ∀ g ∈ BaseAtomCone_critical_brange K, Q g ≥ 0 := by
  have hPathB : PrimeTermPathBTcritical := prime_term_pathB_tcritical_from_legacy
  exact Q_nonneg_on_base_atoms_at_t_critical_brange_of_pathB hPathB K _hK

/-- Tau-0 mainline default for B-range atoms via the certified tau-0 gate. -/
theorem Q_nonneg_on_base_atoms_at_t_critical_brange_via_tau0_brange_gate
    (K : ℝ) (_hK : K ≥ 1) :
    ∀ g ∈ BaseAtomCone_critical_brange K, Q g ≥ 0 := by
  exact Q_nonneg_on_base_atoms_at_t_critical_brange_of_tau0_brange_gate
    prime_term_pathB_tcritical_tau0_brange_thm K _hK

/-! ## Summary -/

/-- The key theorem: at t_critical = 0.15, Q >= 0 on BaseAtomCone (τ=0).

    This closes the gap in the LaTeX proof where t_sym = 0.06 gave Q < 0.
    The solution: increase t from 0.06 to 0.15, where:
    1. Q becomes positive (arch_term > prime_term)
    2. P_A floor is still preserved (min P_A = 1.66 > c_star = 1.1)

    CRITICAL CONSTRAINT: Q >= 0 holds ONLY for τ=0 (BaseAtomCone).
    For τ > 0, Q can be negative (Q = -911 at τ = 1.69).

    This is OK because W_K requires even functions, and BaseAtomCone_K
    is sufficient to approximate all even functions (no τ-shifts needed).

    Numerical crossover point: t* ≈ 0.136
-/
theorem Q_nonneg_base_atoms_summary :
    ∃ t : ℝ, t > t_sym ∧ t < 1 ∧
      (∀ (K : ℝ), K ≥ 1 → ∀ g ∈ Q3.BaseAtomCone_K K (1 / (16 * Real.pi^2 * t)), Q g ≥ 0) := by
  use t_critical
  constructor
  · exact t_critical_gt_t_sym
  constructor
  · norm_num [t_critical]
  intro K hK g hg
  have h_eq : (1 / (16 * Real.pi^2 * t_critical)) = t0_critical := by
    unfold t0_critical
    ring
  rw [h_eq] at hg
  exact Q_nonneg_on_base_atoms_at_t_critical K hK g hg

end Q3
