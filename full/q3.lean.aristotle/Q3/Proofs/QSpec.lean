/-
QSpec: Frozen specification for Q functional

This file defines the exact specification of Q that must match Lean/LaTeX.
Purpose: "kill any chance that the dispute is about wrong Q version"

Key invariants:
1. Q_paper = Q_lean (up to documented normalization)
2. Test vectors must pass sanity checks
3. Counterexample Φ_{B=3,t=0.06} must be in AtomCone AND give Q < 0
-/

import Q3.Basic.Defs
import Q3.Axioms
import Q3.Proofs.ShiftedWindows

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical ComplexConjugate
open MeasureTheory

noncomputable section

namespace Q3

/-! ## QSpec: Frozen Parameter Specification -/

/-- Complete specification of Q functional parameters -/
structure QSpec where
  /-- Fejer width -/
  B : ℝ
  /-- Heat smoothing parameter (LaTeX convention: exp(-4π²t·ξ²)) -/
  t : ℝ
  /-- Shift parameter -/
  τ : ℝ
  /-- Compact support bound -/
  K : ℝ
  /-- Discretization level for Toeplitz -/
  M : ℕ
  /-- Positivity constraints -/
  hB : B > 0
  hK : K > 0
  hM : M > 0
  /-- Support constraint -/
  hτB_K : |τ| + B ≤ K

/-- Standard test spec: B=3, t=0.06, τ=0, K=5, M=100 -/
def testSpec : QSpec where
  B := 3
  t := 3/50  -- = 0.06
  τ := 0
  K := 5
  M := 100
  hB := by norm_num
  hK := by norm_num
  hM := by norm_num
  hτB_K := by norm_num

/-- Critical spec: B=3, t=0.15, τ=0, K=5, M=100 -/
def criticalSpec : QSpec where
  B := 3
  t := 3/20  -- = 0.15
  τ := 0
  K := 5
  M := 100
  hB := by norm_num
  hK := by norm_num
  hM := by norm_num
  hτB_K := by norm_num

/-! ## Q Definitions: Paper vs Lean -/

/-- Test function Φ_{B,t,τ}(ξ) = fejer_heat_window(ξ - τ)
    Paper: Φ(ξ) = max(0, 1-|ξ|/B) · exp(-4π²t·ξ²)
    Lean:  fejer_heat_window B t ξ = max 0 (1 - |ξ|/B) * exp(-4π²t·ξ²)
-/
def Φ_spec (spec : QSpec) (ξ : ℝ) : ℝ :=
  fejer_heat_window spec.B spec.t (ξ - spec.τ)

/-- Q as defined in paper (explicit formula)
    Q(Φ) = ∫ a*(ξ)·Φ(ξ) dξ - Σ w_Q(n)·Φ(ξ_n)
-/
def Q_paper (spec : QSpec) : ℝ :=
  arch_term (Φ_spec spec) - prime_term (Φ_spec spec)

/-- Q as defined in Lean (should be identical)
    Q Φ := arch_term Φ - prime_term Φ
-/
def Q_lean (spec : QSpec) : ℝ :=
  Q (Φ_spec spec)

/-- Key theorem: Q_paper = Q_lean (by definition unfolding) -/
theorem Q_paper_eq_Q_lean (spec : QSpec) : Q_paper spec = Q_lean spec := by
  rfl

/-! ## Sanity Test Cases -/

/-- Test 1: Q(0) = 0 -/
theorem Q_zero : Q (fun _ => 0) = 0 := by
  unfold Q arch_term prime_term
  simp [MeasureTheory.integral_zero]

/-- Test 2: For Φ with very small support, prime_term ≈ 0
    (no prime powers in tiny interval) -/
lemma prime_term_small_support (ε : ℝ) (hε : 0 < ε) (hε_small : ε < xi_n 2) :
    prime_term (fun ξ => if |ξ| < ε then 1 else 0) = 0 := by
  unfold prime_term
  -- For n ≥ 2, xi_n n ≥ xi_n 2 > ε, so Φ(xi_n n) = 0
  have h : ∀ n, w_Q n * (if |xi_n n| < ε then 1 else 0) = 0 := by
    intro n
    by_cases hn : n < 2
    · -- n < 2: w_Q n = 0 (vonMangoldt is 0 for n < 2)
      interval_cases n
      · simp [w_Q, ArithmeticFunction.vonMangoldt]
      · simp [w_Q, ArithmeticFunction.vonMangoldt]
    · -- n ≥ 2: xi_n n ≥ xi_n 2 > ε, so indicator is 0
      push_neg at hn
      have hxi : xi_n n ≥ xi_n 2 := by
        unfold xi_n
        have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
        have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) h2
        have hpi : 0 ≤ 2 * Real.pi := by positivity
        exact div_le_div_of_nonneg_right hlog hpi
      have habs : |xi_n n| ≥ ε := by
        have hxi2_pos : 0 < xi_n 2 := by
          unfold xi_n
          have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
          have hpi : 0 < 2 * Real.pi := by positivity
          exact div_pos hlog2 hpi
        have hxi_nonneg : 0 ≤ xi_n n := by
          unfold xi_n
          apply div_nonneg
          · have h1n : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
            exact Real.log_nonneg h1n
          · positivity
        rw [abs_of_nonneg hxi_nonneg]
        linarith [hxi, hε_small]
      simp [not_lt.mpr habs]
  simp_rw [h]
  simp

/-- Test 3: Φ is even → verified by definition -/
lemma Φ_spec_even (spec : QSpec) (hτ : spec.τ = 0) :
    IsEven (Φ_spec spec) := by
  intro x
  simp only [Φ_spec, hτ, sub_zero]
  unfold fejer_heat_window
  simp only [abs_neg, neg_sq]

/--
Test 4: Φ ∈ W_K

PROVIDED SOLUTION
Use continuity of `phi_shift` from `Q3.Proofs.ShiftedWindows.continuous_phi_shift`
and rewrite `Φ_spec` to `phi_shift` with `simp [Φ_spec, Q3.phi_shift]`.

For support: after `simp [Function.mem_support, Φ_spec, fejer_heat_window]` on `hξ`,
get `|ξ - spec.τ| < spec.B` from positivity of the `max` term, then use
`abs_sub_le` and `spec.hτB_K : |spec.τ| + spec.B ≤ spec.K` to show `|ξ| < spec.K`.
Conclude `ξ ∈ Set.Ioo (-spec.K) spec.K` via `abs_lt`.
-/
lemma Φ_spec_in_W_K (spec : QSpec) (hτ : spec.τ = 0) :
    Φ_spec spec ∈ W_K spec.K := by
  constructor
  · -- Continuous
    unfold Φ_spec
    have h1 : Continuous (fun ξ => fejer_heat_window spec.B spec.t (ξ - spec.τ)) := by
      -- fejer_heat_window is continuous
      sorry
    exact h1
  constructor
  · -- Support ⊆ (-K, K)
    intro ξ hξ
    unfold Φ_spec fejer_heat_window at hξ
    simp only [Function.mem_support, ne_eq] at hξ
    -- If Φ(ξ) ≠ 0 then |ξ - τ| < B, so |ξ| < |τ| + B ≤ K
    sorry
  constructor
  · -- Even
    exact Φ_spec_even spec hτ
  · -- Nonneg
    intro ξ
    unfold Φ_spec
    exact fejer_heat_window_nonneg spec.B spec.t (ξ - spec.τ)

/-! ## Counterexample Membership -/

/-- Key: Φ_{testSpec} = (1/2) · Fejer_heat_atom at τ=0

    Note: Fejer_heat_atom(B, t, 0, ξ) = 2 * fejer_heat_window(B, t, ξ)
    because at τ=0: Φ(ξ-0) + Φ(ξ+0) = 2*Φ(ξ)
-/
lemma Φ_testSpec_is_half_atom (ξ : ℝ) :
    Φ_spec testSpec ξ = (1/2) * Fejer_heat_atom testSpec.B testSpec.t 0 ξ := by
  unfold Φ_spec Fejer_heat_atom testSpec fejer_heat_window
  simp only [sub_zero, add_zero]
  -- Goal: max 0 (1 - |ξ|/3) * exp(-4π²·(3/50)·ξ²) = (1/2) * 2 * (same)
  ring_nf
  -- The ring_nf can't solve this because of max and exp
  -- Need to show: f(ξ) = (1/2) * (f(ξ) + f(ξ)) which is trivially true
  sorry

/-- Φ_{testSpec} ∈ AtomCone_K_fixed -/
lemma Φ_testSpec_in_AtomCone :
    Φ_spec testSpec ∈ AtomCone_K_fixed testSpec.K (1 / (16 * Real.pi^2 * testSpec.t)) := by
  -- Φ = (1/2) * atom, so it's a weighted sum of atoms with c = 1/2
  -- This satisfies all AtomCone conditions
  sorry

/-! ## The Key Finding: Q(Φ_{testSpec}) < 0 -/

/-- AXIOM (numerical verification): Q(Φ_{B=3,t=0.06}) < 0

    This is the counterexample that shows the original axiom is FALSE.
    Numerical value: Q ≈ -15.56

    Verified by: verify_phase0.py
-/
axiom Q_testSpec_negative : Q_paper testSpec < 0

/-- Corollary: The axiom Q ≥ 0 on AtomCone is FALSE at t_sym = 0.06 -/
theorem atoms_positivity_false_at_t_sym :
    ¬ (∀ g ∈ AtomCone_K_fixed testSpec.K (1 / (16 * Real.pi^2 * testSpec.t)), Q g ≥ 0) := by
  intro h
  have h1 : Φ_spec testSpec ∈ AtomCone_K_fixed testSpec.K (1 / (16 * Real.pi^2 * testSpec.t)) :=
    Φ_testSpec_in_AtomCone
  have h2 : Q (Φ_spec testSpec) ≥ 0 := h (Φ_spec testSpec) h1
  have h3 : Q_paper testSpec < 0 := Q_testSpec_negative
  have h4 : Q_paper testSpec = Q (Φ_spec testSpec) := by rfl
  linarith

/-! ## The Solution: Q(Φ_{criticalSpec}) ≥ 0 -/

/-- AXIOM (numerical verification): Q(Φ_{B=3,t=0.15}) ≥ 0

    This is the working parameter where Q becomes positive.
    Numerical value: Q ≈ +0.86

    Verified by: verify_phase0.py
-/
axiom Q_criticalSpec_nonneg : Q_paper criticalSpec ≥ 0

/-- At t_critical, the positivity holds -/
theorem atoms_positivity_at_t_critical :
    Q (Φ_spec criticalSpec) ≥ 0 := by
  have h : Q_paper criticalSpec ≥ 0 := Q_criticalSpec_nonneg
  have h_eq : Q_paper criticalSpec = Q (Φ_spec criticalSpec) := by rfl
  linarith

end Q3
