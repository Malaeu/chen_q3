# Rayleigh-Q identification (lay v1)

## Goal
Prove the Lean statement below. Use Mathlib only. Avoid `exact?` and heavy `aesop`.
Structure the proof via the helper lemmas (also listed below).

## Definitions (Lean)
```lean
import Mathlib

open scoped BigOperators

noncomputable section

def xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

def Nodes (K : ℝ) : Set ℕ := {n | |xi_n n| ≤ K ∧ n ≥ 2}

def fejer_heat_window (B t ξ : ℝ) : ℝ :=
  max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi^2 * t * ξ^2)

def fourier_index (M : ℕ) (i : Fin (2 * M + 1)) : ℤ :=
  (i.val : ℤ) - (M : ℤ)

def prime_vec (M : ℕ) (ξ : ℝ) : Fin (2 * M + 1) → ℂ :=
  fun i =>
    ((1 / Real.sqrt (2 * M + 1 : ℝ)) : ℂ) *
      Complex.exp
        (-2 * Real.pi * Complex.I * ((fourier_index M i : ℤ) : ℂ) * (ξ : ℂ))

def T_P_comp (w_Q : ℕ → ℝ) (K B t : ℝ) (M : ℕ) [Fintype (Nodes K)] :
    Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℂ :=
  fun i j =>
    ∑ n : Nodes K,
      ((w_Q n * fejer_heat_window B t (xi_n n)) : ℂ) *
        prime_vec M (xi_n n) i * conj (prime_vec M (xi_n n) j)

def T_P_comp_real (w_Q : ℕ → ℝ) (K B t : ℝ) (M : ℕ) [Fintype (Nodes K)] :
    Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ :=
  fun i j => (T_P_comp w_Q K B t M i j).re

def ToeplitzEntry (P : ℝ → ℝ) (i j : ℕ) : ℂ :=
  ∫ θ in (-1/2 : ℝ)..(1/2 : ℝ),
    (P θ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((i : ℂ) - (j : ℂ)) * (θ : ℂ))

def ToeplitzMatrix_Fourier_real (M : ℕ) (P : ℝ → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => (ToeplitzEntry P i j).re

def quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * A i j * v j

def RayleighQuotient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  quadForm A v / (∑ i, v i ^ 2)

def basis0 (M : ℕ) : Fin (2 * M + 1) → ℝ :=
  let i0 : Fin (2 * M + 1) := ⟨M, by nlinarith⟩
  fun i => if i = i0 then (1 : ℝ) else 0

def arch_term (a : ℝ → ℝ) (Phi : ℝ → ℝ) : ℝ :=
  ∫ ξ, (2 * Real.pi * a ξ) * Phi ξ

def prime_term (w_Q : ℕ → ℝ) (Phi : ℝ → ℝ) : ℝ :=
  ∑' n, w_Q n * Phi (xi_n n)

def Q (a : ℝ → ℝ) (w_Q : ℕ → ℝ) (Phi : ℝ → ℝ) : ℝ :=
  arch_term a Phi - prime_term w_Q Phi

def g (a : ℝ → ℝ) (B t ξ : ℝ) : ℝ := a ξ * fejer_heat_window B t ξ

def P_A (a : ℝ → ℝ) (B t θ : ℝ) : ℝ :=
  2 * Real.pi * ∑' (m : ℤ), g a B t (θ + m)
```

## Helper Lemmas to Prove (Lean)
```lean
lemma basis0_norm_sq (M : ℕ) :
    (∑ i : Fin (2 * M + 1), (basis0 M i) ^ 2) = 1 := by
  sorry

lemma quadForm_basis0 (M : ℕ) (A : Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ) :
    quadForm A (basis0 M) =
      (let i0 : Fin (2 * M + 1) := ⟨M, by nlinarith⟩; A i0 i0) := by
  sorry

lemma toeplitz_diag_eq_integral (a : ℝ → ℝ) (B t : ℝ) (M : ℕ) :
    (let i0 : Fin (2 * M + 1) := ⟨M, by nlinarith⟩;
      ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A a B t) i0 i0)
    = ∫ θ in (-1/2 : ℝ)..(1/2 : ℝ), P_A a B t θ := by
  -- diagonal of ToeplitzEntry when i=j
  sorry

lemma tpcomp_diag_eq_sum (w_Q : ℕ → ℝ) (B t : ℝ) (M : ℕ) [Fintype (Nodes B)] :
    (let i0 : Fin (2 * M + 1) := ⟨M, by nlinarith⟩;
      T_P_comp_real w_Q B B t M i0 i0)
    = (1 / (2 * M + 1 : ℝ)) *
        ∑ n : Nodes B, w_Q n * fejer_heat_window B t (xi_n n) := by
  -- use prime_vec norm
  sorry

lemma periodized_integral_eq_arch (a : ℝ → ℝ) (B t : ℝ) :
    ∫ θ in (-1/2 : ℝ)..(1/2 : ℝ), P_A a B t θ
      = arch_term a (fun ξ => fejer_heat_window B t ξ) := by
  -- periodization integral
  sorry

lemma prime_term_eq_nodes (w_Q : ℕ → ℝ) (B t : ℝ) :
    prime_term w_Q (fun ξ => fejer_heat_window B t ξ)
      = ∑ n : Nodes B, w_Q n * fejer_heat_window B t (xi_n n) := by
  -- support of fejer_heat_window
  sorry
```

## Main Theorem (Lean)
```lean
theorem rayleigh_Q_identification
    (a : ℝ → ℝ) (w_Q : ℕ → ℝ) (B t : ℝ) (M : ℕ) [Fintype (Nodes B)] :
  (2 * M + 1 : ℝ) *
    RayleighQuotient
      (ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A a B t)
        - T_P_comp_real w_Q B B t M)
      (basis0 M)
  = Q a w_Q (fun ξ => fejer_heat_window B t ξ) := by
  -- use helper lemmas above
  sorry
```

## Policy
- Use `suffices` for goal reduction.
- Avoid `exact?`.
- Minimize `aesop`.
