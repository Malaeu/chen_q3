# Rayleigh-Q identification (rely v1)

## Goal
Prove the Lean statement below using only Mathlib + the definitions given here.
Avoid `exact?` and heavy `aesop`.

## Definitions (Lean)
```lean
import Mathlib

open scoped BigOperators

noncomputable section

def xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

def Nodes (K : ℝ) : Set ℕ := {n | |xi_n n| ≤ K ∧ n ≥ 2}

def fejer_heat_window (B t ξ : ℝ) : ℝ :=
  max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi^2 * t * ξ^2)

/-- Fourier index for i in Fin (2*M+1): maps 0..2M to -M..M. -/
def fourier_index (M : ℕ) (i : Fin (2 * M + 1)) : ℤ :=
  (i.val : ℤ) - (M : ℤ)

/-- Normalized evaluation vector. -/
def prime_vec (M : ℕ) (ξ : ℝ) : Fin (2 * M + 1) → ℂ :=
  fun i =>
    ((1 / Real.sqrt (2 * M + 1 : ℝ)) : ℂ) *
      Complex.exp
        (-2 * Real.pi * Complex.I * ((fourier_index M i : ℤ) : ℂ) * (ξ : ℂ))

/-- Compression prime operator. -/
def T_P_comp (w_Q : ℕ → ℝ) (K B t : ℝ) (M : ℕ) [Fintype (Nodes K)] :
    Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℂ :=
  fun i j =>
    ∑ n : Nodes K,
      ((w_Q n * fejer_heat_window B t (xi_n n)) : ℂ) *
        prime_vec M (xi_n n) i * conj (prime_vec M (xi_n n) j)

/-- Real part of compression prime operator. -/
def T_P_comp_real (w_Q : ℕ → ℝ) (K B t : ℝ) (M : ℕ) [Fintype (Nodes K)] :
    Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ :=
  fun i j => (T_P_comp w_Q K B t M i j).re

/-- Fourier Toeplitz entry. -/
def ToeplitzEntry (P : ℝ → ℝ) (i j : ℕ) : ℂ :=
  ∫ θ in (-1/2 : ℝ)..(1/2 : ℝ),
    (P θ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((i : ℂ) - (j : ℂ)) * (θ : ℂ))

/-- Fourier Toeplitz matrix (real part). -/
def ToeplitzMatrix_Fourier_real (M : ℕ) (P : ℝ → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => (ToeplitzEntry P i j).re

/-- Rayleigh quotient. -/
def RayleighQuotient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, v i * A i j * v j) / (∑ i, v i ^ 2)

/-- Basis vector for constant polynomial. -/
def basis0 (M : ℕ) : Fin (2 * M + 1) → ℝ :=
  let i0 : Fin (2 * M + 1) := ⟨M, by nlinarith⟩
  fun i => if i = i0 then (1 : ℝ) else 0

/-- Archimedean term. -/
def arch_term (a : ℝ → ℝ) (Phi : ℝ → ℝ) : ℝ :=
  ∫ ξ, (2 * Real.pi * a ξ) * Phi ξ

/-- Prime term. -/
def prime_term (w_Q : ℕ → ℝ) (Phi : ℝ → ℝ) : ℝ :=
  ∑' n, w_Q n * Phi (xi_n n)

/-- Q functional. -/
def Q (a : ℝ → ℝ) (w_Q : ℕ → ℝ) (Phi : ℝ → ℝ) : ℝ :=
  arch_term a Phi - prime_term w_Q Phi

/-- A3 symbol pieces. -/
def g (a : ℝ → ℝ) (B t ξ : ℝ) : ℝ := a ξ * fejer_heat_window B t ξ

def P_A (a : ℝ → ℝ) (B t θ : ℝ) : ℝ :=
  2 * Real.pi * ∑' (m : ℤ), g a B t (θ + m)
```

## Theorem (Lean)
```lean
theorem rayleigh_Q_identification
    (a : ℝ → ℝ) (w_Q : ℕ → ℝ) (B t : ℝ) (M : ℕ) [Fintype (Nodes B)] :
  (2 * M + 1 : ℝ) *
    RayleighQuotient
      (ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A a B t)
        - T_P_comp_real w_Q B B t M)
      (basis0 M)
  = Q a w_Q (fun ξ => fejer_heat_window B t ξ) := by
  -- proof
  sorry
```

## Strategy (high-level)
1. Reduce the Rayleigh quotient at `basis0` to diagonal entries.
2. Toeplitz diagonal gives the integral of `P_A` on [-1/2, 1/2].
3. Prime operator diagonal gives the (1/(2M+1)) factor times the weighted sum.
4. Use periodization to rewrite the `P_A` integral as the arch term.
5. Use support of `fejer_heat_window` to reduce the prime term to `Nodes B`.

## Policy
- Use `suffices` for goal reduction.
- Avoid `exact?`.
- Avoid heavy `aesop`.
