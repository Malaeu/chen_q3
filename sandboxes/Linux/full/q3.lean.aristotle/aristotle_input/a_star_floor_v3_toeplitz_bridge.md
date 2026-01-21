# Toeplitz Matrix: Sampling vs Fourier Coefficients

## Goal
Bridge between two Toeplitz matrix definitions:

### Definition 1: Sampling (Q3 uses this)
```lean
def ToeplitzMatrix (M : ℕ) (P : ℝ → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => P ((i.val - j.val : ℤ) * Real.pi / M)
```
Entry T[i,j] = P(π(i-j)/M) — direct sampling of symbol.

### Definition 2: Fourier coefficients (classical Toeplitz theory)
```lean
def ToeplitzEntry (P : ℝ → ℝ) (i j : ℕ) : ℂ :=
  ∫ θ in (-1/2)..(1/2), P θ * Complex.exp (2*π*I*(i-j)*θ)
```
Entry T[i,j] = ĉ_{i-j} — Fourier coefficient of symbol.

## The question
For the Rayleigh quotient lower bound:

**Fourier version (rayleigh_v1.lean PROVEN):**
```lean
theorem rayleigh_lower_bound (M : ℕ) (P : ℝ → ℝ) (m : ℝ)
    (hP_ge : ∀ θ ∈ Set.Icc (-1/2) (1/2), m ≤ P θ) (v : Fin M → ℝ) (hv : v ≠ 0) :
    RayleighQuotient_Fourier (ToeplitzEntry P) v ≥ m
```

**Sampling version (NEEDED):**
```lean
theorem rayleigh_lower_bound_sampling (M : ℕ) (P : ℝ → ℝ) (m : ℝ)
    (hP_ge : ∀ θ, m ≤ P θ) (v : Fin M → ℝ) (hv : v ≠ 0) :
    RayleighQuotient (ToeplitzMatrix M P) v ≥ m
```

## What to prove
Either:
1. The two definitions give the same Rayleigh quotient (asymptotically or exactly)
2. A direct proof of Rayleigh lower bound for sampling definition
3. Show when/how to transfer bounds between definitions

## Mathematical background
For trigonometric polynomial p(θ) = Σ vₖ e^{2πikθ}:
- Fourier: ⟨T·v, v⟩ = ∫ P(θ)|p(θ)|² dθ ≥ min(P)·‖v‖²
- Sampling: ⟨T·v, v⟩ = Σᵢⱼ vᵢvⱼ P(π(i-j)/M) — Riemann sum approximation?

As M → ∞, sampling → integral, so bounds should match.
But we need this for ALL M, not just large M.
