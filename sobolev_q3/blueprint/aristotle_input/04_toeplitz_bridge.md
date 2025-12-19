# Toeplitz-Integral Bridge Identity

## Goal
Prove that the Toeplitz quadratic form equals the integral of Ψ·|S|². This is the A3_s Bridge that connects operator theory to circle method.

## Definitions

```lean
import Mathlib

open scoped BigOperators
open MeasureTheory Set Filter Topology

noncomputable section

/-- Character e(nα) = exp(2πinα) -/
noncomputable def circleChar (n : ℤ) (α : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * n * α)

/-- Fourier coefficient at frequency n -/
noncomputable def fourierCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  ∫ α in Set.Icc 0 1, f α * conj (circleChar n α)

/-- Toeplitz matrix entry: T_Ψ(n,m) = Ψ̂(n-m) -/
noncomputable def toeplitzEntry (Ψ : ℝ → ℂ) (n m : ℤ) : ℂ :=
  fourierCoeff Ψ (n - m)

/-- Exponential sum S_b(α) = Σ_n b(n)·e(nα) -/
noncomputable def expSum (b : ℤ → ℂ) (support : Finset ℤ) (α : ℝ) : ℂ :=
  ∑ n ∈ support, b n * circleChar n α

/-- Squared modulus |S_b(α)|² -/
noncomputable def expSumSq (b : ℤ → ℂ) (support : Finset ℤ) (α : ℝ) : ℝ :=
  Complex.normSq (expSum b support α)

/-- Toeplitz quadratic form: ⟨T_Ψ b, b⟩ = Σ_{n,m} b(n)·b(m)*·Ψ̂(n-m) -/
noncomputable def toeplitzForm (Ψ : ℝ → ℂ) (b : ℤ → ℂ) (support : Finset ℤ) : ℂ :=
  ∑ n ∈ support, ∑ m ∈ support, b n * conj (b m) * toeplitzEntry Ψ n m
```

## Main Theorem to Prove

```lean
/-- THE TOEPLITZ-INTEGRAL BRIDGE IDENTITY

The Toeplitz quadratic form equals the integral of Ψ times |S|².
This connects the matrix world to the integral world.

  ⟨T_Ψ b, b⟩ = ∫_𝕋 Ψ(α) · |S_b(α)|² dα

This is fundamental for the circle method:
- Left side: Operator-theoretic (spectral analysis)
- Right side: Integral (Fourier analysis)
-/
theorem toeplitz_integral_identity (Ψ : ℝ → ℂ) (b : ℤ → ℂ) (support : Finset ℤ) :
    toeplitzForm Ψ b support = ∫ α in Set.Icc 0 1, Ψ α * (expSumSq b support α : ℂ) := by
  sorry
```

## Proof Sketch

### Step 1: Expand |S_b(α)|²

$$|S_b(\alpha)|^2 = S_b(\alpha) \cdot \overline{S_b(\alpha)} = \left(\sum_n b(n) e(n\alpha)\right) \cdot \overline{\left(\sum_m b(m) e(m\alpha)\right)}$$

$$= \sum_{n,m} b(n) \overline{b(m)} \cdot e(n\alpha) \cdot \overline{e(m\alpha)} = \sum_{n,m} b(n) \overline{b(m)} \cdot e((n-m)\alpha)$$

### Step 2: Integrate with Ψ

$$\int_0^1 \Psi(\alpha) |S_b(\alpha)|^2 \, d\alpha = \int_0^1 \Psi(\alpha) \sum_{n,m} b(n) \overline{b(m)} e((n-m)\alpha) \, d\alpha$$

### Step 3: Interchange sum and integral (Fubini)

Since the sum is finite (over support × support):

$$= \sum_{n,m} b(n) \overline{b(m)} \int_0^1 \Psi(\alpha) e((n-m)\alpha) \, d\alpha$$

### Step 4: Recognize Fourier coefficients

The integral is exactly the Fourier coefficient of Ψ at frequency (n-m):

$$\int_0^1 \Psi(\alpha) e((n-m)\alpha) \, d\alpha = \int_0^1 \Psi(\alpha) \overline{e(-(n-m)\alpha)} \, d\alpha = \hat{\Psi}(n-m)$$

### Step 5: Conclude

$$= \sum_{n,m} b(n) \overline{b(m)} \hat{\Psi}(n-m) = \sum_{n,m} b(n) \overline{b(m)} \cdot T_\Psi(n,m) = \langle T_\Psi b, b \rangle$$

This is exactly the definition of `toeplitzForm`.

## Notes

- This is a finite sum version; no convergence issues
- The key is Fubini's theorem for finite sums
- Use `Finset.sum_comm` for swapping sums
- Use `MeasureTheory.integral_finset_sum` for interchange
- The Fourier coefficient integral is exactly `fourierCoeff` definition
- `Complex.normSq_eq_conj_mul_self` for expanding |z|²
- This bridges operator theory (Szegő, Toeplitz) with harmonic analysis (circle method)
