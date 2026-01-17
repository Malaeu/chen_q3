# Toeplitz Diagonal = Integral

## Goal

Prove that the Toeplitz matrix diagonal at i0 equals the integral of P_A.

```lean
lemma ToeplitzFourier_P_A_diag (M : ℕ) (B t : ℝ) :
    RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t) (i0 M) (i0 M) =
      ∫ θ in (-1/2 : ℝ)..(1/2), P_A B t θ
```

## Key Definitions

```lean
-- ToeplitzMatrix_Fourier_real is the real part of Toeplitz matrix with Fourier entries
-- At i, j: A[i,j] = (∫_{-1/2}^{1/2} f(θ) · e^{-2πi(i-j)θ} dθ).re

-- ToeplitzEntry
def ToeplitzEntry (f : ℝ → ℝ) (k : ℤ) : ℂ :=
  ∫ θ in (-1/2 : ℝ)..(1/2), (f θ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * k * θ)

-- ToeplitzMatrix_Fourier_real: real part
def ToeplitzMatrix_Fourier_real (n : ℕ) (f : ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (ToeplitzEntry f (↑i.val - ↑j.val)).re

-- i0 M : Fin (2*M+1) with i0 M = M
def i0 (M : ℕ) : Fin (2 * M + 1) := ⟨M, M_lt_2M_add_1 M⟩
```

## Proof Idea

At i = j = i0, the Fourier exponent k = i0.val - i0.val = M - M = 0.
So exp(-2πi · 0 · θ) = exp(0) = 1.

The diagonal entry becomes:
```
A[i0, i0] = (∫_{-1/2}^{1/2} (P_A θ : ℂ) * 1 dθ).re
          = (∫_{-1/2}^{1/2} (P_A θ : ℂ) dθ).re
          = ∫_{-1/2}^{1/2} P_A θ dθ
```

The last step uses that P_A is real-valued.

## Key Calculation

```lean
-- Step 1: At i0, the index difference is 0
have h_diff : (i0 M).val - (i0 M).val = 0 := sub_self _

-- Step 2: exp(0) = 1
have h_exp : ∀ θ, Complex.exp (-2 * Real.pi * Complex.I * 0 * θ) = 1 := by simp

-- Step 3: The integral simplifies
-- ∫_{-1/2}^{1/2} (P_A θ : ℂ) * 1 dθ = ∫_{-1/2}^{1/2} (P_A θ : ℂ) dθ

-- Step 4: (∫ (f : ℂ)).re = ∫ (f.re) when integrand is real-valued
-- This is: Complex.re_integral or similar
```

## The Crux: Step 4

The key step is: `(∫ θ, (P_A θ : ℂ)).re = ∫ θ, P_A θ`

For intervalIntegral of complex-valued functions:
```lean
-- Mathlib has: intervalIntegral.integral_ofReal for real→complex integral
-- Or use: Complex.re_integral when applicable
```

Since `P_A θ : ℝ` and we're integrating `(P_A θ : ℂ)`, we need to show:
```lean
(∫ θ in (-1/2 : ℝ)..(1/2), (P_A B t θ : ℂ)).re = ∫ θ in (-1/2 : ℝ)..(1/2), P_A B t θ
```

## Mathlib Lemmas to Use

```lean
-- For real-cast integrals:
intervalIntegral.integral_ofReal :
  ∫ x in a..b, (f x : ℂ) = ↑(∫ x in a..b, f x)

-- Then apply Complex.ofReal_re to get:
Complex.ofReal_re : (↑r : ℂ).re = r

-- For the exponential simplification:
Complex.exp_zero : exp 0 = 1

-- For 0 * anything:
zero_mul, mul_zero
```

## Suggested Proof Structure

```lean
lemma ToeplitzFourier_P_A_diag (M : ℕ) (B t : ℝ) :
    RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t) (i0 M) (i0 M) =
      ∫ θ in (-1/2 : ℝ)..(1/2), P_A B t θ := by
  simp only [RayleighFourier.ToeplitzMatrix_Fourier_real, RayleighFourier.ToeplitzEntry]
  -- At i0, i0.val - i0.val = 0
  simp only [i0, sub_self]
  -- exp(-2πi · 0 · θ) = 1
  simp only [Int.cast_zero, mul_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one]
  -- Now need: (∫ θ, (P_A θ : ℂ)).re = ∫ θ, P_A θ
  -- Use intervalIntegral.integral_ofReal + Complex.ofReal_re
  rw [← intervalIntegral.integral_ofReal]
  exact Complex.ofReal_re _
```

## Integrability

If Aristotle asks about integrability:
- P_A is continuous (proven in project as `continuous_P_A`)
- Continuous functions on compact intervals are integrable
- Use `Continuous.intervalIntegrable`

## Tactic Preferences

AVOID: `exact?`, heavy `aesop`
PREFER: `simp` with explicit lemmas, `rfl`, `norm_cast`
