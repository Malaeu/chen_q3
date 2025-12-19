# Indicator Functions in Sobolev Spaces

## Goal
Prove that indicator functions of intervals belong to H^s(𝕋) if and only if s < 1/2.

This is the **critical lemma** that distinguishes Sobolev spaces from Heat Kernel RKHS and enables circle method decompositions.

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

/-- Sobolev weight (1 + |n|²)^s -/
noncomputable def sobolevWeight (s : ℝ) (n : ℤ) : ℝ :=
  (1 + (n : ℝ)^2) ^ s

/-- Has finite Sobolev norm -/
def HasFiniteSobolevNorm (s : ℝ) (f : ℝ → ℂ) : Prop :=
  Summable (fun n : ℤ ↦ Complex.normSq (fourierCoeff f n) * sobolevWeight s n)

/-- Indicator function of interval [a,b] -/
noncomputable def indicatorInterval (a b : ℝ) : ℝ → ℂ := fun α ↦
  if a ≤ α ∧ α ≤ b then 1 else 0
```

## Main Theorem to Prove

```lean
/-- Indicator Sobolev Criterion: 𝟙_{[a,b]} ∈ H^s(𝕋) ⟺ s < 1/2

This is the critical threshold that enables circle method decompositions.
Heat Kernel RKHS requires exponential decay and cannot contain indicators.
Sobolev H^s for s < 1/2 has polynomial decay and DOES contain indicators.
-/
theorem indicator_in_sobolev {a b : ℝ} (hab : a < b) (hb : b ≤ 1) (ha : 0 ≤ a) (s : ℝ) :
    HasFiniteSobolevNorm s (indicatorInterval a b) ↔ s < 1/2 := by
  sorry
```

## Proof Sketch

### Part 1: Compute Fourier coefficients of 𝟙_{[a,b]}

For $n \neq 0$:
$$\widehat{\mathbf{1}_{[a,b]}}(n) = \int_a^b e^{-2\pi i n \alpha} \, d\alpha = \frac{e^{-2\pi i n a} - e^{-2\pi i n b}}{2\pi i n}$$

Using $|e^{i\theta_1} - e^{i\theta_2}| \leq 2$:
$$|\widehat{\mathbf{1}_{[a,b]}}(n)| \leq \frac{2}{2\pi |n|} = \frac{1}{\pi |n|}$$

For large $|n|$, we have $|\widehat{\mathbf{1}}(n)| \sim C/|n|$ (polynomial decay, not exponential!).

### Part 2: Sobolev norm convergence

The Sobolev norm squared is:
$$\|\mathbf{1}_{[a,b]}\|_{H^s}^2 = \sum_{n \in \mathbb{Z}} |\widehat{\mathbf{1}}(n)|^2 (1 + n^2)^s$$

For large $|n|$, this behaves like:
$$\sum_{n \neq 0} \frac{C}{n^2} \cdot (1 + n^2)^s \sim \sum_{n=1}^{\infty} n^{2s - 2}$$

### Part 3: Convergence criterion

The series $\sum_{n=1}^{\infty} n^{2s-2}$ converges if and only if:
$$2s - 2 < -1 \iff s < \frac{1}{2}$$

### Part 4: Conclusion

- If $s < 1/2$: The series converges, so $\mathbf{1}_{[a,b]} \in H^s(\mathbb{T})$ ✓
- If $s \geq 1/2$: The series diverges, so $\mathbf{1}_{[a,b]} \notin H^s(\mathbb{T})$ ✗

## Notes

- The key is that indicator functions have **polynomial Fourier decay** $|\hat{f}(n)| \sim 1/|n|$
- Heat Kernel RKHS requires **exponential decay**, so indicators are excluded
- This is why Sobolev-Q3 works for circle method: we can decompose 𝕋 = 𝔐 ∪ 𝔪 with 𝟙_𝔐 ∈ H^s
- Use `Real.summable_nat_rpow_inv` for convergence of $\sum n^{-p}$
- The integral formula for Fourier coefficients of step functions is standard
- May need `Complex.abs_exp_ofReal_mul_I` for phase bounds
