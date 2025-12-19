# Sobolev Duality Bound

## Goal
Prove the H^s × H^{-s} duality inequality, which is the key tool for controlling Minor Arc integrals in the circle method.

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

/-- Sobolev norm squared -/
noncomputable def sobolevNormSq (s : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∑' n : ℤ, Complex.normSq (fourierCoeff f n) * sobolevWeight s n

/-- Sobolev norm -/
noncomputable def sobolevNorm (s : ℝ) (f : ℝ → ℂ) : ℝ :=
  Real.sqrt (sobolevNormSq s f)

/-- Has finite Sobolev norm -/
def HasFiniteSobolevNorm (s : ℝ) (f : ℝ → ℂ) : Prop :=
  Summable (fun n : ℤ ↦ Complex.normSq (fourierCoeff f n) * sobolevWeight s n)

/-- Dual pairing in Fourier space -/
noncomputable def sobolevDualPairing (f g : ℝ → ℂ) : ℂ :=
  ∑' n : ℤ, fourierCoeff f n * conj (fourierCoeff g n)
```

## Main Theorem to Prove

```lean
/-- Sobolev Duality Bound: |⟨f, g⟩| ≤ ‖f‖_{H^s} · ‖g‖_{H^{-s}}

This is the key estimate for controlling Minor Arc integrals.
When Ψ ∈ H^s and |S|² ∈ H^{-s}, we get:
  |∫ Ψ · |S|²| ≤ ‖Ψ‖_{H^s} · ‖|S|²‖_{H^{-s}}

This replaces the need for Riemann Hypothesis in classical circle method!
-/
theorem sobolev_duality_bound (s : ℝ) (f g : ℝ → ℂ)
    (hf : HasFiniteSobolevNorm s f) (hg : HasFiniteSobolevNorm (-s) g) :
    Complex.abs (sobolevDualPairing f g) ≤ sobolevNorm s f * sobolevNorm (-s) g := by
  sorry
```

## Proof Sketch

### Step 1: Rewrite dual pairing with weights

$$\langle f, g \rangle = \sum_{n \in \mathbb{Z}} \hat{f}(n) \overline{\hat{g}(n)}$$

Insert identity using $(1 + n^2)^{s/2} \cdot (1 + n^2)^{-s/2} = 1$:

$$= \sum_n \left[\hat{f}(n) (1+n^2)^{s/2}\right] \cdot \left[\overline{\hat{g}(n)} (1+n^2)^{-s/2}\right]$$

### Step 2: Apply Cauchy-Schwarz in ℓ²

By Cauchy-Schwarz inequality:

$$|\langle f, g \rangle| \leq \left(\sum_n |\hat{f}(n)|^2 (1+n^2)^s\right)^{1/2} \cdot \left(\sum_n |\hat{g}(n)|^2 (1+n^2)^{-s}\right)^{1/2}$$

### Step 3: Identify Sobolev norms

The left factor is $\|f\|_{H^s}$ and the right factor is $\|g\|_{H^{-s}}$.

Therefore:
$$|\langle f, g \rangle| \leq \|f\|_{H^s} \cdot \|g\|_{H^{-s}}$$

### Step 4: Application to Circle Method

For Minor Arc control:
- $\Psi$ = test function (twisted symbol), $\Psi \in H^s$
- $|S|^2$ = prime exponential sum squared, aim to show $|S|^2 \in H^{-s}$

Then:
$$\left|\int_{\mathfrak{m}} \Psi \cdot |S|^2\right| \leq \|\Psi\|_{H^s} \cdot \||S|^2\|_{H^{-s}}$$

This is the "Sobolev Cap" that controls Minor Arc noise WITHOUT assuming RH!

## Notes

- This is essentially Cauchy-Schwarz in weighted ℓ² space
- Use `inner_mul_le_norm_mul_norm` from Mathlib
- The key is that H^s and H^{-s} are dual with respect to the L² pairing
- Parseval: $\int f \bar{g} = \sum_n \hat{f}(n) \overline{\hat{g}(n)}$
- The negative Sobolev norm $\|g\|_{H^{-s}}$ measures "roughness" - larger for oscillatory functions
- `tsum_mul_le_sqrt_mul_sqrt` may be useful
- `Complex.abs_sum_le_sum_abs` for triangle inequality
