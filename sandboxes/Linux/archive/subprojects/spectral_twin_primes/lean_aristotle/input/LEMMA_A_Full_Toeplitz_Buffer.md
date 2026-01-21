# Lemma A: Toeplitz Buffer Suppression (Full Version)

## Context

This is the FULL formulation of Lemma A for the Q3 → MAS → TPC chain.
The goal is to bound cross-terms in a Toeplitz bilinear form when indices are separated.

## Setup

**Toeplitz Matrix:** A matrix $T_M$ of size $M \times M$ with entries $T_{jk} = A_{j-k}$ where $A_\ell$ are Fourier coefficients of some symbol.

**Tail Norm:** For threshold $\Delta$:
$$\|A\|_{\text{tail},\Delta} = \sum_{|\ell| \geq \Delta} |A_\ell|$$

**Index Sets:**
- $I_{\text{maj}} \subseteq \{0, 1, \ldots, M-1\}$ — "major" indices
- $I_{\text{min}} \subseteq \{0, 1, \ldots, M-1\}$ — "minor" indices
- **Separation condition:** $|j - k| \geq \Delta$ for all $j \in I_{\text{maj}}$, $k \in I_{\text{min}}$

**Vectors:**
- $p_{\text{maj}} \in \mathbb{C}^M$ supported on $I_{\text{maj}}$
- $p_{\text{min}} \in \mathbb{C}^M$ supported on $I_{\text{min}}$

## Theorem Statement

**Lemma A (Toeplitz Buffer Suppression):**

If $p_{\text{maj}}$ is supported on $I_{\text{maj}}$ and $p_{\text{min}}$ is supported on $I_{\text{min}}$, and all pairs $(j,k) \in I_{\text{maj}} \times I_{\text{min}}$ satisfy $|j - k| \geq \Delta$, then:

$$\left|\sum_{j,k} A_{j-k} \cdot p_{\text{maj}}(j) \cdot \overline{p_{\text{min}}(k)}\right| \leq \|A\|_{\text{tail},\Delta} \cdot \|p_{\text{maj}}\|_2 \cdot \|p_{\text{min}}\|_2$$

## Proof Sketch

**Step 1:** By support conditions, the sum only runs over $(j,k) \in I_{\text{maj}} \times I_{\text{min}}$.

**Step 2:** By separation, $|j - k| \geq \Delta$ for all terms in the sum.

**Step 3:** Therefore $A_{j-k}$ only involves coefficients with $|\ell| \geq \Delta$.

**Step 4:** Apply Cauchy-Schwarz:
$$\left|\sum_{j,k} A_{j-k} \cdot p_{\text{maj}}(j) \cdot \overline{p_{\text{min}}(k)}\right| \leq \sum_{|\ell| \geq \Delta} |A_\ell| \cdot \left|\sum_j p_{\text{maj}}(j) \cdot \overline{p_{\text{min}}(j-\ell)}\right|$$

**Step 5:** Each inner sum is bounded by $\|p_{\text{maj}}\|_2 \cdot \|p_{\text{min}}\|_2$ (Cauchy-Schwarz again).

**Step 6:** Sum over $\ell$ gives $\|A\|_{\text{tail},\Delta}$.

## Expected Lean Formalization

```lean
import Mathlib

open scoped BigOperators
open Complex Finset

noncomputable section

variable {M : ℕ}

/-- Toeplitz matrix coefficients -/
structure ToeplitzCoeffs where
  coeff : ℤ → ℂ

/-- Tail norm of Fourier coefficients -/
noncomputable def tail_norm (A : ToeplitzCoeffs) (Δ : ℕ) : ℝ :=
  ∑' ℓ : ℤ, if Δ ≤ |ℓ| then ‖A.coeff ℓ‖ else 0

/-- Bilinear form from Toeplitz matrix -/
noncomputable def toeplitz_bilinear (A : ToeplitzCoeffs) (p q : Fin M → ℂ) : ℂ :=
  ∑ j : Fin M, ∑ k : Fin M, A.coeff (j - k) * p j * conj (q k)

/-- Support of a vector -/
def support (p : Fin M → ℂ) : Finset (Fin M) :=
  Finset.filter (fun i => p i ≠ 0) Finset.univ

/-- Separation condition -/
def separated (I_maj I_min : Finset (Fin M)) (Δ : ℕ) : Prop :=
  ∀ j ∈ I_maj, ∀ k ∈ I_min, Δ ≤ |((j : ℤ) - k)|

/-- LEMMA A: Toeplitz Buffer Suppression -/
theorem toeplitz_buffer_suppression
    (A : ToeplitzCoeffs) (Δ : ℕ)
    (p_maj p_min : Fin M → ℂ)
    (I_maj I_min : Finset (Fin M))
    (h_supp_maj : support p_maj ⊆ I_maj)
    (h_supp_min : support p_min ⊆ I_min)
    (h_sep : separated I_maj I_min Δ)
    (h_summable : Summable (fun ℓ : ℤ => ‖A.coeff ℓ‖)) :
    ‖toeplitz_bilinear A p_maj p_min‖ ≤
      tail_norm A Δ * ‖p_maj‖ * ‖p_min‖ := by
  sorry

/-- Corollary: If Fourier coefficients decay as 1/k², tail is finite -/
theorem tail_finite_of_decay
    (A : ToeplitzCoeffs) (C : ℝ) (hC : C > 0)
    (h_decay : ∀ k : ℤ, k ≠ 0 → ‖A.coeff k‖ ≤ C / (k : ℝ)^2) :
    Summable (fun ℓ : ℤ => ‖A.coeff ℓ‖) := by
  sorry
```

## Dependencies

- Cauchy-Schwarz inequality for sums
- Properties of support and indicator functions
- Summability of 1/k² (p-series)

## Note

This theorem is needed for the Q3 → MAS chain to bound cross-terms between major and minor arc contributions. The separation Δ comes from the buffer width in Fourier space.
