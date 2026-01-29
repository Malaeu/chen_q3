# Cauchy-Schwarz Trap: Spectral Norm of All-Ones Matrix

## Mathematical Context

We need to prove the fundamental scaling barrier for the $(2M+1)$ factor in Rayleigh quotient calculations.

### Setup

Let $N = 2M + 1$ be the dimension. Define:

1. **All-ones matrix**: $J_{ij} = 1$ for all $i, j \in \{0, \ldots, N-1\}$
2. **Constant vector**: $\mathbf{1} = (1, 1, \ldots, 1)^T \in \mathbb{R}^N$
3. **Rayleigh quotient**: $R_A(v) = \frac{v^T A v}{v^T v}$

### Main Theorem to Prove

**Theorem (Spectral Norm of J)**:
For the $N \times N$ all-ones matrix $J$, we have:
$$\|J\|_{\text{op}} = N$$

**Proof outline**:
1. $J = \mathbf{1} \mathbf{1}^T$ (rank-1 outer product)
2. For any rank-1 matrix $uv^T$: $\|uv^T\|_{\text{op}} = \|u\| \cdot \|v\|$
3. $\|\mathbf{1}\| = \sqrt{N}$
4. Therefore $\|J\| = \sqrt{N} \cdot \sqrt{N} = N$

### Corollary (Rayleigh Quotient Saturation)

For $\Phi = \mathbf{1}$:
$$R_J(\mathbf{1}) = \frac{\mathbf{1}^T J \mathbf{1}}{\mathbf{1}^T \mathbf{1}} = \frac{N^2}{N} = N$$

This shows the spectral norm is **attained** on the constant vector.

### Key Consequence

If we have a matrix term of the form:
$$\text{prime\_term} \approx w^T J w = |\langle w, \mathbf{1} \rangle|^2$$

To normalize this to $O(1)$, we MUST divide by $N = 2M+1$.

## Lean 4 Statement

```lean
import Mathlib

open Matrix Finset BigOperators

variable {n : ℕ} [NeZero n]

/-- All-ones matrix: J_{ij} = 1 -/
def allOnesMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun _ _ => (1 : ℝ)

/-- Constant vector: 1 = (1, 1, ..., 1) -/
def constVec (n : ℕ) : Fin n → ℝ := fun _ => (1 : ℝ)

/-- J = 1 * 1^T (outer product) -/
lemma allOnesMatrix_eq_outer (n : ℕ) [NeZero n] :
    allOnesMatrix n = (fun i => (1 : ℝ)) ⬝ (fun j => (1 : ℝ))ᵀ := by
  sorry

/-- The spectral norm of J is n -/
theorem allOnesMatrix_opNorm (n : ℕ) [NeZero n] :
    ‖allOnesMatrix n‖ = (n : ℝ) := by
  sorry

/-- Rayleigh quotient of J at constant vector equals n -/
theorem rayleigh_allOnes_constVec (n : ℕ) [NeZero n] :
    let J := allOnesMatrix n
    let v := constVec n
    (∑ i, ∑ j, v i * J i j * v j) / (∑ i, v i ^ 2) = (n : ℝ) := by
  sorry

/-- The 1/(2M+1) divisor is necessary for normalization -/
theorem divisor_necessary (M : ℕ) :
    let N := 2 * M + 1
    let J := allOnesMatrix N
    ∀ v : Fin N → ℝ, v ≠ 0 →
      (∑ i, ∑ j, v i * J i j * v j) / (∑ i, v i ^ 2) ≤ (N : ℝ) := by
  sorry
```

## References

- Gray, R.M. (2006). "Toeplitz and Circulant Matrices: A Review"
- Standard linear algebra: spectral norm of rank-1 matrix
