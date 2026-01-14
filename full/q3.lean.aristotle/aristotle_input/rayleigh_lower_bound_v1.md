# Rayleigh Lower Bound for Toeplitz Matrices (Pure Informal)

## Goal
Prove that for a Toeplitz matrix with non-negative symbol, the minimum Rayleigh quotient is bounded below by the infimum of the symbol.

## Mathematical Statement

**Theorem (Rayleigh Lower Bound):**
Let P : ℝ → ℝ be a continuous function on [-1/2, 1/2].
Let T_M[P] be the M×M Toeplitz matrix with entries:
  T_M[P]_{i,j} = ∫_{-1/2}^{1/2} P(θ) · exp(2πi(i-j)θ) dθ

If P(θ) ≥ m for all θ ∈ [-1/2, 1/2], then for any non-zero vector v ∈ ℝ^M:
  (v^T · T_M[P] · v) / ‖v‖² ≥ m

## Proof Sketch

1. **Toeplitz Quadratic Form Identity:**
   For trigonometric polynomial p(θ) = Σ_{k=0}^{M-1} v_k · exp(2πikθ), we have:

   v^T · T_M[P] · v = ∫_{-1/2}^{1/2} P(θ) · |p(θ)|² dθ

   This is a standard result in Toeplitz theory (Grenander-Szegő).

2. **Pointwise Lower Bound:**
   Since P(θ) ≥ m for all θ:

   ∫_{-1/2}^{1/2} P(θ) · |p(θ)|² dθ ≥ ∫_{-1/2}^{1/2} m · |p(θ)|² dθ = m · ∫_{-1/2}^{1/2} |p(θ)|² dθ

3. **Parseval Identity:**
   For trigonometric polynomial p with coefficients v_0, ..., v_{M-1}:

   ∫_{-1/2}^{1/2} |p(θ)|² dθ = Σ_{k=0}^{M-1} |v_k|² = ‖v‖²

4. **Conclusion:**
   v^T · T_M[P] · v ≥ m · ‖v‖²

   Dividing by ‖v‖² (valid since v ≠ 0):
   (v^T · T_M[P] · v) / ‖v‖² ≥ m

## Key Lemmas Needed

1. `toeplitz_quadratic_form`: The quadratic form equals the integral of P times |p|².
2. `parseval_trig_poly`: L² norm of trig polynomial equals ℓ² norm of coefficients.
3. `integral_mono`: If f ≤ g pointwise, then ∫f ≤ ∫g.

## Mathlib Hints

- `MeasureTheory.integral_mono` for integral monotonicity
- `inner_self_eq_norm_sq` for ⟨v, v⟩ = ‖v‖²
- `Finset.sum_nonneg` for non-negativity of sums
- Fourier theory in `Mathlib.Analysis.Fourier`

## Expected Lean Statement

```lean
theorem rayleigh_lower_bound
    (M : ℕ) (hM : M > 0)
    (P : ℝ → ℝ) (hP_cont : Continuous P)
    (m : ℝ) (hP_ge : ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2), m ≤ P θ)
    (v : Fin M → ℝ) (hv : v ≠ 0) :
    (∑ i, ∑ j, v i * ToeplitzEntry P i j * v j) / (∑ i, v i ^ 2) ≥ m
```

where `ToeplitzEntry P i j = ∫ θ in Icc (-1/2) (1/2), P θ * exp(2πi(i-j)θ)`.
