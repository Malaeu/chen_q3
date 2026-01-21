# Rayleigh Lower Bound (Sandbox Version)

## Goal
Prove the theorems in the attached sandbox file `rayleigh_lower_bound_v2_sandbox.lean`.

## What to Prove

The sandbox contains:
1. `cos_integral_orthogonality` - orthogonality of cosines
2. `parseval_trig_poly` - Parseval identity for trig polynomials
3. `toeplitz_quadratic_form` - key identity linking matrix form to integral
4. `rayleigh_lower_bound` - **MAIN THEOREM**

## Proof Strategy for Main Theorem

1. Use `toeplitz_quadratic_form` to rewrite numerator:
   ∑∑ v_i * T_{ij} * v_j = ∫ P(θ) |p(θ)|² dθ

2. Apply pointwise bound P(θ) ≥ m:
   ∫ P(θ) |p(θ)|² dθ ≥ ∫ m |p(θ)|² dθ = m · ∫ |p(θ)|² dθ

3. Use `parseval_trig_poly`:
   ∫ |p(θ)|² dθ = ∑ v_k²

4. Conclude:
   Rayleigh quotient = (∫ P |p|²) / (∑ v²) ≥ m

## Mathlib Lemmas to Use

- `MeasureTheory.integral_mono` - monotonicity of integrals
- `MeasureTheory.integral_mul_left` - pull constant out of integral
- `Real.cos_add`, `Real.cos_sub` - trigonometric identities
- `Finset.sum_mul`, `Finset.mul_sum` - sum manipulation
- `div_le_iff` - for working with ratios

## Notes

The sandbox file has all definitions. Aristotle should create `_proof` versions of the sorry theorems.
