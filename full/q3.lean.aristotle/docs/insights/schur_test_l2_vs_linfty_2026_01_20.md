# Schur Test: L2 vs L∞ Norm Mismatch

**Date:** 2026-01-20
**Status:** INVESTIGATED — axiom remains

## Summary

Attempted to close `Schur_test` axiom using Mathlib. Failed due to norm mismatch.

## Problem

**Project uses L2 (spectral) norm:**
```lean
open scoped Matrix.Norms.L2Operator
```

**Mathlib has L∞ (row-sum) norm:**
```lean
Matrix.linfty_opNorm_def : ‖A‖ = sup_i (∑_j ‖A i j‖)
```

These are **different norms**:
- L∞ norm = max row sum (trivial bound)
- L2 norm = max |eigenvalue| (spectral norm, requires Gershgorin)

## What Was Done

1. Created `Q3/Proofs/Schur_Test.lean` with L∞ version proof
2. Proof compiles and is correct for L∞ norm
3. Cannot wire to axiom because project uses L2 norm

## L∞ Proof (for reference)

```lean
theorem Schur_test_proof {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (_hA : A.IsSymm)
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ i, ∑ j, |A i j| ≤ C) :
    ‖A‖ ≤ C := by
  rw [Matrix.linfty_opNorm_def]
  -- ... direct from definition
```

## What Would Be Needed for L2

To prove Schur test for L2/spectral norm:

1. **Gershgorin theorem** (exists in Mathlib as `eigenvalue_mem_ball`):
   - Every eigenvalue lies in a disk centered at diagonal entry
   - Disk radius = off-diagonal row sum

2. **Spectral norm = max |eigenvalue|** for symmetric matrices
   - Need: `‖A‖ = sup {|μ| : μ is eigenvalue of A}`

3. **Combine:** If row sums ≤ C and diagonal = 0, then all eigenvalues in [-C, C]

This requires significant work connecting:
- `Mathlib.LinearAlgebra.Matrix.Gershgorin`
- `Mathlib.Analysis.Matrix` (L2 norm)
- Symmetric matrix eigenvalue theory

## Files

- `Q3/Proofs/Schur_Test.lean` — L∞ version (created, not wired)
- `Q3/Axioms.lean:164` — axiom definition (unchanged)

## Conclusion

`Schur_test` remains as Tier-1 classical axiom. The L∞ proof is available
but cannot replace the L2 axiom without additional Gershgorin-based proof.

**Effort estimate:** ~2-4 hours to properly prove L2 version with Gershgorin.
