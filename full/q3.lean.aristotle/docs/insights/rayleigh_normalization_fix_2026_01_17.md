# Rayleigh-Q Normalization Fix

**Date:** 2026-01-17
**Status:** RESOLVED
**Impact:** Critical formula correction (tex + Lean)

---

## Problem Identified

The original Rayleigh identification formula was **WRONG**:

```
(2M+1) * RQ(T_M[P_A] - T_P^{(M)}, basis0) = Q(Φ)
```

**Issue:** Multiplying by `(2M+1)` affects BOTH parts:
- Arch part: `(2M+1) * ∫ P_A` — WRONG! Should not be scaled
- Prime part: `(2M+1) * (1/(2M+1)) * prime_term = prime_term` — correct

Result: `(2M+1) * arch_term - prime_term ≠ Q(Φ)`

---

## Root Cause

The normalized vectors `v_n^{(M)}` have:
```
v_n^{(M)}(θ) = (1/√(2M+1)) Σ_{|k|≤M} e^{2πik(θ-ξ_n)}
```

So `||v_n^{(M)}|| = 1`, but:
```
⟨1, v_n^{(M)}⟩ = 1/√(2M+1)
|⟨1, v_n^{(M)}⟩|² = 1/(2M+1)
```

While `|1(ξ_n)|² = 1`.

This means:
```
⟨T_P^{(M)} 1, 1⟩ = Σ w(n)Φ(ξ_n) · |⟨1, v_n⟩|² = prime_term / (2M+1)
```

---

## Correct Formulas

### Option 1: Scale prime part only
```
⟨T_M[P_A] 1, 1⟩ - (2M+1)⟨T_P^{(M)} 1, 1⟩ = Q(Φ)
```

### Option 2: Use unnormalized vectors (Lean implementation)
```
v_n^{unnorm}(θ) = Σ_{|k|≤M} e^{2πik(θ-ξ_n)}   (no 1/√(2M+1))
T_P^{unnorm} uses unnormalized vectors
RQ(T_M[P_A] - T_P^{unnorm}, basis0) = Q(Φ)   (no (2M+1) needed!)
```

---

## Files Changed

### Lean (sandbox/measure_dom)
- `Q3/Basic/Defs.lean` — added `prime_vec_unnorm`, `T_P_comp_unnorm`, `T_P_comp_unnorm_real`
- `Q3/Proofs/Rayleigh_Q_correct.lean` — correct identification theorem

### LaTeX
- `full/sections/A3/rayleigh_bridge.tex`:
  - Lemma 2 proof: added `|p(ξ_n)|² = (2M+1)|⟨p,v_n⟩|²`
  - Theorem 4: corrected formula with explicit (2M+1) on prime part
  - Added explanation and alternative unnormalized form

- `full/sections/A3/calibration.tex`:
  - Added note that infinite-dim case differs from finite-dim compression
  - Reference to Theorem where normalization matters

---

## Verification

The correction does NOT change the mathematical chain:
- Weil criterion: Q(Φ) ≥ 0 ⟺ RH
- arch_term = ∫ P_A = ∫ a*·Φ (unchanged)
- prime_term = Σ w(n)·Φ(ξ_n) (unchanged)
- Q(Φ) = arch_term - prime_term (unchanged)

Only the **operator representation** is corrected to match the functional.

---

## Key Identities

For `p ≡ 1` (constant polynomial):
```
⟨T_M[P_A] 1, 1⟩ = ∫_{-1/2}^{1/2} P_A(θ) dθ = arch_term

⟨T_P^{(M)} 1, 1⟩ = Σ w(n)Φ(ξ_n) · |⟨1, v_n^{(M)}⟩|²
                 = Σ w(n)Φ(ξ_n) / (2M+1)
                 = prime_term / (2M+1)

(2M+1) · ⟨T_P^{(M)} 1, 1⟩ = prime_term
```

With unnormalized vectors:
```
⟨T_P^{unnorm} 1, 1⟩ = Σ w(n)Φ(ξ_n) · |⟨1, v_n^{unnorm}⟩|² / ||v_n^{unnorm}||²
                    = Σ w(n)Φ(ξ_n) · (2M+1) / (2M+1)
                    = prime_term
```

---

## Lessons Learned

1. **Always check normalization constants** when converting between functional and operator forms
2. **The `1/√(2M+1)` factor** in Fourier basis vectors propagates to inner products as `1/(2M+1)`
3. **Unnormalized versions** are cleaner for quadratic forms where the normalization cancels anyway
