# Insight: Rayleigh-Q Identification Framework

**Date:** 2026-01-17
**Category:** Spectral Theory / Matrix Analysis
**Status:** Proven (with 1 sorry for periodization identity)

## Core Result

The Q functional can be expressed via Rayleigh quotients of matrices:

```
Q(Φ) = RQ(Toeplitz[P_A], basis0) - (2M+1)·RQ(T_P_comp, basis0)
```

## Warning: Correct Formula

**WRONG** (naive version):
```
(2M+1)·RQ(Toeplitz - T_P_comp, basis0)  ← multiplies BOTH parts by (2M+1)
```

**CORRECT**:
```
RQ(Toeplitz, basis0) - (2M+1)·RQ(T_P_comp, basis0)
```

The factor (2M+1) only applies to T_P_comp due to prime_vec normalization:
`|prime_vec(i0)|² = 1/(2M+1)`

## Key Theorems

| Theorem | Statement | Status |
|---------|-----------|--------|
| `prime_vec_i0_norm_sq` | `|prime_vec(i0)|² = 1/(2M+1)` | ✅ Proven |
| `T_P_comp_real_diag` | `T_P_comp[i0,i0] = (1/(2M+1))·Σ w_Q·Φ(ξ_n)` | ✅ Proven |
| `arch_rayleigh_eq` | `RQ(Toeplitz[P_A], basis0) = arch_term(Φ)` | ✅ Proven |
| `prime_rayleigh_eq` | `(2M+1)·RQ(T_P_comp, basis0) = Σ w_Q·Φ(ξ_n)` | ✅ Proven |
| `integral_P_A_eq_arch_term` | `∫ P_A dθ = arch_term(Φ)` | ⚠️ 1 sorry |
| `rayleigh_Q_identification` | Main identity | ✅ Proven |
| `rayleigh_Q_eq_Q` | Connects to Q3.Q | ✅ Proven |

## Periodization Sorry

The remaining sorry is for standard Poisson summation:
```
∫_{-1/2}^{1/2} ∑'_m g(θ+m) dθ = ∫_ℝ g(ξ) dξ
```
for compactly supported g. This is classical harmonic analysis.

## Applications

1. **Spectral bounds via Szegő-Böttcher**: If P_A ≥ c_*, then Toeplitz eigenvalues ≥ c_*
2. **A3 bridge**: RQ(Toeplitz - T_P_comp) ≥ c_* - ρ₁ > 0
3. **Numerical verification**: Matrix formulation enables computational checks

## Key Files

- `Q3/Proofs/Rayleigh_Q_identification.lean`
- `Q3/Proofs/Rayleigh_Fourier.lean`

## Impact

Provides **alternative path** to Q ≥ 0 via spectral analysis. May help close `Q_nonneg_on_atoms` axiom.
