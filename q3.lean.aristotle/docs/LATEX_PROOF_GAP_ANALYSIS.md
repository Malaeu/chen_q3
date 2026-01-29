# Critical Gap in LaTeX Proof: Two Different T_P Operators

**Date:** 2026-01-22  
**Status:** CRITICAL - Numerical verification shows Q(Φ_{t_sym}) < 0

## Summary

The LaTeX proof of Q ≥ 0 contains a fundamental gap: it conflates two different prime operators T_P that have incompatible definitions.

## The Two T_P Operators

### 1. Rayleigh T_P^{(M)} (rayleigh_bridge.tex:28)

```latex
T_P^{(M)} := Σ_{n: |ξ_n|≤B} w(n)·Φ_{B,t}(ξ_n)·|v_n^{(M)}⟩⟨v_n^{(M)}|
```

- **Weights:** `w(n) · Φ_{B,t}(ξ_n)` — includes Fejér×heat damping
- **Norm bound:** `||T_P^{(M)}|| ≤ Σ w(n)·Φ_{B,t}(ξ_n)` (triangle inequality)
- **Purpose:** Used in Rayleigh identification to connect matrix eigenvalues to Q functional

### 2. RKHS T_P (RKHS/main.tex:17)

```latex
T_P := Σ_{α_n∈[-K,K]} w_RKHS(n)·|k_{α_n}⟩⟨k_{α_n}|
```

- **Weights:** `w_RKHS(n) = Λ(n)/√n` — NO Fejér×heat factor
- **Norm bound:** `||T_P|| ≤ ρ(t_rkhs)` via Gram geometry
- **Purpose:** Provides contraction bound in RKHS framework

## The Gap in Theorem A3 (A3/main.tex)

Theorem A3 claims:
```
λ_min(T_M[P_A] - T_P) ≥ c_*/4 > 0
```
and derives `Q(Φ_{B,t_sym}) ≥ 0`.

**The proof uses:**
1. `P_A` built with `t_sym = 3/50 = 0.06`
2. `||T_P|| ≤ ρ(t_rkhs)` from RKHS analysis with `t_rkhs ≫ t_sym`
3. Two-scale decoupling: "no coupling between t_sym and t_rkhs is needed"

**The problem:**
- The RKHS bound `||T_P|| ≤ ρ(t_rkhs)` applies to the RKHS operator (without Φ weights)
- The Rayleigh identification requires the Rayleigh operator (with Φ weights at t_sym)
- These are **different operators** with different norm bounds

## Numerical Verification

Parameters: B = 3, t_sym = 0.06

### Archimedean Term
```
∫_{-1/2}^{1/2} P_A(θ) dθ = 2π ∫_ℝ a(ξ)·Φ_{B,t}(ξ) dξ = 11.059
```

### Prime Term (with Fejér×heat weights)
```
Σ_{|ξ_n|≤B} w(n)·Φ_{B,t}(ξ_n) = 27.347
```
where w(n) = 2Λ(n)/√n and ξ_n = log(n)/(2π)

### Q Functional
```
Q(Φ_{B=3, t=0.06}) = 11.059 - 27.347 = -16.288 < 0
```

**This directly contradicts the claim Q(Φ_{t_sym}) ≥ 0.**

## Analysis

The "two-scale decoupling" claimed in Remark 5.1 does not work because:

1. **Rayleigh identification requires same t:** The identity
   ```
   Q(Φ_{B,t}) = ⟨(T_M[P_A] - (2M+1)T_P^{(M)})1, 1⟩
   ```
   holds only when P_A and T_P^{(M)} use the **same** Fejér×heat parameter t.

2. **RKHS bound uses different operator:** The bound `||T_P|| ≤ ρ(t_rkhs)` applies to
   the RKHS operator T_P = Σ w_RKHS(n)|k_n⟩⟨k_n|, not the Rayleigh operator.

3. **No bridge between operators:** There is no lemma connecting the two T_P definitions.

## Possible Fixes

### Option A: Same t for both
Use t = t_rkhs for both P_A and T_P. But then:
- P_A floor drops dramatically (min P_A ≈ 0.0004 at t=1.0)
- The c_* = 11/10 floor no longer holds

### Option B: Modified Rayleigh identity
Derive a Rayleigh identity that decouples the two t parameters. This would require:
- A new functional Q_decoupled(t_sym, t_rkhs)
- Proof that Q_decoupled ≥ 0 implies Q ≥ 0

### Option C: Different proof strategy
Abandon the Rayleigh approach and prove Q ≥ 0 directly using:
- Fourier analysis
- Contour integration
- Explicit positivity certificates

## Conclusion

The current LaTeX proof has a fundamental structural gap. The "two-scale architecture" 
is mathematically invalid because it applies a norm bound for one operator (RKHS T_P) 
to a different operator (Rayleigh T_P^{(M)}).

Numerical computation confirms that Q(Φ_{t_sym}) = -16.29 < 0, contradicting the theorem claim.

## Files Referenced

| File | Content |
|------|---------|
| `sections/A3/main.tex` | Theorem A3 (gap location) |
| `sections/A3/rayleigh_bridge.tex` | Rayleigh T_P^{(M)} definition |
| `sections/RKHS/main.tex` | RKHS T_P definition |
| `sections/RKHS/prime_cap.tex` | RKHS norm bound ρ(t) |
| `sections/A3/symbol_floor.tex` | P_A definition and c_* floor |
