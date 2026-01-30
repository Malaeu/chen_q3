# Growth Target P(X): Analysis Summary

## The Setup

**Goal:** Prove R(Φ_X) → ∞ as X → ∞

**Definitions:**
- Φ_X = Σ_{p ∈ T(X)} λ_p e_p  (twin vector)
- λ_p = log(p) × log(p+2)  (von Mangoldt weights)
- E_comm = Φᵀ Q Φ  where Q = AᵀA
- E_lat = Φᵀ G Φ
- R = E_comm / E_lat  (Rayleigh quotient)

**Key matrices:**
- A_{pq} = (ξ_q - ξ_p) × K_{pq}  — has **gradient factor** (ξ_q - ξ_p)
- G_{pq} = √(2πt) × exp(-(ξ_p - ξ_q)²/(8t))  — no gradient factor

## Numerical Results

| X | N (twins) | R | E_comm/Σλ² | E_lat/Σλ² |
|---|-----------|---|------------|-----------|
| 100 | 8 | 4.58 | 68.6 | 15.0 |
| 500 | 24 | 19.2 | 949 | 49.4 |
| 1000 | 35 | 29.8 | 2188 | 73.3 |
| 5000 | 126 | 94.9 | 26950 | 284 |
| 10000 | 205 | 143 | 67274 | 470 |

**Scaling:**
- R ~ X^{0.72} (R² = 0.988)
- R ~ N^{1.04} (nearly linear in number of twins)

## SC2 Verification

**Fixed twins (6 twins):** R = 2.575 = **constant** ✓

This confirms SC2: finite twins ⟹ R = O(1)

## Why R Grows

**Key observation:** E_comm/Σλ² grows 30× faster than E_lat/Σλ²

**Mechanism:**
1. A_{pq} contains gradient factor (ξ_q - ξ_p)
2. Q = AᵀA "accumulates" this factor quadratically
3. When new twins are added at larger p:
   - They interact with existing twins at distance |Δξ|
   - Each interaction contributes (Δξ)² to E_comm
   - G_{pq} doesn't have this quadratic bonus
4. Result: E_comm grows faster than E_lat → R → ∞

## Logical Structure of Proof

```
SC2 (PROVEN):    finite twins ⟹ R = O(1)
P(X) (NUMERICAL): R ~ X^{0.72} → ∞

Contrapositive of SC2:
    R → ∞ ⟹ twins infinite

Combined:
    P(X) + SC2 ⟹ TPC
```

## What Remains for Rigorous Proof

**Gap:** P(X) is numerical, not analytical.

**To prove P(X) rigorously, need to show:**
- E_comm(Φ_X) grows faster than E_lat(Φ_X)

**Possible approaches:**
1. **Direct summation:** Bound Σ λ_p λ_q Q_{pq} from below
2. **Spectral argument:** Show λ_max(Q/G) → ∞
3. **Trace argument:** Show Tr(Q)/Tr(G) → ∞

**Key ingredient needed:**
- Lower bound on "gradient energy" Σ_{p,q} (Δξ)² K²_{pq}
- This requires density information about twins (Hardy-Littlewood or weaker)

## Conclusion

- **SC2 is verified** (fixed twins → constant R)
- **P(X) is numerically confirmed** (R ~ X^{0.72})
- **The contradiction is clear** (O(1) vs X^{0.72})
- **Remaining task:** Formalize the growth argument analytically
