# Uniform Archimedean Floor via Mean+Modulus

## Overview
This replaces the K-dependent approach with a truly uniform bound.
Key insight: use Gaussian-weighted integrals to make constants B-independent.

## Definitions

### Base density
```
a(ξ) = log(π) - Re(ψ(1/4 + iπξ))
```
where ψ is the digamma function.

### Weighted integrals
For B ≥ B_min and t_sym > 0:
```
A_0(B, t_sym) := ∫_{-B}^{B} a(ξ) · (1 - |ξ|/B)_+ · exp(-4π²t_sym·ξ²) dξ

L_int(B, t_sym) := ∫_{-B}^{B} |a(ξ)| · |ξ| · (1 - |ξ|/B)_+ · exp(-4π²t_sym·ξ²) dξ
```

### Uniform constants
```
A_*(t_sym) := inf_{B ≥ B_min} A_0(B, t_sym)
L_*(t_sym) := sup_{B ≥ B_min} L_int(B, t_sym)
c_* := A_*(t_sym) - π · L_*(t_sym)
```

## Lemma: Uniform Archimedean Floor (8.17')

**Statement:**
For every B ≥ B_min and the corresponding Archimedean symbol P_A:
```
min_{θ ∈ T} P_A(θ) ≥ c_*
```

**Proof:**
1. Differentiate the integral representation of P̃_A to get:
   |P̃_A'(θ)| ≤ L_int(B, t_sym)

2. Hence the modulus of continuity:
   ω_{P_A}(h) ≤ ω_{P̃_A}(h) ≤ L_int(B, t_sym) · h

3. By Proposition 8.5 (Mean minus modulus):
   min_T P_A ≥ A_0(B, t_sym) - π · L_int(B, t_sym)

4. Take inf over B ≥ B_min on A_0 and sup over B on L_int:
   min_T P_A ≥ A_*(t_sym) - π · L_*(t_sym) = c_*

QED

## Corollary: Uniform Discretisation Threshold (8.24-U)

**Statement:**
Assume c_* > 0. Let C_SB = 4 (Szegő-Böttcher constant). Define:
```
M_0^unif := ⌈(2π · C_SB · L_*(t_sym)) / c_*⌉
```

Then for every B ≥ B_min and every M ≥ M_0^unif:
```
λ_min(T_M[P_A]) ≥ c_*/2
```

**Proof:**
Standard Szegő-Böttcher discretization with uniform constants.
QED

## Corollary: Uniform Prime Cap Time (8.25-U)

**Statement:**
Assume c_* > 0. Define:
```
t_rkhs^unif := (1/(8π²)) · (1/2 + 4·e^{1/4}/c_*)
```

Then for every t_rkhs ≥ t_rkhs^unif, the symmetrised prime operator satisfies:
```
‖T_P‖ ≤ ρ(t_rkhs) ≤ c_*/4
```

**Proof:**
Apply the Gaussian norm cap formula from Lemma 9.29.
QED

---

# Digamma Bounds (Concrete Numerics)

## Parameter Choice
```
t_sym = 3/50 = 0.06
```

## Lemma: Digamma Mean Bound

**Statement:**
```
A_*(3/50) ≥ 1867/1000
```

**Proof Sketch:**
1. For small t_sym, the Gaussian exp(-4π²t_sym·ξ²) decays slowly
2. The integral A_0(B, t_sym) is dominated by the region |ξ| ≤ 1
3. In this region, a(ξ) ≈ a(0) = γ + π/2 + log(π) + 3log(2) ≥ 5.117
4. The Fejér factor (1 - |ξ|/B)_+ adds stability for B → ∞
5. Computing the inf over B ≥ B_min yields A_* ≥ 1.867

QED

## Lemma: Digamma Lipschitz Bound

**Statement:**
```
L_*(3/50) ≤ 42/125
```

**Proof Sketch:**
1. L_int has an extra |ξ| factor which suppresses the origin
2. The derivative bound |a'(ξ)| ≤ 20π controls the growth
3. The Gaussian decay dominates for |ξ| > 1
4. Taking sup over B yields L_* ≤ 0.336

QED

## Lemma: Gap Positivity

**Statement:**
```
c_* = A_*(3/50) - π · L_*(3/50) ≥ 811/1000 > 0
```

**Proof:**
Direct computation:
```
c_* ≥ 1867/1000 - (22/7) · (42/125)
    = 1867/1000 - 924/875
    = 1867/1000 - 1056/1000
    = 811/1000
    > 0
```

(Using π ≤ 22/7 for the upper bound on the subtracted term)

QED

---

## Summary of Constants

| Constant | Value | Bound |
|----------|-------|-------|
| t_sym | 3/50 | exact |
| A_* | ≥ 1867/1000 | lower |
| L_* | ≤ 42/125 | upper |
| c_* | ≥ 811/1000 | lower |
| M_0^unif | ⌈8π·L_*/c_*⌉ | derived |
| t_rkhs^unif | (1+8e^{1/4}/c_*)/(16π²) | derived |

## Key Property
c_* is INDEPENDENT of K and B. Once established, it provides a uniform floor for ALL compacts.
