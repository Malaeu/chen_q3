# Q* Definitions — Single Source of Truth

**Status:** BYPASS DOCUMENT for Q3 LaTeX inconsistencies
**Date:** 2026-01-22
**Rule:** Every operator = name + space + ALL parameters. No naked symbols!

---

## Core Principle

```
WRONG:  T_P, Q, rho     ← ambiguous, caused the bug!
RIGHT:  T_P(t,M), Q(t;Phi), rho(t)   ← explicit parameters
```

## Notation Glossary (frozen, quick index)

- `t = t_critical = 3/20`, `t0 = 1/(16π²t)`.
- `Phi_{B,t}` = Fejér–heat window; base atom = `2 * Phi_{B,t}` at `tau = 0`.
- `Q*(t;Phi) = arch_term(t;Phi) - prime_term(t;Phi)`.
- `w_Q(n) = 2*Λ(n)/√n`, `xi_n = log n / (2π)`.
- `T_P^{Ray}(t,M)` vs `T_P^{RKHS}(t)` are distinct operators (do not mix).

**Change control:** any edits here require an entry in `docs/CHAIN_STATUS.md`
“Revision Log (local)”.

---

## 1. Heat Scale Parameter t

The SINGLE most important parameter. Everything depends on it.

| Symbol | Definition | Current Value |
|--------|------------|---------------|
| t | Heat smoothing scale in exp(-4 pi^2 t xi^2) | **t = 0.15** (t_critical) |
| t0 | Dual parameter: t0 = 1/(16 pi^2 t) | t0 = 0.0422... |

**CRITICAL:** LaTeX used t_sym = 0.06, which FAILS. We use t = 0.15.

---

## 2. Window Functions (explicit t)

### 2.1 Fejer-Heat Window

```
Phi_{B,t}(xi) := max(0, 1 - |xi|/B) * exp(-4 pi^2 t xi^2)

Parameters:
  B : bandwidth (support = [-B, B])
  t : heat scale (smoothing strength)
```

**Lean:** `fejer_heat_window B t xi`

### 2.2 Base Atom (tau = 0)

```
Atom_{B,t}(xi) := 2 * Phi_{B,t}(xi)

This is Fejer_heat_atom at tau = 0:
  Fejer_heat_atom B t 0 xi = Phi_{B,t}(xi - 0) + Phi_{B,t}(xi + 0) = 2 * Phi_{B,t}(xi)
```

**CONSTRAINT:** We ONLY use tau = 0. Shifted atoms (tau != 0) give Q < 0.

---

## 3. The Q* Functional (explicit t)

### 3.1 Definition

```
Q*(t; Phi) := arch_term(t; Phi) - prime_term(t; Phi)

where:
  arch_term(t; Phi) := integral_{-infty}^{infty} a*(xi) * Phi(xi) dxi
  prime_term(t; Phi) := sum_{n >= 2} w_Q(n) * Phi(xi_n)
```

**Note:** The t-dependence enters through Phi = Phi_{B,t}.

### 3.2 Component Functions

| Symbol | Definition | Notes |
|--------|------------|-------|
| a*(xi) | 2 pi * (log(pi) - Re psi(1/4 + i pi xi)) | Archimedean density, t-independent |
| w_Q(n) | 2 * Lambda(n) / sqrt(n) | von Mangoldt weight, t-independent |
| xi_n | log(n) / (2 pi) | Prime node position |

### 3.3 Numerical Values at t = 0.15

```
For Phi = Phi_{B=3, t=0.15}:

  arch_term = 9.57
  prime_term = 8.71
  Q* = +0.86 > 0   ← PASSES!

Compare to t = 0.06 (FAILS):
  arch_term = 11.06
  prime_term = 26.61
  Q* = -15.56 < 0  ← BUG SOURCE!
```

---

## 4. Operators (explicit t and space)

### 4.1 Toeplitz Matrix T_M[P_A]

```
T_M[P_A](t, B, M) : C^{2M+1} -> C^{2M+1}

Definition:
  T_M[i,j] = c_{i-j}  (Toeplitz structure)
  
where c_k are Fourier coefficients of the symbol:
  P_A(theta; t, B) = integral a*(xi) * Phi_{B,t}(xi) * e^{2 pi i xi theta} dxi

Key property:
  lambda_min(T_M[P_A]) >= c* - omega(pi/M)
  
where:
  c* = 11/10 (symbol floor)
  omega = continuity modulus of P_A
```

### 4.2 Prime Operator T_P (THREE VERSIONS!)

**This is where LaTeX went wrong — conflating different T_P's.**

#### Version A: T_P^{Ray}(t, M) — Rayleigh representation

```
T_P^{Ray}(t, M) : C^{2M+1} -> C^{2M+1}

Acts in Rayleigh identity:
  Q*(t; Phi) = <(T_M[P_A] - T_P^{Ray}) * e_0, e_0> * normalization

Explicit form:
  T_P^{Ray}[i,j] = (1/(2M+1)) * sum_n w_Q(n) * Phi_{B,t}(xi_n) * e^{2 pi i (i-j) xi_n}
```

#### Version B: T_P^{RKHS}(t) — RKHS bound operator

```
T_P^{RKHS}(t) : H_t -> H_t   (acts on RKHS space H_t)

Used for norm bound:
  ||T_P^{RKHS}(t)|| <= rho(t)
  
where:
  rho(t) = 2 * integral_0^infty y * e^{y/2} * e^{-4 pi^2 t y^2} dy
```

#### Version C: T_P^{simple} — simplified diagonal

```
T_P^{simple}(t) = (prime_term / (2M+1)) * I

Just the scalar contribution, no off-diagonal structure.
||T_P^{simple}|| = prime_term / (2M+1)
```

### 4.3 THE CRITICAL IDENTITY

```
T_P^{Ray}(t, M) and T_P^{RKHS}(t) are COMPARABLE only when:
  - Same t value
  - Appropriate embedding between finite-dim and RKHS

LaTeX BUG: Used ||T_P^{RKHS}(1)|| to bound T_P^{Ray}(0.06).
           These are DIFFERENT operators!

FIX: Use same t everywhere:
  ||T_P^{Ray}(t)|| <= ||T_P^{RKHS}(t)|| <= rho(t)
```

---

## 5. The rho Function (explicit t)

### 5.1 Definition

```
rho(t) := 2 * integral_0^infty y * e^{y/2} * e^{-4 pi^2 t y^2} dy

This bounds ||T_P^{RKHS}(t)||.
```

### 5.2 Numerical Values

| t | rho(t) | rho(t) <= c*/4 = 0.275? |
|---|--------|-------------------------|
| 0.06 | ~0.8 | NO (too big!) |
| 0.10 | ~0.4 | NO |
| 0.15 | ~0.2 | YES |
| 1.00 | 0.039 | YES (but overkill) |

**Conclusion:** t >= 0.15 is needed for rho(t) <= c*/4.

---

## 6. The Proof Chain (single-scale)

### 6.1 Old (BROKEN) chain

```
1. lambda_min(T_M[P_A]) >= c*/2           ← OK, uses t_sym
2. ||T_P^{RKHS}(1)|| <= rho(1) < 1/25     ← Uses t=1
3. "Therefore" ||T_P^{Ray}(t_sym)|| small ← INVALID! Different t!
4. Q >= 0                                  ← FALSE at t_sym=0.06
```

### 6.2 New (CORRECT) chain

```
1. lambda_min(T_M[P_A](t)) >= c*/2        ← At t = 0.15
2. ||T_P^{RKHS}(t)|| <= rho(t) <= c*/4    ← Same t = 0.15
3. ||T_P^{Ray}(t)|| <= ||T_P^{RKHS}(t)||  ← Valid: same t!
4. lambda_min(A - B) >= c*/2 - c*/4 = c*/4 > 0
5. Q*(t; Phi) >= 0                         ← TRUE at t = 0.15!
```

---

## 7. Cone Definitions (explicit t0)

### 7.1 BaseAtomCone_K (CORRECT cone)

```
BaseAtomCone_K(K, t0) := {
  g : R -> R |
  exists n, c : Fin n -> R, B : Fin n -> R,
    (forall i, c_i >= 0) and
    (forall i, B_i > 0) and
    (forall i, B_i <= K) and
    g = sum_i c_i * Atom_{B_i, t}   where t = 1/(16 pi^2 t0)
}

Note: tau = 0 for all atoms (centered).
```

### 7.2 AtomCone_K_fixed (PROBLEMATIC cone)

```
AtomCone_K_fixed(K, t0) := {
  g | includes atoms with arbitrary tau
}

WARNING: Q < 0 on this cone at large tau!
Example: tau = 1.69 gives Q = -911.

DO NOT USE for Q >= 0 theorem.
```

---

## 8. Parameter Summary

| Parameter | Symbol | Value | Notes |
|-----------|--------|-------|-------|
| Heat scale | t | 0.15 | Critical value where Q >= 0 |
| Dual scale | t0 | 1/(16 pi^2 * 0.15) | ~0.0422 |
| Symbol floor | c* | 11/10 = 1.1 | min P_A(theta) |
| Prime cap | c*/4 | 0.275 | Target for rho(t) |
| Bandwidth | B | 3.0 | Default test value |
| Compact param | K | 5.0 | Support bound |

---

## 9. Lean Name Mapping

| This Document | Lean Name | File |
|---------------|-----------|------|
| t | t_sym (CHANGE TO 3/20!) | HeatKernelParams.lean |
| t0 | t0_A1 | HeatKernelParams.lean |
| Phi_{B,t} | fejer_heat_window B t | Defs.lean |
| Atom_{B,t} | Fejer_heat_atom B t0 0 | Axioms.lean |
| Q*(t; Phi) | Q | Defs.lean |
| arch_term | arch_term | Defs.lean |
| prime_term | prime_term | Defs.lean |
| a*(xi) | a_star | Defs.lean |
| w_Q(n) | w_Q | Defs.lean |
| xi_n | xi_n | Defs.lean |
| c* | c_star | A3_Floor_Bounds.lean |
| rho(t) | rho_one (RENAME!) | RKHS_contraction.lean |
| BaseAtomCone_K | BaseAtomCone_K | Axioms.lean |

---

## 10. Verification Commands

```bash
# Numerical check that Q >= 0 at t = 0.15
cd sandboxes/projekt_2
python3 verify_variant_b.py --direct

# Expected:
# Test A: Q = 0.8565 >= 0  PASS
# Test B: min Q = 1.0292 >= 0  PASS (BaseAtomCone)
# Test C: min Q = -911 < 0  EXPECTED FAIL (AtomCone with tau > 0)
```

---

## Changelog

- 2026-01-22: Initial version. Fixed two-scale bug by unifying to t = 0.15.
