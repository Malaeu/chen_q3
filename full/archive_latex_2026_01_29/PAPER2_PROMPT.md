# Scientific Writer Task: Paper 2

## Task: Write "Toeplitz barrier and RKHS prime contraction for the Weil criterion"

**CRITICAL RULES**:
1. DO NOT read any PDF files
2. Read ONLY the .tex files listed below
3. Read files ONE AT A TIME, max 200 lines per read
4. This is the SECOND paper in a trilogy

---

## Context

This paper develops the operator-theoretic core of an RH proof via Weil's criterion.
It builds on Paper 1 (Fejér-heat density + Lipschitz) and feeds into Paper 3 (main theorem).

**What Paper 1 established** (reference, don't re-prove):
- Fejér×heat cone G_K is dense in C⁺_even([−K,K])
- Q is Lipschitz continuous with constant L_Q(K)

**What this paper must establish**:
- Uniform Archimedean floor c* > 0 on the symbol P_A
- Szegő–Böttcher Toeplitz asymptotics for λ_min
- RKHS contraction: ||T_P|| ≤ ρ(t) < c*/4
- Combined: λ_min(T_M[P_A] - T_P) ≥ c*/4 > 0

---

## Source Files (read in this order)

Base path: `/Users/emalam/Documents/GitHub/chen_q3/full/sections/`

### A3 Module (Toeplitz barrier):
1. `A3/main.tex` - Overview and main theorem
2. `A3/symbol_floor.tex` - Symbol positivity floor
3. `A3/rayleigh_bridge.tex` - Rayleigh quotient identification
4. `A3/fejer_modulus.tex` - Modulus of continuity
5. `A3/arch_bounds.tex` - Explicit bounds
6. `A3/matrix_guard.tex` - Discretization

### RKHS Module (prime cap):
7. `RKHS/main.tex` - RKHS mechanism
8. `RKHS/core.tex` - Core estimates
9. `RKHS/prime_cap.tex` - Uniform cap
10. `RKHS/prime_norm_leq_rho.tex` - Norm bound

---

## Required Sections

### 1. Abstract (~150 words)
- State that this develops the Toeplitz/RKHS machinery
- Reference Paper 1 for prerequisites
- Main result: uniform A3 bridge inequality

### 2. Introduction
- Brief motivation (Weil criterion context)
- Reference Paper 1 explicitly
- State main theorem informally
- Paper outline

### 3. The Archimedean Symbol
- Definition via Fejér×heat periodization
- Positivity: min P_A(θ) ≥ c* = 11/10
- Lipschitz property

### 4. Szegő–Böttcher Asymptotics
- Classical theory (cite Böttcher-Silbermann)
- λ_min(T_M[f]) approximation
- Error control via modulus of continuity

### 5. RKHS Prime Contraction
- Gaussian kernel RKHS setup
- Gram matrix structure
- Gershgorin-type bound
- Closed-form ρ(t) with no tables

### 6. The Uniform A3 Bridge
- Two-scale architecture (t_sym vs t_rkhs)
- Main theorem: λ_min ≥ c*/4
- Conversion to Q ≥ 0 on generators

### 7. Discussion
- Connection to Paper 3
- What's new: K-independent bounds
- Legacy branches archived

---

## Key Formulas (must appear)

```latex
% Symbol floor
\min_{\theta \in \mathbb{T}} P_A(\theta) \geq c_* = \frac{11}{10}

% Szegő–Böttcher
\lambda_{\min}(T_M[P_A]) \geq c_* - C_{\mathrm{SB}} \omega_{P_A}(1/2M)

% Weight cap
w_{\max} = \sup_n \frac{\Lambda(n)}{\sqrt{n}} \leq \frac{2}{e} < 1

% RKHS bound
\|T_P\| \leq w_{\max} + \sqrt{w_{\max}} S_K(t) =: \rho(t)

% Main result
\lambda_{\min}(T_M[P_A] - T_P) \geq \frac{c_*}{4} > 0
```

---

## Bibliography Requirements

Must cite:
- Szegő (1952) - original Toeplitz theory
- Böttcher-Silbermann (2006) - Analysis of Toeplitz Operators
- Aronszajn (1950) - RKHS theory
- Paulsen-Raghupathi (2016) - modern RKHS
- Horn-Johnson (2013) - matrix analysis (Gershgorin)
- Paper 1 of this series

---

## Output Format

- LaTeX source
- Standard math journal style (article class)
- Theorem/Lemma/Proof environments
- Numbered equations
- ~20-25 pages target

---

## Author Info

```latex
\author{Eugen Malamutmann}
\address{University of Duisburg--Essen}
\email{eugen.malamutmann@uni-due.de}
```

---

*This prompt file: /Users/emalam/Documents/GitHub/chen_q3/full/PAPER2_PROMPT.md*
