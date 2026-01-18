# RH-Q3 Paper Trilogy: Scientific Writer Instructions

**CRITICAL**: DO NOT read the full RHQ3 PDF! It will overflow context.
Read ONLY the specific .tex files listed below, in the order specified.

---

## Overview: Three Papers from One Proof

The RH-Q3 project proves the Riemann Hypothesis via operator-theoretic methods.
The proof is modular: (T0) + (A1') + (A2) + (A3) + (RKHS) → Q ≥ 0 → RH.

We split this into **three self-contained papers**:

| Paper | Title | Modules | Status |
|-------|-------|---------|--------|
| 1 | Fejér–heat generators and Lipschitz control | A1' + A2 | **DONE** |
| 2 | Toeplitz barrier and RKHS prime contraction | A3 + RKHS | TO WRITE |
| 3 | Weil positivity and the Riemann Hypothesis | T0 + Main + Weil | TO WRITE |

---

## Paper 1: REVIEW ONLY (Already Written)

**Location**: `/Users/emalam/Documents/GitHub/chen_q3/full/Fejér–heat generators and Lipschitz control for the Weil quadratic functional/main.pdf`

**Content**:
- Fejér×heat cone density (A1')
- Lipschitz continuity of Q (A2)
- 15 pages, technical note style

**Task**: Light review for consistency with Papers 2-3. Check:
- Notation consistency
- Cross-references to "companion paper" language
- Abstract/intro mentions series of papers

---

## Paper 2: WRITE NEW

**Title**: "Toeplitz barrier and RKHS prime contraction for the Weil criterion"

**Content**: The operator-theoretic core
- (A3) Archimedean Toeplitz barrier via Szegő–Böttcher
- (RKHS) Uniform prime cap without K-dependent schedules

### Source Files to Read (IN ORDER, max 200 lines each):

```
BASE: /Users/emalam/Documents/GitHub/chen_q3/full/sections/

1. A3/main.tex              -- Core A3 theorem and lemmas
2. A3/symbol_floor.tex      -- Uniform floor c* = 11/10
3. A3/rayleigh_bridge.tex   -- Toeplitz-Rayleigh identification
4. A3/fejer_modulus.tex     -- Modulus of continuity ω_PA
5. A3/arch_bounds.tex       -- Archimedean bounds
6. A3/matrix_guard.tex      -- Discretization M → ∞

7. RKHS/main.tex            -- RKHS contraction mechanism
8. RKHS/core.tex            -- Gram matrix bounds
9. RKHS/prime_cap.tex       -- Uniform cap ρ(t) ≤ c*/4
10. RKHS/prime_norm_leq_rho.tex -- ||T_P|| ≤ ρ bound
```

### Key Results to Include:

1. **Uniform Archimedean floor** (Lemma): min_{θ∈T} P_A(θ) ≥ c* = 11/10
2. **Szegő–Böttcher bridge** (Lemma): λ_min(T_M[P_A]) ≥ c* - C·ω_PA(1/2M)
3. **Uniform discretization** (Corollary): M₀^unif such that above ≥ c*/2
4. **Weight cap** (Lemma): w_max = sup Λ(n)/√n ≤ 2/e < 1
5. **RKHS contraction** (Theorem): ||T_P|| ≤ ρ(t_rkhs) ≤ c*/4
6. **Uniform A3 bridge** (Theorem): λ_min(T_M[P_A] - T_P) ≥ c*/4 > 0

### Structure:

```
1. Introduction
   - Reference Paper 1 for density/Lipschitz
   - State main theorem: uniform A3 bridge

2. The Archimedean Symbol P_A
   - Definition via Fejér×heat periodization
   - Positivity floor c* > 0

3. Szegő–Böttcher Toeplitz Asymptotics
   - λ_min approximation
   - Modulus of continuity control

4. RKHS Framework for Prime Operator
   - Gaussian kernel RKHS
   - Gram matrix Gershgorin bounds
   - Closed-form ρ(t) cap

5. The Uniform A3 Bridge
   - Two-scale separation (t_sym vs t_rkhs)
   - Combined bound: c*/4 > 0

6. Discussion
   - Connection to Paper 3 (full RH proof)
   - K-independent nature (no schedules)
```

### Constants Table (include in paper):

| Constant | Value | Where Defined |
|----------|-------|---------------|
| c* | 11/10 | Uniform arch floor |
| C_SB | 4 | Szegő–Böttcher |
| t_sym | 3/50 | Symbol heat param |
| w_max | 2/e ≈ 0.736 | Weight cap |
| B_min | TBD | Min bandwidth |
| M₀^unif | TBD | Min discretization |

---

## Paper 3: WRITE NEW

**Title**: "Weil positivity and the Riemann Hypothesis via operator modules"

**Content**: The synthesis and main theorem
- (T0) Guinand–Weil normalization
- Main closure: combining all modules
- Weil criterion: Q ≥ 0 ⟺ RH

### Source Files to Read (IN ORDER):

```
BASE: /Users/emalam/Documents/GitHub/chen_q3/full/sections/

1. T0.tex                   -- Normalization (ξ_n = log n / 2π, etc.)
2. scope_notation.tex       -- Notation conventions
3. Main_closure.tex         -- Main positivity theorem
4. Weil_linkage.tex         -- RH equivalence
5. Weil_pack.tex            -- Supporting lemmas (if needed)
6. introduction.tex         -- For context on program diagram
7. abstract.tex             -- For abstract template
```

### Key Results to Include:

1. **Guinand–Weil normalization** (Proposition): crosswalk from standard to our conventions
2. **Module dependency diagram**: (T0) → (A1') → (A2) → (A3) → (RKHS) → Main → RH
3. **Main positivity** (Theorem): Q(Φ) ≥ 0 for all Φ ∈ W
4. **Weil criterion** (Theorem): Q ≥ 0 ⟺ RH
5. **RH Theorem**: Under (T0)+(A1')+(A2)+(A3)+(RKHS), RH holds

### Structure:

```
1. Introduction
   - Historical context (Weil, Guinand)
   - Reference Papers 1-2 for technical modules
   - State main result: RH under the analytic chain

2. The Guinand–Weil Normalization (T0)
   - Explicit formula conventions
   - Frequency/time crosswalk
   - Q decomposition: Q_arch - Q_prime

3. The Analytic Module Stack
   - Summary of (A1'), (A2) from Paper 1
   - Summary of (A3), (RKHS) from Paper 2
   - Dependency diagram

4. Main Closure
   - Generator positivity → cone positivity
   - Density + continuity argument
   - W_K exhaustion to W

5. The Weil Criterion and RH
   - Theorem statement
   - Proof via Weil's equivalence

6. Discussion
   - What is new (no K-dependent schedules)
   - Verification and reproducibility
   - Open questions
```

---

## Cross-References Between Papers

### Paper 1 should say:
- "This is the first in a series of three papers..."
- "The Toeplitz barrier (A3) and RKHS contraction are developed in [companion paper]"
- "The main closure combining these tools is presented in [third paper]"

### Paper 2 should say:
- "This paper continues [Paper 1], which established density and Lipschitz control"
- "The synthesis with the Weil criterion appears in [Paper 3]"
- "We use the Fejér×heat generators from [Paper 1]"

### Paper 3 should say:
- "This paper completes the trilogy begun in [Papers 1-2]"
- "Density and Lipschitz control are established in [Paper 1]"
- "The Toeplitz barrier and RKHS cap are proved in [Paper 2]"

---

## Author Information

**Author**: Eugen Malamutmann
**Affiliation**: University of Duisburg–Essen
**ORCID**: 0000-0003-4624-5890

---

## Writing Style Notes

- Use Guinand–Weil normalization throughout (not Weil–Guinand)
- Szegő (with ő), Böttcher (with ö), Fejér (with é)
- All bounds explicit and closed-form
- No numerical tables in main proofs (archive in appendix if needed)
- Target: math journal (Ann. Math, Invent. Math style)

---

## DO NOT READ

- `/Users/emalam/Documents/GitHub/chen_q3/RH_Q3_malamutmann_v*.pdf` (too large!)
- Any compiled PDF > 20 pages
- Legacy/deprecated sections in IND_AB/, D3/, T5/

---

## Quick Start Commands

```bash
# Navigate to sections
cd /Users/emalam/Documents/GitHub/chen_q3/full/sections

# Check file sizes
wc -l A3/*.tex RKHS/*.tex

# Read specific file
cat A3/main.tex | head -100
```

---

*Last updated: 2026-01-16*
