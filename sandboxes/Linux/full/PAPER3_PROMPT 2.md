# Scientific Writer Task: Paper 3

## Task: Write "Weil positivity and the Riemann Hypothesis via operator modules"

**CRITICAL RULES**:
1. DO NOT read any PDF files
2. Read ONLY the .tex files listed below
3. Read files ONE AT A TIME, max 200 lines per read
4. This is the THIRD and FINAL paper in a trilogy

---

## Context

This paper synthesizes Papers 1-2 into the main RH theorem.
It's the capstone that puts everything together.

**What Paper 1 established** (cite, don't re-prove):
- (A1') Fejér×heat density on each W_K
- (A2) Lipschitz continuity of Q

**What Paper 2 established** (cite, don't re-prove):
- (A3) Uniform Archimedean floor c* > 0
- (RKHS) Uniform prime cap ||T_P|| ≤ c*/4
- Combined: λ_min(T_M[P_A] - T_P) ≥ c*/4

**What this paper establishes**:
- (T0) Guinand–Weil normalization
- Main closure: Q ≥ 0 on entire Weil cone W
- Weil criterion: Q ≥ 0 ⟺ RH
- **Main Theorem: The Riemann Hypothesis**

---

## Source Files (read in this order)

Base path: `/Users/emalam/Documents/GitHub/chen_q3/full/sections/`

### Normalization:
1. `T0.tex` - Guinand-Weil normalization
2. `scope_notation.tex` - Conventions

### Main Results:
3. `Main_closure.tex` - Main positivity theorem
4. `Weil_linkage.tex` - RH equivalence
5. `Weil_pack.tex` - Supporting lemmas

### Context:
6. `introduction.tex` - Program diagram and motivation
7. `abstract.tex` - Abstract style reference

---

## Required Sections

### 1. Abstract (~200 words)
- Context: Weil's positivity criterion
- This paper: synthesis of analytic module chain
- Main result: RH under (T0)+(A1')+(A2)+(A3)+(RKHS)
- Method: operator-theoretic, no numerics

### 2. Introduction
- Historical context (Weil 1952, 1972; Guinand 1948)
- The positivity criterion: Q ≥ 0 ⟺ RH
- Our approach: modular analytic chain
- Reference Papers 1-2 explicitly
- State main theorem
- Paper outline

### 3. The Guinand–Weil Normalization (T0)
- Explicit formula setup
- Frequency variable ξ = η/(2π)
- Archimedean density a*(ξ)
- Prime nodes ξ_n = log(n)/(2π)
- Weil weights w_Q(n) = 2Λ(n)/√n
- Q decomposition: Q_arch - Q_prime

### 4. The Analytic Module Stack
- Summary table of all modules
- Dependency diagram:
  ```
  T0 → A1' + A2 → A3 + RKHS → Main → RH
  ```
- What each module provides

### 5. Main Closure
- Positivity on Fejér×heat generators (from A3)
- Extension to W_K via density (A1') and continuity (A2)
- Union over K: W = ∪_K W_K
- Theorem: Q(Φ) ≥ 0 for all Φ ∈ W

### 6. The Weil Criterion
- Statement of Weil's equivalence
- Historical remarks
- Proof of RH from Q ≥ 0

### 7. Main Theorem
- **Theorem**: Under (T0)+(A1')+(A2)+(A3)+(RKHS), RH holds
- Proof: combine Main closure + Weil criterion
- Remarks on scope

### 8. Discussion
- What's new: uniform bounds, no schedules
- Verification philosophy
- Relation to other approaches
- Open questions

---

## Key Formulas (must appear)

```latex
% Weil functional
Q(\Phi) = \int_{-K}^K a^*(\xi) \Phi(\xi) \, d\xi
        - \sum_{\xi_n \in [-K,K]} w_Q(n) \Phi(\xi_n)

% Normalization
\xi_n = \frac{\log n}{2\pi}, \quad w_Q(n) = \frac{2\Lambda(n)}{\sqrt{n}}

% Main positivity
Q(\Phi) \geq 0 \quad \text{for all } \Phi \in \mathcal{W}

% Weil criterion
\text{RH} \iff Q(\Phi) \geq 0 \text{ for all admissible } \Phi

% Main theorem
\text{Under (T0)+(A1')+(A2)+(A3)+(RKHS)}, \quad \text{RH holds}
```

---

## Module Summary Table (include in Section 4)

| Module | Statement | Paper |
|--------|-----------|-------|
| T0 | Guinand–Weil normalization | This paper |
| A1' | Fejér×heat density on W_K | Paper 1 |
| A2 | Lipschitz continuity L_Q(K) | Paper 1 |
| A3 | Uniform Toeplitz barrier | Paper 2 |
| RKHS | Uniform prime cap | Paper 2 |
| Main | Q ≥ 0 on W | This paper |
| RH | Riemann Hypothesis | This paper |

---

## Bibliography Requirements

Must cite:
- Weil (1952, 1972) - positivity criterion
- Guinand (1948) - summation formula
- Edwards (1974) - Riemann's Zeta Function
- Iwaniec-Kowalski (2004) - Analytic Number Theory
- Papers 1-2 of this series

---

## Output Format

- LaTeX source
- Math journal style (Annals of Mathematics style if possible)
- Theorem/Lemma/Proof environments
- Numbered equations
- ~15-20 pages target (shorter than Paper 2)

---

## Tone

This is the culmination paper. It should:
- Be accessible to number theorists
- Clearly state the main achievement
- Not over-claim (stay within scope)
- Acknowledge the modular nature of the proof

---

## Author Info

```latex
\author{Eugen Malamutmann}
\address{University of Duisburg--Essen}
\email{eugen.malamutmann@uni-due.de}
```

---

*This prompt file: /Users/emalam/Documents/GitHub/chen_q3/full/PAPER3_PROMPT.md*
