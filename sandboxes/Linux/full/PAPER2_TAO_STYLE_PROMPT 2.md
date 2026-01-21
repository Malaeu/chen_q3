# Paper 2: Toeplitz Barrier and RKHS Prime Contraction
## Tao Writing Style Version

**CRITICAL RULES**:
1. **DO NOT read any PDF files** - they are too large and will crash the session
2. Read ONLY the `.tex` source files listed below, one at a time, max 200 lines each
3. **Follow TAO_STYLE_GUIDE.md** for writing style
4. Target length: **20-25 pages** (not 8 pages!)
5. Output to: `/Users/emalam/Documents/GitHub/chen_q3/full/paper2_toeplitz_rkhs/main.tex`

---

## Style Reference

**READ FIRST**: `/Users/emalam/Documents/GitHub/chen_q3/full/TAO_STYLE_GUIDE.md`

This guide is based on Rodgers & Tao's 62-page paper on the de Bruijn–Newman constant.

---

## Source Files to Read

**Base path**: `/Users/emalam/Documents/GitHub/chen_q3/full/sections/`

Read in this order, max 200 lines each:

1. `A3/main.tex` - Overview of A3 bridge
2. `A3/symbol_floor.tex` - Uniform Archimedean floor $c_* = 11/10$
3. `A3/rayleigh_bridge.tex` - Rayleigh quotient identification
4. `A3/fejer_modulus.tex` - Fejér modulus of continuity
5. `RKHS/main.tex` - RKHS mechanism overview
6. `RKHS/prime_cap.tex` - Prime operator cap $\rho(1) < 1/25$
7. `RKHS/prime_norm_leq_rho.tex` - Operator norm bound

---

## Required Structure (Tao Style)

### Abstract (one paragraph, ~250 words)
- Define Weil functional Q on test function space
- State the positivity question and its connection to RH
- State the two main results: (1) Toeplitz barrier A3, (2) RKHS cap
- Describe proof method: Szegő–Böttcher asymptotics + RKHS contraction
- End with "This paper is the second of three developing an operator-theoretic approach to the Weil positivity criterion."

### 1. Introduction (6-8 pages)

#### Opening
- Define the Weil functional Q with numbered equations
- State connection to Riemann Hypothesis via Weil criterion
- Reference Paper I for A1', A2 modules

#### Main Results
State as formal theorems:

**THEOREM 1 (Toeplitz barrier).** For any $g \in G_K^+$ with $K \geq K_0$, one has
$$Q(g) \geq c_* \cdot \|g\|_{L^2}^2 - O(K^{-1})$$
where $c_* = 11/10$ is the Archimedean floor.

**THEOREM 2 (RKHS prime cap).** There exists $t_* > 0$ such that for all $t \geq t_*$, the prime operator $T_P$ satisfies
$$\|T_P\|_{\mathcal{H}_t \to \mathcal{H}_t} \leq \rho(t) < \frac{c_*}{4}$$

#### Proof Overview (heuristic first!)
- Physical analogy: Toeplitz eigenvalues as "spectral barriers"
- Heuristic: why $c_* = 11/10$ is the natural floor
- Why RKHS contraction controls prime contribution
- Forward references to sections

#### REMARK 3. (Relation to Paper I)
#### REMARK 4. (Connection to Paper III)

#### 1.1 Notation
- $\xi_n = \log(n)/(2\pi)$ for prime nodes
- $w_Q(n) = 2\Lambda(n)/\sqrt{n}$ for Weil weights
- $W_K = [-K, K]$ bandwidth notation
- $G_K^+$ Fejér-heat cone
- Asymptotic conventions: $O(), O_K(), \tilde{O}()$

### 2. Toeplitz Operators and Szegő Asymptotics (4-5 pages)
- Definition of Toeplitz matrix $T_N(f)$
- Szegő's first theorem (eigenvalue distribution)
- Böttcher's refinement (error bounds)
- **LEMMA 5** with numbered equations and detailed proof

### 3. The Archimedean Symbol (4-5 pages)
- Definition of $P_A(\theta)$ with explicit formula
- **LEMMA 6 (Symbol floor).** $\inf_\theta P_A(\theta) = c_* = 11/10$
- Detailed calculation showing why 11/10
- Connection to Rayleigh quotient

### 4. The Rayleigh-Toeplitz Bridge (3-4 pages)
- **PROPOSITION 7 (Rayleigh identification).**
- Show $Q_A(g) = \langle g, T_N(P_A) g \rangle + O(...)$
- Detailed proof with all steps

### 5. RKHS Construction (4-5 pages)
- Define reproducing kernel $K_t(x,y)$
- Define Hilbert space $\mathcal{H}_t$
- **LEMMA 8** (RKHS properties)
- Connection to heat-Fejér convolution

### 6. Prime Operator Contraction (4-5 pages)
- Define prime operator $T_P$
- **THEOREM 9 (Prime cap).** Detailed proof
- Why $\rho(1) < 1/25 < c_*/4$
- Two-scale decoupling: $t_{sym}$ vs $t_{rkhs}$

### 7. Discussion (1-2 pages)
- Summary of what A3 + RKHS achieve
- Forward reference to Paper III
- Open questions

---

## Key Constants (must appear)

| Constant | Value | Description |
|----------|-------|-------------|
| $c_*$ | 11/10 | Archimedean floor |
| $C_{SB}$ | 4 | Szegő–Böttcher constant |
| $t_{sym}$ | 3/50 | Symbol heat parameter |
| $t_{rkhs}$ | $\geq 1$ | RKHS threshold |
| $B_{min}$ | 3 | Minimum bandwidth |
| $w_{max}$ | $\leq 2/e$ | Maximum weight |

---

## Writing Style Checklist

- [ ] One-paragraph abstract with complete narrative
- [ ] Numbered equations for all important formulas
- [ ] References like "from (24)", "inserting into (28)"
- [ ] Heuristic discussion BEFORE formal proofs
- [ ] Physical analogies (barriers, contraction, spectral gaps)
- [ ] Multi-part lemmas with (i), (ii), (iii)
- [ ] Transition phrases: "We now show...", "It remains to establish..."
- [ ] Reader guidance: "(may be ignored on first reading)"
- [ ] Section 1.1 Notation at end of Introduction
- [ ] Named theorems: THEOREM 1 (Toeplitz barrier)
- [ ] Detailed proofs showing ALL calculation steps
- [ ] Forward/backward references to Papers I and III

---

## Compilation

```bash
cd /Users/emalam/Documents/GitHub/chen_q3/full/paper2_toeplitz_rkhs
pdflatex main.tex && pdflatex main.tex
```

Target: 20-25 pages, Tao-level detail and rigor.
