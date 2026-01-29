# Tao Writing Style Guide for Scientific Writer

**Reference**: Rodgers & Tao, "The De Bruijn–Newman constant is non-negative", Forum of Mathematics Pi (2020), 62 pages.

---

## 1. Overall Structure

### Paper Organization
```
1. Introduction (with 1.1 Notation subsection at end)
2. First Technical Section (e.g., "Asymptotics of H_t")
3. Second Technical Section (e.g., "Riemann–von Mangoldt type formulae")
4. Third Technical Section (e.g., "Dynamics of zeros")
5. Fourth Technical Section (energy/monotonicity arguments)
6. Final Section (contradiction and conclusion)
```

### Length Guidelines
- **Abstract**: One dense paragraph, ~200-300 words, complete story
- **Introduction**: 6-8 pages with historical context and proof outline
- **Each technical section**: 8-12 pages with detailed calculations
- **Total**: 50-70 pages for a major result (scale down proportionally)

---

## 2. Abstract Style

**Pattern**: Single paragraph with complete narrative arc:
1. Define the main object of study
2. State the classical context/problem
3. State the main theorem
4. Describe the proof method at high level
5. Mention key technical innovations

**Example structure**:
```latex
For each $t \in \mathbb{R}$, we define [object]. It is known that [classical result].
The [famous conjecture] asserts [statement]. In this paper, we establish [main theorem].
The argument proceeds by [high-level method], building on [prior work], to obtain
[intermediate results], until one establishes [key technical step]. But this latter
claim is inconsistent with [known results], yielding the contradiction.
```

---

## 3. Introduction Structure

### Opening (1-2 paragraphs)
- Define main objects with numbered equations
- State connection to famous problem
- Give classical Fourier/integral representations

### Historical Context (1-2 pages)
- **TABLE of prior results** with dates, authors, and bounds
- Discussion of methods used in prior work
- Clear statement of the gap being filled

### Main Theorem
- Formal theorem statement in theorem environment
- **Named theorems**: `THEOREM 1.` (no title) for main result

### Proof Overview (2-3 pages)
- Heuristic discussion BEFORE formal details
- Physical analogies ("particles", "repulsion", "equilibrium")
- Key insight explained in words
- Forward references to later sections

### Remarks
- `REMARK 2.` discussing related results
- `REMARK 3.` mentioning concurrent/subsequent work

### 1.1 Notation Subsection
- Asymptotic conventions: $O(), O_\epsilon(), \tilde{O}(), o_{T\to\infty}()$
- Index conventions and principal value notation
- Modified functions (e.g., $\log_+(x) := \log(2 + |x|)$)

---

## 4. Theorem/Lemma Style

### Format
```latex
\begin{theorem}[Descriptive Name]
Statement of theorem.
\end{theorem}

\begin{proof}
Detailed proof with all steps shown.
\end{proof}
```

### Multi-part Lemmas
```latex
\begin{lemma}[Name]
Let [hypotheses]. Then:
\begin{enumerate}[(i)]
\item (Brief description) [Statement 1]
\item (Brief description) [Statement 2]
\item (Brief description) [Statement 3]
\end{enumerate}
\end{lemma}

\begin{proof}
We first prove (i). [Proof of (i)]

Now we show (ii). [Proof of (ii)]

Finally, we prove (iii). [Proof of (iii)]
\end{proof}
```

---

## 5. Proof Writing Style

### Detailed Calculations
- **Show every step** in major calculations
- Number important equations: (1), (2), ..., (57), etc.
- Reference equations explicitly: "from (24)", "inserting into (28)"

### Transition Phrases
- "We now discuss the methods of the proof."
- "We first consider the estimation of..."
- "Now we show (ii)."
- "Finally, we prove (iii)."
- "It remains to show that..."
- "It suffices to establish..."
- "Inserting these bounds into (18), we conclude that..."

### Heuristic Before Formal
Before technical lemmas, include intuitive discussion:
```latex
Informally, ODE (56) indicates that the zeros will repel each other as one goes
forward in time. On the other hand, if zeros are arranged locally in an arithmetic
progression, then ODE (56) suggests that the zeros will be in equilibrium.
```

### Physical Analogies
Use physical language for abstract concepts:
- "particles" for zeros
- "repulsion" for inverse-distance forces
- "equilibrium" for stationary configurations
- "relaxation" for convergence
- "Hamiltonian" for energy-like quantities
- "gradient flow" for dynamics

---

## 6. Reader Guidance

### Parenthetical Asides
```latex
(The reader is advised not to take the numerous factors of $\pi$, $\sqrt{2}$
and so on appearing in this section too seriously, as the exact numerical
values of these constants are not of major significance in the rest of the arguments.)
```

```latex
(the factors of $4\pi$ are not of particular significance and may be
ignored by the reader on a first read)
```

### Acknowledgments in Proofs
```latex
(We thank Alex Dobner for pointing out some issues in the original proof
of this lemma and suggesting a repaired proof, which is reproduced here.)
```

### References to External Resources
```latex
(A sketch of the argument may be found at terrytao.wordpress.com/2018/01/20.)
```

---

## 7. Equation Formatting

### Display Equations
- Major definitions: numbered
- Important intermediate steps: numbered
- Routine calculations: unnumbered

### Multi-line Displays
```latex
\begin{align}
\partial_t H(t) &= -4E(t), \\
E(t) &:= \sum_{k,k': k \neq k'} E_{kk'}(t), \\
E_{kk'}(t) &:= \frac{1}{|x_k(t) - x_{k'}(t)|^2}.
\end{align}
```

### Inline vs Display
- Complex expressions: always display
- Simple expressions ($x > 0$, $t < 0$): inline
- When in doubt: display

---

## 8. Bibliography Style

### Citation Format
- `[11, Corollary 1]` for specific results
- `[29, Theorem 9.4]` for classical theorems
- `[4]` for general reference

### Key References to Include
- Original papers establishing the problem
- Prior progress (with a TABLE)
- Key techniques borrowed from other papers
- Standard references (textbooks) for classical results

---

## 9. Section Titles

Use descriptive, technical titles:
- "Asymptotics of $H_t$"
- "Riemann–von Mangoldt type formulae"
- "Dynamics of zeros"
- "Energy estimates"
- "Proof of the main theorem"

---

## 10. Specific LaTeX Conventions

### Theorem Environments
```latex
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
```

### Custom Commands
```latex
\newcommand{\R}{\mathbb{R}}
\newcommand{\C}{\mathbb{C}}
\newcommand{\Z}{\mathbb{Z}}
\DeclareMathOperator{\Re}{Re}
\DeclareMathOperator{\Im}{Im}
```

---

## Application to RH-Q3 Papers

For Paper 2 (Toeplitz barrier + RKHS):

1. **Abstract**: Complete narrative from Toeplitz operators to prime cap
2. **Introduction**:
   - Define Weil functional Q
   - State modules A1', A2 (from Paper I)
   - State main results A3 + RKHS cap
   - Give proof outline with physical intuition
   - Include 1.1 Notation subsection
3. **Section 2**: Toeplitz operators and Szegő asymptotics
4. **Section 3**: Symbol floor $c_* = 11/10$
5. **Section 4**: RKHS construction and prime operator
6. **Section 5**: Contraction bound $\rho < c_*/4$
7. **Section 6**: Synthesis and discussion

Target: 20-25 pages with Tao-level detail.
