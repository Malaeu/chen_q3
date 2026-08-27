# Chen Q3 Spectral Analysis

Rigorous numerical verification and analytical estimates for the Chen Q3 approach to the Riemann Hypothesis.

## Project Structure

```
chen_q3/
├── q3.lean.aristotle/     # Lean proofs + Aristotle workflow + DB
├── ACTIVE -> q3.lean.aristotle/ACTIVE
├── full/                 # LaTeX sources + PDFs (RH_Q3.tex/RH_Q3.pdf)
├── docs/                 # Project docs and policies
├── archive/              # Legacy materials
├── bellman_bmo.py        # BMO check-mode script
├── AGENTS.md / CLAUDE.md / README.md
```

See `docs/PROJECT_STRUCTURE.md` for the archive policy and layout rules.

## Key Results

| Quantity | Value | Description |
|----------|-------|-------------|
| C* (Ceiling) | ~277 | Symbol norm saturation |
| c_arch (Floor) | ~0.19 | Archimedean floor (Lorentzian) |
| δ* (Stability) | ~0.20 | Stability ratio (Lorentzian) |
| δ* (Mellin) | ~0.79 | Optimal stability (Mellin kernel) |

## Key Findings

1. **Saturation**: ||P_A||∞ ≤ C* ≈ 277 (grub) or 109 (Q3)
2. **Floor**: c_arch ≈ 0.19 matches Q3's 0.1878
3. **Decay Law**: Slower decay → larger δ*
4. **Winner**: Mellin kernel K(ξ) = 1/(1+|ξ|^{1/2}) achieves δ* ≈ 0.79

## Running Lean Checks

```bash
cd q3.lean.aristotle
./scripts/check_axioms.sh
```

## Building the Paper

```bash
cd full
latexmk -pdf RH_Q3.tex
```

## Quick Start (after git clone)

```bash
cd chen_q3

git pull

# Lean project
cd q3.lean.aristotle
./scripts/check_axioms.sh        # Verify axioms

# Paper (LaTeX)
cd ../full
latexmk -pdf RH_Q3.tex
```

Compat: `full/q3.lean.aristotle` is a symlink to `q3.lean.aristotle` for legacy docs.

## RH Proof Status (audited 2026-08-27)

- **Unconditional RH proof:** No.
- **Compiled broad-cone RH export:** Conditional legacy surface. Its current
  Lean axiom profile includes `Q3.Weil_criterion` and
  `Q3.prime_term_le_at_t_critical_axiom`.
- **Corrected square-class interfaces:** Open conditional interfaces. They
  state their mathematical premises explicitly; no canonical public RH export
  has been established.
- **Route B:** Challenger / not RH.
- **Public-export audit baseline:** `49c3b916cfa24df9ba6b49b9d9952a0cf06d3da9` on
  branch `rh_clean`.

Historical status documents and compiled compatibility wrappers may describe
earlier project phases. A successful Lean build verifies derivations from the
declared premises; it does not establish those project premises independently.

See
[`docs/semantic_quarantine/PUBLIC_EXPORT_INDEX_AND_AXIOM_RECEIPT_v1.md`](docs/semantic_quarantine/PUBLIC_EXPORT_INDEX_AND_AXIOM_RECEIPT_v1.md)
for the pinned public-export, test-class, dependency, and axiom inventory.

## Dependencies

- Python 3.10+
- numpy
- scipy
- matplotlib
- mpmath
- Lean 4 + Mathlib (for formalization)
