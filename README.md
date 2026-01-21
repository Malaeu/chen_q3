# Chen Q3 Spectral Analysis

Rigorous numerical verification and analytical estimates for the Chen Q3 approach to the Riemann Hypothesis.

## Project Structure

```
chen_q3/
├── docs/                   # Project docs and policies
├── src/                    # Python source code
│   ├── saturation_proof.py     # Symbol norm saturation
│   ├── floor_proof.py          # Archimedean floor (Lorentzian)
│   ├── floor_q3_real.py        # Floor with real digamma
│   ├── floor_saturation.py     # Floor saturation analysis
│   ├── floor_adaptive_t.py     # Adaptive t parameter test
│   ├── analyze_digamma_poison.py # Digamma sign analysis
│   ├── rescue_archimedes.py    # Gamma metric test
│   ├── rescue_gamma_pure.py    # Pure Gamma periodization
│   └── merlin_kernel_test.py   # Kernel comparison (★ Mellin winner)
│
├── output/                 # Generated figures
│   ├── saturation_proof.png
│   ├── floor_proof.png
│   ├── floor_adaptive_comparison.png
│   ├── digamma_poison_analysis.png
│   ├── rescue_archimedes.png
│   └── merlin_kernel_test.png
│
├── paper/                  # LaTeX paper
│   ├── main.tex               # Main document
│   ├── introduction.tex       # Section 1
│   ├── preliminaries.tex      # Section 2
│   ├── lemma_saturation.tex   # Section 3: Ceiling lemma
│   ├── lemma_floor.tex        # Section 4: Floor lemma
│   ├── theorem_stability.tex  # Section 5: Main theorem
│   ├── numerical_results.tex  # Section 6: Experiments
│   └── conclusions.tex        # Section 7
│
├── full/                   # Lean proofs and formalization workflow
│   └── q3.lean.aristotle/      # A3_FLOOR kernel proofs + DB + Aristotle I/O
│
├── data/                   # Data files
└── archive/                # Legacy materials moved out of root
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

## Running the Code

```bash
cd src
python saturation_proof.py
python floor_proof.py
python merlin_kernel_test.py
```

## Building the Paper

```bash
cd paper
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

## Quick Start (after git clone)

```bash
cd chen_q3
git pull

# Main Lean project
cd full/q3.lean.aristotle
./scripts/check_axioms.sh        # Verify axioms (expect 6)
./scripts/contribution_stats.sh  # Code statistics

# Sandbox (isolated experiments)
cd sandboxes/Linux
# Work here without affecting main
```

## Current Status (2026-01-21)

- **Axioms:** 6 total (3 standard Lean + 3 project)
- **Remaining closable:** 1 (`Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`)
- **Lines of code:** 44,250 (Q3/ + aristotle_output/)
- **Aristotle contribution:** 20% (in proof chain)
- **DB lemmas:** 555

## Dependencies

- Python 3.10+
- numpy
- scipy
- matplotlib
- mpmath
- Lean 4 + Mathlib (for formalization)
