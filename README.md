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

<!-- PROJECT_STATE:START -->
<!-- project_state_sha256: e7d259915d2f200c0693e2d2907ddfe639e0930c2b73fa68f95434677698f020 -->
Project-level current status is generated from
`orchestrator/state/PROJECT_STATE.json`.
Human views: `docs/generated/PROJECT_STATUS.md` and
`docs/generated/WORK_QUEUE.md`.
Current projection: RH proof `NO`; Route B `CHALLENGER / NOT_RH`; goal `058`.
<!-- PROJECT_STATE:END -->

Historical status documents and compiled compatibility wrappers may describe
earlier project phases. A successful Lean build verifies derivations from the
declared premises; it does not establish those project premises independently.

The generated project status links the pinned public-export, test-class,
dependency, and axiom inventory.

## Dependencies

- Python 3.10+
- numpy
- scipy
- matplotlib
- mpmath
- Lean 4 + Mathlib (for formalization)
