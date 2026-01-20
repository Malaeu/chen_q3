# PROBLEM.md — Q3 Lean Formalization

## Problem Statement

Complete the Lean 4 formalization of Chen's Q3 approach to the Riemann Hypothesis by closing remaining axioms: A1 (density), A3 (Rayleigh bridge), and Q non-negativity on atoms.

## Sub-Problems

### SP1: A1 Density WK Axiom
**Goal:** Prove `A1_density_WK_axiom` — the weighted Korobov density theorem.
**Status:** 1 sorry remains (`h_approx` triangle inequality).
**Search hints:** `Korobov density`, `Fejér kernel approximation`, `weighted density theorem`, `trigonometric polynomial approximation`

### SP2: A3 Bridge Axiom (Rayleigh-Q Identification)
**Goal:** Prove `A3_bridge_axiom` — connect Toeplitz symbol floor to Rayleigh quotient.
**Status:** BLOCKED on Szegő theorem formalization.
**Search hints:** `Toeplitz finite section method`, `Szegő limit theorem`, `symbol floor theorem`, `Rayleigh quotient Toeplitz`

### SP3: Q Non-negativity on RKHS Atoms
**Goal:** Prove `Q_nonneg_on_atoms_of_A3_RKHS_axiom`.
**Status:** Blocked on SP2.
**Search hints:** `RKHS kernel evaluation`, `reproducing kernel Hilbert space positivity`, `prime vector orthogonality`

### SP4: P_A Periodization Integral
**Goal:** Fast path for `∫ P_A = arch_term` without tsum/integral swap timeout.
**Search hints:** `Poisson summation formula`, `periodization integral`, `Lean Mathlib integral tactics`, `tsum integral interchange`

### SP5: Normalization Factor Consistency
**Goal:** Fix (2M+1) factor mismatch in Rayleigh quotient normalization.
**Search hints:** `Toeplitz matrix normalization`, `finite section scaling`, `averaging operator normalization`

## Research Directions

### RD1: Toeplitz Operator Theory
- Böttcher & Silbermann books
- Finite section method convergence
- Symbol calculus for Toeplitz operators

### RD2: Lean Mathlib Tactics
- `integral_tsum` conditions
- `MeasureTheory` interchange lemmas
- `Summable` criteria automation

### RD3: RKHS Methods
- Prime-indexed kernel constructions
- Riesz representation in sequence spaces
- Contraction estimates

### RD4: Heat Kernel Localization
- Fejér × heat kernel products
- Support localization via heat decay
- Archimedean vs prime balance

## Failed Approaches (DO NOT SEARCH)

- Generic `exact?` or `aesop` heavy solutions (timeout)
- ζ(2) or π bounds (too indirect)
- Full Szegő theorem generality (overkill, need finite-dimensional)

## Success Criteria

1. `lake build Q3.Main` succeeds
2. `#print axioms Q3.Main.RH_of_Weil_and_Q3` shows only standard axioms:
   - `propext`, `Classical.choice`, `Quot.sound`
3. Axiom count reduced from 10 to ≤ 3 (standard only)

## Current Axiom Count: 10

```
Standard (3): propext, Classical.choice, Quot.sound
Level 1 (4): Weil_criterion, a_star_pos, a_star_bdd_on_compact, a_star_continuous
Level 2 (3): A1_density_WK_axiom, A3_bridge_axiom, Q_nonneg_on_atoms_of_A3_RKHS_axiom
```

## Key Files

| File | Purpose |
|------|---------|
| `full/q3.lean.aristotle/Q3/Axioms.lean` | Axiom definitions |
| `full/q3.lean.aristotle/Q3/Main.lean` | Main theorem chain |
| `full/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md` | Current status |

---
*Auto-generated for Research Swarm System*
