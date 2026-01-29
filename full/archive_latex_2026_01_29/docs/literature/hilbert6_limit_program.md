# Hilbert-6 Limit Program (Deng--Hani--Ma)

Purpose
- Reviewer-facing context for why the Q3 proof is organized as a chain of limit bridges.
- Not a source of lemmas; used as a structural analogy only.

Borrowed pattern
- Two-step limit architecture: Newtonian dynamics -> Boltzmann -> fluid equations.
- Emphasis on long-time control so successive limits are compatible.

Where it shows up in Q3
- Program diagram in `sections/introduction.tex` (T0/A1'/A2/A3/RKHS/T5 chain).
- Compact-by-compact transfer (T5) plays the role of the long-time/stability bridge.
- Monotone parameter schedules in K are the analog of compatible limiting regimes.

Notes for Lean bridges
- Keep coordinate changes explicit (xi vs eta = 2pi*xi), with a dedicated crosswalk lemma.
- Treat limit passages as monotone schedules, not as pointwise limits.

Source
- Deng, Hani, Ma, "Hilbert's Sixth Problem: derivation of fluid equations via Boltzmann's kinetic theory" (arXiv:2503.01800).
