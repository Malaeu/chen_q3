---
title: 2026-03-07 A3-pd packet package review
review status: reviewed
safe for embeddings: `yes`
source: inline user note
date: 2026-03-07
---

# Summary

This note survives review and sharpens the corrected-cone route one more step.

The honest theorem package is now:

1. `A1-pd` on the dense autocorrelation packet family `\mathcal G_K^{pd}`;
2. exact packet-Rayleigh on autocorrelation packets
   `\Psi_c * \widetilde{\Psi_c}`;
3. the new hard theorem `A3-pd`: positivity of the packet symbol
   `S_{g,\Delta}` on that same exact family.

# Surviving mathematical content

## 1. Corrected cone

The local target remains
\[
  \mathcal W_K^{pd}
  =
  \overline{\operatorname{cone}\{\Psi * \widetilde{\Psi}:
  \Psi\in C_c([-K/2,K/2])\}}^{\|\cdot\|_\infty}.
\]

This keeps the Weil target positive-definite / convolution-square in the correct
sense.

## 2. Density side

The note's density route survives:

- shifted Fej\'er$\times$heat atoms are used in the pre-square variable;
- the packet span `\mathcal P_K(t_0)` approximates compactly supported packets;
- autocorrelation continuity transfers this to density of
  `\mathcal G_K^{pd}` in `\mathcal W_K^{pd}`.

So `A1-pd` is the right corrected density theorem.

## 3. Exact packet-Rayleigh

The note's exact packet-Rayleigh theorem also survives.

For
\[
  \Psi_c(x)=\sum_{j=-M}^{M} c_j g(x-j\Delta),
  \qquad
  h=g*\widetilde g,
\]
one sets
\[
  \kappa_m := Q^\star(t;h(\cdot-m\Delta)),
  \qquad
  S_{g,\Delta}(\theta):=\sum_{m\in\mathbb Z}\kappa_m e^{-im\theta},
\]
and obtains
\[
  Q^\star(t;\Psi_c * \widetilde{\Psi_c})
  =
  \sum_{i,j=-M}^{M}\kappa_{i-j} c_i\overline{c_j}
  =
  \langle T_M[S_{g,\Delta}]c,c\rangle.
\]

This is the correct quadratic-form bridge on the packet side.

## 4. What does not close yet

RH is still not closed.

The remaining hard theorem is no longer `OP-pd` and no longer a same-family
bridge through `\Phi_{B,t}|p|^2`.

It is:

- prove positivity of `S_{g,\Delta}` on the same exact dense family,
- ideally with a uniform lower bound `S_{g,\Delta}(\theta)\ge c_K>0`.

That is the live theorem `A3-pd`.

# Repo impact

- Public mainline should now say:
  `T0-pd -> corrected cone -> A1-pd -> packet-Rayleigh-pd -> A3-pd -> A2 closure -> LF-pd -> G6 -> RH`.
- `OP-pd` is superseded by the more exact packet-symbol route.
- Naive packet-Rayleigh on `\Phi_{B,t}|p|^2` stays background-only.

# File pointers

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/A1prime.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/scope_notation.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Weil_pack.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
