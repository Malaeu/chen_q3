---
title: 2026-03-07 same-family bridge review
review status: superseded
safe for embeddings: `no`
source: inline user note
date: 2026-03-07
---

# Summary

This note is now historical.

Its surviving point was:

- `A1-pd` and packet-Rayleigh do **not** currently close RH by themselves.
- They naturally land on **two different centered families**:
  - a dense autocorrelation family coming from shifted pre-packets,
  - a positive Rayleigh family coming from centered windows times periodic modulus squares.
- The live knife-edge is therefore the **same-family bridge** between these two families,
  or an enlarged operator model acting directly on the dense family.

# Surviving mathematical content

## 1. Corrected density family

Let
\[
  \mathcal P_K(t_0)
  := \operatorname{span}\{g_{\delta,\tau}:\ |\tau|+\delta\le K/2\},
\]
where
\[
  g_{\delta,\tau}(\xi)=\Lambda_\delta(\xi-\tau)\rho_{t_0}(\xi-\tau).
\]

Then define
\[
  \mathcal G_{K,\mathrm{dens}}^{\mathrm{pd}}
  := \operatorname{cone}\{\Psi*\widetilde\Psi:\ \Psi\in\mathcal P_K(t_0)\}.
\]

The old A1 grid interpolation appears strong enough to support the pre-square density route,
because the interpolation estimate itself does not fundamentally depend on coefficient positivity.

## 2. Rayleigh-controlled family

For a centered Fej\'er$\times$heat window `\Phi_{B,t}` and a trigonometric polynomial `p`,
define
\[
  \Phi_{B,t,p}(\xi):=\Phi_{B,t}(\xi)|p(\xi)|^2.
\]

Then the family
\[
  \mathcal G_{K,\mathrm{Ray}}^{\mathrm{pd}}
  := \operatorname{cone}\{\Phi_{B,t,p}\}
\]
is exactly the kind of centered family already seen by the Toeplitz/RKHS quadratic form.

## 3. Honest blocker

The honest remaining blocker is not merely
`A1-pd + packet-Rayleigh`.
It is:

\[
  \mathcal G_{K,\mathrm{dens}}^{\mathrm{pd}}
  \quad\text{vs.}\quad
  \mathcal G_{K,\mathrm{Ray}}^{\mathrm{pd}}.
\]

One still needs one of:

1. a same-family density theorem
   \[
     \overline{\operatorname{cone}(\mathcal G_{K,\mathrm{Ray}}^{\mathrm{pd}})}^{\|\cdot\|_\infty}
     = \mathcal W_K^{\mathrm{pd}},
   \]
   or
2. an enlarged operator model acting directly on
   `\mathcal G_{K,\mathrm{dens}}^{\mathrm{pd}}`.

# Repo impact

- This note is consistent with the corrected-cone pivot.
- It was itself superseded later on 2026-03-07 by the stronger obstruction:
  the naive family `\Phi_{B,t}|p|^2` is too large to serve as the closure family.
- Current source of truth therefore no longer treats `SF-pd` as the live frontier.

# File pointers

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/A1prime.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/scope_notation.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
