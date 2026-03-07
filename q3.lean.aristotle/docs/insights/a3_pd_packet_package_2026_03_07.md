# A3-pd Packet Package

Date: 2026-03-07

## Status

Accepted as the live corrected-cone theorem package.

## Core point

The corrected positive-definite route now splits cleanly into three parts:

1. `A1-pd`: density of the centered autocorrelation packet family
   `\mathcal G_K^{pd}` in `\mathcal W_K^{pd}`;
2. exact packet-Rayleigh on the same packet side:
   `Q^\star(t;\Psi_c * \widetilde{\Psi_c}) = \langle T_M[S_{g,\Delta}]c,c\rangle`;
3. the single live hard theorem `A3-pd`: positivity of the packet symbol
   `S_{g,\Delta}` on that same exact dense family.

## What survives

- `A1-pd` survives as the right density theorem on the corrected cone.
- packet-Rayleigh survives, but only in the autocorrelation-packet form
  `\Psi_c * \widetilde{\Psi_c}`.
- the naive family `\Phi_{B,t}|p|^2` remains background-only because it is too
  large and would force false broad local positivity.

## New knife-edge

The project is no longer blocked on a vague same-family bridge and no longer on a
smaller undefined operator family.

The exact remaining theorem is:

\[
  S_{g,\Delta}(\theta)\ge c_K>0
  \qquad\text{on the same dense packet family used by } A1\text{-pd}.
\]

That is the honest `A3-pd` frontier.

## Repo consequence

- supersede `OP-pd` as the public frontier;
- keep naive packet-Rayleigh only as background;
- freeze the public mainline as
  `T0-pd -> corrected cone -> A1-pd -> packet-Rayleigh-pd -> A3-pd -> A2 closure -> LF-pd -> G6 -> RH`.
