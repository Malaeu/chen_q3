# Naive Rayleigh Family Obstruction

Date: 2026-03-07

## Status

This note is accepted as the live architectural correction after the
same-family phase.

## Core point

The corrected-cone pivot survives, but the naive centered family

\[
  \mathcal G_{K,\mathrm{Ray}}^{\mathrm{pd}}
  = \operatorname{cone}\{\Phi_{B,t}|p|^2\}
\]

is too large to serve as the public closure family.

On compacts `K<\pi`, the positivity of the centered window `\Phi_{B,t}` and
Stone--Weierstrass imply that `\Phi_{B,t}r^2` is already dense in the broad local
cone of even nonnegative bumps. Combined with the full quadratic-form meaning of
Lemma 8.8 and the centered A3 positivity engine, that would force false broad
local positivity.

## Consequence

The live blocker is no longer `SF-pd`.

The honest next theorem is `OP-pd`:

- an exact **smaller** operator-controlled packet family inside
  `\mathcal W_K^{\mathrm{pd}}`,
- with a quadratic-form identification on that same family,
- without enlarging back to arbitrary local bumps.

## Public phrasing

- `A1-pd` remains the dense corrected-cone input.
- naive packet-Rayleigh on `\Phi_{B,t}|p|^2` is background-only.
- `OP-pd` is the active frontier.
