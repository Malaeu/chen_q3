# Same-Family Bridge After The Corrected-Cone Pivot

Date: 2026-03-07

## Status

This note is accepted as a live architectural correction.

## Core point

After the corrected-cone pivot, the route no longer fails because the target cone is broad.
That part is already fixed.

The new knife-edge is stricter:

- `A1-pd` feeds a dense family
  `\mathcal G_{K,\mathrm{dens}}^{\mathrm{pd}}`
  built from autocorrelations of shifted pre-packets.
- packet-Rayleigh feeds a positive family
  `\mathcal G_{K,\mathrm{Ray}}^{\mathrm{pd}}`
  built from centered windows times modulus squares.

These are both centered and both plausible, but they are not yet the same exact family.

## External check

- External source confirmation: the positive-definite form of the Weil criterion is
  stated in the recent paper
  “On the Hilbert space derived from the Weil distribution”
  ([Cambridge Core](https://www.cambridge.org/core/product/FD33EBD117A6B448053450DD8D62ADB6/core-reader)),
  which explicitly phrases Weil positivity on convolution squares
  `W(\psi * \widetilde\psi)`.

## Honest blocker

The public missing theorem is now:

\[
  \overline{\operatorname{cone}(\mathcal G_{K,\mathrm{Ray}}^{\mathrm{pd}})}^{\|\cdot\|_\infty}
  = \mathcal W_K^{\mathrm{pd}},
\]

or else an enlarged operator model acting directly on
`\mathcal G_{K,\mathrm{dens}}^{\mathrm{pd}}`.

## Consequence

The phrase
“A1-pd + packet-Rayleigh closes the corrected route”
is too strong and must be retired from active docs.

The honest public phrasing is:

- `A1-pd` = corrected density input,
- packet-Rayleigh = corrected positivity/identification input,
- `SF-pd` = same-family bridge between them.
