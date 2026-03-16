# H-bridge macro map: three doors plus final (2026-03-16)

## Status

This is the compressed public route map for the active Suzuki/Yoshida
mainline.

It is not a new theorem note and not a new RH architecture.
Its purpose is operational: keep the phase-level local work aligned with the
actual macro route.

## Public mainline

```tex
T0\text{-}pd \to H\text{-}bridge \to H4 \to RH.
```

Inside the bridge the honest ladder remains

```tex
H1^f \to H2^f \to H3^f \to H4^f.
```

The live blocker is still only `H1^f`.

## Door 1 — mixed block

Question:

```tex
(+,-)\ \text{exact or only cap-corrected?}
```

Active theorem shape:

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+E_a^{+-}.
```

Required closure:

- bulk exactness;
- boundary cancellation;
- at worst an explicit cap-only remainder.

Operational translation:

- `P1` = tail defect setup;
- `P2` = cross-sign bulk exactness;
- `P3` = cross-sign boundary cancellation.

Current position:

```tex
\textbf{we are here: Door 1 / P3.}
```

## Door 2 — same-sign block

Question:

```tex
(++) = ?
```

Required theorem shape:

```tex
M^{++}(a)-\kappa_{+-}(a)\widetilde Q^{++}
=
H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}.
```

This is the hard core.
No new basis/rank language should enter here as theorem content.

This is also the main macro kill-gate:

- if same-sign boundary and cap do not separate cleanly,
  the current route loses its structural asymmetry.

## Door 3 — compression

Question:

```tex
\text{does finite compression create any new theorem-shaped residue?}
```

Required shape:

```tex
D_{a,M,N}=P_{M,N}\mathcal D_{a,N}P_{M,N}+\mathcal E_{a,M,N},
```

with `\mathcal E_{a,M,N}` reduced to pure compression bookkeeping.

This door is serious, but it is not supposed to invent new mathematics after
Doors 1 and 2 are settled.

## Final

After the three doors the route should no longer look like a swamp.
It should reduce to the upper bridge:

```tex
H2^f \to H3^f \to H4^f \to RH.
```

Human translation:

- `H2^f` = tail/cap reduction;
- `H3^f` = filtered gap transfer;
- `H4^f` = Suzuki endpoint to RH.

## What is dead

These are not mainline theorem language anymore:

- shared global rank-`3` defect basis;
- another rank-`4/5/6` hunt;
- raw `w_{rs}(a)=\kappa(a)q_{rs}`;
- augmented-cap positivity before the defect is classified;
- new RH architectures outside `H-bridge` and `PSD-pd`.

## Honest progress picture

Current route compression:

```tex
(+,-)\checkmark
\to
(++)=H^{\mathrm{ss}}+C^{\mathrm{cap}}
\to
\text{compression neutrality}
\to
H2^f\to H3^f\to H4^f.
```

As of this note:

- Door 1 is partly closed and `P3` is its boundary half;
- Door 2 is still the heaviest local brick;
- Door 3 should become bookkeeping if Doors 1 and 2 really land.

## Main kill gate

The main macro kill gate is Door 2:

```tex
\text{can }(++)\text{ really be split as }H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}\ ?
```

But there is one earlier near-route-kill:

```tex
\text{a surviving non-cap cross-sign boundary term at }P3.
```

If that survives, Door 1 itself stops behaving like a calibration block.
