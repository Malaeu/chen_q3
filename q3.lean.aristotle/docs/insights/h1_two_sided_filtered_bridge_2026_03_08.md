# H1 two-sided filtered bridge (2026-03-08)

## Status

Active `H1` package. This note supersedes the earlier one-sided filtered
Volterra stepping stones:

- `h1_filtered_volterra_bridge_2026_03_08.md`
- `h1_filtered_finite_section_2026_03_08.md`

Those earlier notes remain useful as historical scaffolding, but they are no
longer the live bridge contract.

The current bulk-cycle refinements of this bridge are recorded in
`h1_four_block_bulk_2026_03_08.md`
and
`h1_raw_entry_reduction_2026_03_08.md`.

## Core correction

The exact Suzuki tail basis is two-sided:

- positive tail: `\phi_n^+[a]=\chi_{n,n+1}[a]`
- negative tail: `\phi_n^-[a]=\chi_{-n,-(n+1)}[a]`

Therefore the exact filtered finite object cannot be globally one-sided
`(1+z)` on all of `P_M`. The active bridge must instead use the symmetric
two-sided tail package

```tex
\mathcal P_{M,N},\qquad
\Delta_{M,N},\qquad
B_{M,N}:=\Delta_{M,N}^*\Delta_{M,N},\qquad
\widetilde Q_{M,N}:=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}.
```

Here `\Delta_{M,N}` applies `1+z` on the positive tail and `1+z^{-1}` on the
negative tail.

## Exact metric side

With

```tex
J_a=(I_0^{(a)})^*I_0^{(a)},\qquad
S_{a,M,N}z^n=\phi_n^+[a],\qquad
S_{a,M,N}z^{-n}=\phi_n^-[a],
```

the metric pullback is exact:

```tex
S_{a,M,N}^*J_aS_{a,M,N}=B_{M,N}=\Delta_{M,N}^*\Delta_{M,N}.
```

This is no longer a heuristic brick. It is the exact metric side of the
filtered Suzuki bridge.

## No-loss bulk transfer

If the existing Q3 bulk bound is

```tex
Q_{M+1}\ge c(a)I,
```

then

```tex
\widetilde Q_{M,N}
=
\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}
\ge
c(a)\Delta_{M,N}^*\Delta_{M,N}
=
c(a)B_{M,N}.
```

So the old coarse `1/4` loss is no longer part of the active route. It remains
only a superseded historical stepping stone.

## Live blocker

The real remaining bulk theorem is now exact four-block matrix comparison:

```tex
[\langle G_g[a]\phi_n^\sigma[a],\phi_m^\tau[a]\rangle]
\quad\text{vs.}\quad
\kappa(a)\widetilde Q_{M,N}^{\sigma\tau},
\qquad
\sigma,\tau\in\{+,-\}.
```

After that, the only other live brick is the finite-dimensional Suzuki cap.

## Role of semilocal data

Semilocal Connes--Consani--Moscovici machinery remains secondary:

- useful as finite-prime basis/Gram supplier for `H1`
- not a new RH endgame
- not a replacement for the Suzuki endpoint

## Practical consequence

The active theorem stack is now

```tex
H1^f \to H2^f \to H3^f \to H4^f,
```

with:

- `H1^f`: exact filtered bulk intertwining
- `H2^f`: Suzuki tail/cap reduction
- `H3^f`: filtered gap transfer
- `H4^f`: RH via Suzuki Theorem 1.4
