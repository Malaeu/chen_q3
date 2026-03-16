# H1 external foundations for the split route (2026-03-16)

## Status

Supporting note only.

This file is conceptual support for the current `H1` route language:

- mixed block `(+,-)`;
- same-sign block `(++)`;
- finite cap;
- finite compression.

It is not a tracker-level source of truth and it does not replace
`ACTIVE/PHASE_MONITOR.md`.

RH itself remains open; Clay still lists the problem as unsolved.

## What is already externally proved

### 1. Suzuki endpoint geometry

The external endpoint is already in place:

```tex
0 \notin \sigma_p(G_g[a]) \quad \text{for every } a>0.
```

In the Suzuki/Yoshida route this is the RH-equivalent endpoint criterion, and
it is exactly the type of endpoint targeted by `H4^f`.

Within the repo this is already frozen in:

- `docs/insights/suzuki_form_pair_bridge_2026_03_08.md`

### 2. Suzuki tail/cap geometry

Suzuki also already provides the right finite-dimensional geometry for the cap
part:

- a tail space `V_N(a)` built from adjacent packets;
- coercive control on that tail side;
- a finite-dimensional annihilator/cap reduction;
- a finite matrix receiver for the remaining positivity/nonnegativity problem.

That is the right external conceptual ancestor of our future
`C_{a,N}^{\mathrm{cap}}`.

### 3. Classical Toeplitz/Hankel boundary mechanism

Classical operator theory already gives the right language for boundary or
commutator residues:

```tex
T_{fg}-T_fT_g = H_{\tilde f}H_g,
\qquad
H_{fg}=H_fT_g+T_{\tilde f}H_g.
```

These identities are the natural reason to expect a same-sign
Toeplitz/Hankel/commutator defect, rather than a mysterious floating low-rank
basis effect.

### 4. Paired-operator language for the mixed block

There is also an external operator language that matches the mixed `(+,-)`
channel more naturally than the same-sign Toeplitz+Hankel block:

```tex
S_{\phi,\psi}=M_\phi P_+ + M_\psi P_-.
```

This makes it structurally plausible that the cross-sign block should collapse
to exactness or cap-only, while the surviving boundary residue should sit in
the same-sign channels.

## What is not externally proved

The key filtered split theorem of the current `Q_\zeta`-core is not already
available as a ready-made external theorem.

In particular, the literature does not hand us the exact package

```tex
\mathcal D_{a,N}^{+-}=C_{a,N}^{+-,\mathrm{cap}},
\qquad
\mathcal D_{a,N}^{++}=H_{a,N}^{\mathrm{ss}}+C_{a,N}^{++,\mathrm{cap}},
```

in our current filtered defect language.

So the external material supports the route, but it does not close the live
split theorem for us.

## Why this supports the current route

The current route in `H1` is:

- Door 1: mixed block `(+,-)`;
- Door 2: same-sign block `(++)`;
- Door 3: compression neutrality.

The external facts above support exactly that asymmetry:

1. `(+,-)` should be exact-or-cap-only, because the mixed block is naturally
   paired-operator shaped rather than same-sign Hankel shaped.
2. `(++)` is the right place for a surviving same-sign boundary or commutator
   term, because Toeplitz/Hankel identities live there naturally.
3. finite cap should be extracted from Suzuki-style tail/annihilator geometry,
   not from a new numerical basis hunt.
4. finite compression should come only after the infinite-tail decomposition is
   fixed.

That is exactly the language already frozen in:

- `docs/insights/h_bridge_three_doors_macro_map_2026_03_16.md`
- `docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`

## Three theorem targets

### 1. Mixed adapter

Primary target:

```tex
\mathcal D_{a,N}^{+-}=C_{a,N}^{+-,\mathrm{cap}}.
```

Preferred stronger version:

```tex
\mathcal D_{a,N}^{+-}=0
\quad
\text{after quotienting the finite cap channel.}
```

### 2. Same-sign boundary

Primary target:

```tex
\mathcal D_{a,N}^{++}=H_{a,N}^{\mathrm{ss}}+C_{a,N}^{++,\mathrm{cap}},
```

where `H_{a,N}^{\mathrm{ss}}` is an explicit same-sign
Toeplitz/Hankel/commutator term.

### 3. Compression neutrality

Only after the infinite-tail split is fixed:

```tex
D_{a,M,N}=P_{M,N}\mathcal D_{a,N}P_{M,N}+\mathcal E_{a,M,N},
```

with `\mathcal E_{a,M,N}` reduced to pure compression bookkeeping.

## Strict boundary: external facts vs our live theorem shape

This note must not be read as “the literature already proves our split
theorem”.

The honest boundary is:

- external literature gives the endpoint, the tail/cap geometry, and the right
  operator language for boundary residues;
- our live work still has to prove the filtered split itself.

So this file is conceptual support, not a substitute theorem.

Operationally that means:

- if `P3` leaves a genuinely non-cap cross-sign boundary term, the current
  reset is in serious trouble;
- if Door 2 does not separate
  `H_{a,N}^{\mathrm{ss}}` from `C_{a,N}^{\mathrm{cap}}`,
  the current route loses its structural asymmetry.

## Minimal reference stack

- Repo route note:
  `docs/insights/suzuki_form_pair_bridge_2026_03_08.md`
- Current live blocker note:
  `docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md`
- Macro route note:
  `docs/insights/h_bridge_three_doors_macro_map_2026_03_16.md`
- Clay status page:
  <https://www.claymath.org/millennium-problems/>
- Paired operators:
  <https://arxiv.org/abs/2404.05435>
- Generalized Toeplitz plus Hankel operators:
  <https://arxiv.org/abs/1501.04271>
