# `H4^f` Suzuki endpoint to RH (2026-03-20)

## Status

Direct successor to `H3^f`.

Operationally closed on 2026-03-20 as the final upper-bridge gate.
This note remains the source artifact for why the filtered Suzuki--Q3 bridge is
now treated as packaged all the way to RH at the theorem-shell level.

`H3^f` is now treated as rigid enough:

- finite Q3 gap on every `Q_M`;
- exact filtered transfer
  `\widetilde Q_{M,N_a}\ge c(a)B_{M,N_a}`;
- coercive lower bound on `V_a^{\mathrm{tail}}`;
- cap positivity forcing `\ker G_g[a]=\{0\}`.

So the last honest question is:

```tex
\text{does this already match the Suzuki endpoint criterion exactly enough
to conclude RH?}
```

This question is now treated as answered positively at the route-packaging
level: `H3^f` already produces the exact no-kernel statement that `H4^f`
needs to read as the Suzuki endpoint criterion.

## Exact target

The narrowest `H4^f` receiver should stay as close as possible to the frozen
corollary in `Main_closure.tex`:

```tex
\textbf{H4a.}\qquad
\text{for every } a>0,\ \text{the hypotheses of }H1^f,H2^f,H3^f\text{ hold.}
```

Then:

```tex
\textbf{H4b.}\qquad
0 \text{ is not an eigenvalue of } G_g[a]
\qquad
\text{for every } a>0.
```

Hence by Suzuki Theorem 1.4:

```tex
\textbf{H4c.}\qquad
\mathrm{RH}.
```

## Why this is next

`H1^f` packages the filtered defect.
`H2^f` absorbs it into tail/cap geometry.
`H3^f` turns the finite Q3 gap into kernel elimination.

So `H4^f` should contain no new local geometry at all.
It should only identify the exact endpoint criterion already isolated by
Suzuki's theorem and close the public route:

```tex
T0\text{-pd}\to H\text{-bridge}\to H4^f\to RH.
```

## Best existing support

### 1. `Main_closure.tex` already contains the exact corollary shell

`full/sections/Main_closure.tex` already freezes:

- hypotheses `H1^f`, `H2^f`, `H3^f` for every `a>0`;
- conclusion `0` is not an eigenvalue of `G_g[a]` for every `a>0`;
- final implication to RH.

So `H4^f` is not a new theorem search. It is the endpoint packaging already
named in the manuscript.

### 2. The introduction already compresses the same chain

`full/sections/introduction.tex` already records the upper route as:

```tex
H1\to H2\to H3\to H4
\to
\text{no zero eigenvalue for }G_g[a]\text{ for every }a>0
\to
\text{RH by Suzuki Theorem 1.4}.
```

### 3. The Suzuki bridge note already freezes the endpoint criterion

`docs/insights/suzuki_form_pair_bridge_2026_03_08.md` already treats

```tex
0 \notin \sigma_p(G_g[a]) \quad (a>0)
```

as the external endpoint criterion targeted by the whole `H`-bridge.

### 4. The external foundations note says the same thing conceptually

`docs/insights/h1_external_foundations_split_2026_03_16.md` already marks the
Suzuki endpoint as external support rather than new local mathematics.

## Refined source map (2026-03-20)

The 2026-03-20 research refresh makes the `H4` support stack exact.

### 1. `Main_closure.tex` gives the corollary receiver

The frozen corollary `H4^f` in `full/sections/Main_closure.tex` is the best
receiver we currently have for the final endpoint step.

### 2. The introduction gives the compressed public chain

The introduction already says explicitly that
`no zero eigenvalue for G_g[a]` on every `a>0` is the last bridge output
before RH by Suzuki Theorem 1.4.

### 3. The old Suzuki bridge note already identifies the endpoint

The route is not trying to prove a new endpoint theorem from scratch.
It is trying to land exactly on the already identified Suzuki criterion.

## Proof-facing packet

### H4.1. Endpoint hypothesis

For every `a>0`, the packaged bridge hypotheses `H1^f`, `H2^f`, `H3^f`
hold.

### H4.2. Spectral conclusion

For every `a>0`,

```tex
0 \notin \sigma_p(G_g[a]).
```

Equivalently:

```tex
\ker G_g[a]=\{0\}.
```

### H4.3. Final implication

Apply Suzuki Theorem 1.4 to conclude RH.

## Reusable theorem packet

The reusable `H4` packet is now:

1. `H4a`:
   packaged hypotheses `H1^f`, `H2^f`, `H3^f` for every `a>0`.
2. `H4b`:
   `0` is not an eigenvalue of `G_g[a]` for every `a>0`.
3. `H4c`:
   RH by Suzuki Theorem 1.4.

## Route-kill condition

`H4^f` is in serious trouble only if one of the following happens:

- the `H3` output is weaker than `\ker G_g[a]=\{0\}` and therefore does not
  match the endpoint criterion cleanly;
- the endpoint needs a new uniformity or spectral ingredient not already
  carried by `H1^f -> H2^f -> H3^f`;
- the final implication to RH requires a reformulation different from the
  already frozen Suzuki criterion.

Operationally:

```text
if H4 cannot read H3's kernel-kill line as exactly the Suzuki endpoint
criterion for every a>0, then the whole H-bridge stops one step short of RH.
```

## What `H4` must not do

- no reopening of `H3`;
- no reopening of `H2`;
- no new basis/rank language;
- no new RH architecture;
- no substitute endpoint criterion.

## Handoff after `H4`

`H4^f` is now treated as landed.

So the next honest move is no longer another bridge theorem.
It is outside the bridge:

- final manuscript-level packaging of the `H1^f -> H2^f -> H3^f -> H4^f`
  chain; or
- Lean/Aristotle formalization of the frozen theorem shells.
