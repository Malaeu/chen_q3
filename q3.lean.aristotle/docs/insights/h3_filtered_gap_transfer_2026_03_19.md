# `H3^f` filtered gap transfer (2026-03-19)

## Status

Direct successor to `H2^f`.

Operationally closed on 2026-03-20 as the second upper-bridge gate.
This note remains the source artifact for why the filtered finite Q3 gap plus
finite cap positivity are now treated as rigid enough to hand upward into the
Suzuki endpoint step.

`H2^f` is now treated as rigid enough:

- closed tail space `V_a^{\mathrm{tail}}`;
- finite-dimensional cap complement `A_a^{\mathrm{cap}}`;
- `q_{G,a}`-orthogonal split;
- finite Hermitian cap matrix `H_a^{\mathrm{cap}}`.

The next honest question is therefore no longer internal to `H3^f`, but the
endpoint handoff:

```tex
\text{does this kernel-kill output match Suzuki Theorem 1.4 cleanly enough
to imply RH?}
```

## Exact target

The narrowest `H3^f` receiver should stay as close as possible to the frozen
theorem shell in `Main_closure.tex`:

```tex
\textbf{H3a.}\qquad
Q_M\ge c(a)\,I_{P_M}
\qquad
\text{for every }M\ge N_a+1.
```

Then for every `M>N_a`,

```tex
\textbf{H3b.}\qquad
\widetilde Q_{M,N_a}\ge c(a)\,B_{M,N_a}.
```

Hence the filtered gap transfers to the tail space:

```tex
\textbf{H3c.}\qquad
q_{G,a}(v)\ge \kappa(a)c(a)\,q_{J,a}(v)
\qquad
\text{for every } v\in V_a^{\mathrm{tail}}.
```

If, in addition, the finite cap matrix `H_a^{\mathrm{cap}}` is positive
definite, then

```tex
\textbf{H3d.}\qquad
\ker G_g[a]=\{0\}.
```

Equivalently, `0` is not an eigenvalue of `G_g[a]`.

## Why this is next

`H2^f` isolates the geometry.
`H3^f` must now transfer the filtered Q3 gap into that geometry.

So `H3^f` is exactly the upper-bridge step that should turn:

```text
closed tail space + finite cap complement
```

into:

```text
no kernel for G_g[a].
```

Without `H3^f`, the route still has geometry but no actual spectral
consequence.

## Best existing support

### 1. `Main_closure.tex` already contains the right theorem shell

`full/sections/Main_closure.tex` already freezes the theorem label
`\label{thm:H3-filtered-transfer}` with the correct logical flow:

- Q3 gap on finite sections;
- filtered transfer to `\widetilde Q_{M,N_a}\ge c(a)B_{M,N_a}`;
- coercive lower bound on `V_a^{\mathrm{tail}}`;
- positive cap matrix implies `\ker G_g[a]=\{0\}`.

### 2. `H2` already provides the exact input

`docs/insights/h2_filtered_cap_reduction_2026_03_19.md` already hands `H3`
the only geometry it is allowed to use:

- `V_a^{\mathrm{tail}}`;
- `A_a^{\mathrm{cap}}`;
- orthogonal split;
- finite Hermitian cap matrix.

So `H3` is not a new structural search.

### 3. The two-sided bridge note already explains the no-loss transfer

`docs/insights/h1_two_sided_filtered_bridge_2026_03_08.md` already freezes the
exact metric side and the no-loss relation
`\widetilde Q_{M,N}\ge c(a)B_{M,N}`.

That is precisely the mechanism `H3` needs.

### 4. The macro route already isolates this as the next honest upper gate

`docs/insights/h_bridge_three_doors_macro_map_2026_03_16.md` already says the
local three-door work should collapse into:

```tex
H2^f\to H3^f\to H4^f.
```

So `H3` should be read as a genuine upper-bridge transfer theorem, not as a
return to local defect bookkeeping.

## Refined source map (2026-03-19)

The 2026-03-19 research refresh makes the `H3` support stack more exact.

### 1. `Main_closure.tex` gives the theorem shell

The frozen theorem shell in `full/sections/Main_closure.tex` is the best
receiver we currently have for `H3^f`.

### 2. `H2` gives the admissible geometry

`H3` is only allowed to read the closed tail space plus finite-dimensional cap
complement package from `H2`.

### 3. The old bridge notes already explain the transfer mechanism

The filtered bridge notes already demote all old losses and make the
`\widetilde Q \to B` transfer exact at the metric level.

## Proof-facing packet

### H3.1. Finite Q3 gap hypothesis

Primary first line:

```tex
Q_M\ge c(a)\,I_{P_M}
\qquad
\text{for every }M\ge N_a+1.
```

### H3.2. Filtered metric transfer

Primary bridge line:

```tex
\widetilde Q_{M,N_a}\ge c(a)\,B_{M,N_a}.
```

### H3.3. Tail-space coercivity

Primary consequence on the tail space:

```tex
q_{G,a}(v)\ge \kappa(a)c(a)\,q_{J,a}(v)
\qquad
(v\in V_a^{\mathrm{tail}}).
```

### H3.4. Kernel elimination

Final local consequence:

```tex
H_a^{\mathrm{cap}}>0
\quad\Longrightarrow\quad
\ker G_g[a]=\{0\}.
```

### H3.5. Exact `H2 -> H3` input package

At theorem level `H3^f` should consume only:

- closed tail space `V_a^{\mathrm{tail}}`;
- finite-dimensional cap complement `A_a^{\mathrm{cap}}`;
- `q_{G,a}`-orthogonal split;
- finite Hermitian cap matrix `H_a^{\mathrm{cap}}`.

No new geometric object is allowed to appear here.

## Reusable theorem packet

The reusable `H3` packet is now:

1. `H3a`:
   finite Q3 gap on `Q_M`.
2. `H3b`:
   filtered transfer `\widetilde Q_{M,N_a}\ge c(a)B_{M,N_a}`.
3. `H3c`:
   coercive lower bound on `V_a^{\mathrm{tail}}`.
4. `H3d`:
   positive cap matrix kills the kernel.

## Route-kill condition

`H3^f` is in serious trouble if:

- the finite Q3 gap does not transfer to the filtered metric side;
- the tail-space coercive lower bound fails;
- the cap matrix positivity is not enough to eliminate the kernel;
- or the argument needs new geometry not already frozen by `H2`.

Operationally:

```text
if H3 cannot turn the filtered Q3 gap plus cap positivity into
\ker G_g[a]=\{0\}, then the upper bridge no longer looks like a real
spectral transfer theorem.
```

More explicitly, the bad forms are:

```tex
\widetilde Q_{M,N_a}\not\ge c(a)B_{M,N_a}
\quad\text{for arbitrarily large }M,
```

or

```tex
q_{G,a}(v_j)\to 0
\quad\text{for a }q_{J,a}\text{-normalized tail sequence }v_j\in V_a^{\mathrm{tail}},
```

or

```tex
H_a^{\mathrm{cap}}\nsucc 0
\quad\text{with a surviving cap null vector.}
```

## What `H3` must not do

- no reopening of `H2` geometry;
- no reopening of `H1`;
- no new basis/rank language;
- no jump to `H4` without explicit kernel elimination.

## Handoff after `H3`

If `H3^f` lands, the next honest move is:

```tex
H4^f:\ \text{Suzuki endpoint to RH}.
```

At that point the route should already have:

- coercive lower bound on the tail space;
- positive finite cap matrix;
- kernel elimination.

## Success criterion

This note lands only if the next theorem attempt is no longer
“can the gap transfer work?”, but the final endpoint step `H4^f`.
