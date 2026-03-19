# `H2^f` Suzuki tail/cap reduction (2026-03-19)

## Status

Direct successor to `P7`.

`H1^f` is now treated as packaged enough to hand upward:

- exact-or-cap-only mixed block;
- same-sign boundary term `H_a^{\mathrm{ss}}`;
- finite cap term `C_a^{\mathrm{cap}}`;
- no extra independent compression defect.

So the next honest question is:

```tex
\text{can this cleaned }H1^f\text{ package be absorbed into Suzuki tail/cap geometry?}
```

## Exact target

The narrowest `H2^f` receiver should stay as close as possible to the frozen
theorem shell in `Main_closure.tex`:

```tex
\textbf{H2a.}\qquad
V_a^{\mathrm{tail}}
:=
\overline{\bigcup_{M>N_a} S_{a,M,N_a}\mathcal P_{M,N_a}}^{\,L^2(-a,a)}.
```

```tex
\textbf{H2b.}\qquad
L^2(-a,a)=V_a^{\mathrm{tail}}\oplus A_a^{\mathrm{cap}},
```

with `q_{G,a}`-orthogonality:

```tex
\langle G_g[a]v,w\rangle_{L^2(-a,a)}=0
\qquad
(v\in V_a^{\mathrm{tail}},\ w\in A_a^{\mathrm{cap}}).
```

and finite-dimensional cap control:

```tex
\textbf{H2c.}\qquad
A_a^{\mathrm{cap}}
=
\operatorname{span}\{u_n[a]-v_n[a]: |n|\le N_a+1\},
```

with the restriction of `q_{G,a}` on `A_a^{\mathrm{cap}}` represented by a
finite Hermitian matrix `H_a^{\mathrm{cap}}`.

## Why this is next

`H1^f` no longer asks what the defect is.
It now hands `H2^f` a rigid interface.

So `H2^f` is exactly the step that should turn:

```text
clean filtered block package
```

into:

```text
closed tail space + finite-dimensional cap complement.
```

Without `H2^f`, the route still has no honest bridge from the filtered block
theorem to Suzuki's tail/annihilator geometry.

## Best existing support

### 1. `Main_closure.tex` already contains the right theorem shell

`full/sections/Main_closure.tex` already freezes the theorem label
`\label{thm:H2-filtered-cap}` with exactly the right ingredients:

- closed tail space `V_a^{\mathrm{tail}}`;
- finite-dimensional complement `A_a^{\mathrm{cap}}`;
- `q_{G,a}`-orthogonality;
- annihilator-vector spanning set;
- finite Hermitian cap matrix `H_a^{\mathrm{cap}}`.

So `H2^f` is not a fresh guess. It is an already named upper bridge gate.

### 2. The `H1 -> H2` interface is already frozen

`docs/insights/h1_proof_obligation_table_2026_03_16.md` already says `H2^f`
should be allowed to read only:

- exact or cap-only cross-sign adapter;
- same-sign boundary term `H_a^{\mathrm{ss}}`;
- finite cap term `C_a^{\mathrm{cap}}`;
- no extra independent compression defect.

That is exactly the package we now have after `P7`.

### 3. Suzuki geometry already supports the tail/cap language

The external conceptual support remains the same:

- Suzuki already gives the tail/annihilator geometry;
- our task is not to invent new cap data, but to identify the right filtered
  tail space and finite cap complement in the cleaned `H1` language.

## Refined source map (2026-03-19)

The 2026-03-19 research refresh makes the `H2` support stack more exact.

### 1. `Main_closure.tex` gives the theorem shell

The frozen theorem shell in `full/sections/Main_closure.tex` is the best
receiver we currently have for `H2^f`.

### 2. The proof-obligation table gives the exact handoff contract

`docs/insights/h1_proof_obligation_table_2026_03_16.md` tells us exactly what
`H2^f` is allowed to consume and what it must not consume.

### 3. The old H1 notes already demoted everything except cap

`docs/insights/h1_raw_entry_reduction_2026_03_08.md`,
`docs/insights/h1_filtered_finite_section_2026_03_08.md`, and
`docs/insights/h1_four_block_bulk_2026_03_08.md` all say the same thing:

- after the filtered block theorem, the only other live H-bridge problem is
  the finite-dimensional Suzuki cap.

So `H2^f` really is the next honest gate.

### 4. The macro map already says the same thing operationally

`docs/insights/h_bridge_three_doors_macro_map_2026_03_16.md` compresses the
entire local route into:

```tex
(+,-)\checkmark
\to
(++)=H^{\mathrm{ss}}+C^{\mathrm{cap}}
\to
\text{compression neutrality}
\to
H2^f\to H3^f\to H4^f.
```

So once `P7` lands, the first upper-bridge gate is exactly `H2^f`, not a
return to any earlier local classification.

## Proof-facing packet

### H2.1. Tail-space definition

Primary first line:

```tex
V_a^{\mathrm{tail}}
:=
\overline{\bigcup_{M>N_a} S_{a,M,N_a}\mathcal P_{M,N_a}}^{\,L^2(-a,a)}.
```

This should be treated as the stabilized infinite filtered tail space coming
out of `H1^f`.

### H2.2. Tail/cap orthogonal split

Primary structural split:

```tex
L^2(-a,a)=V_a^{\mathrm{tail}}\oplus A_a^{\mathrm{cap}},
```

with `q_{G,a}`-orthogonality between the two pieces.

### H2.3. Finite cap representation

The cap piece must remain finite-dimensional and explicit:

```tex
A_a^{\mathrm{cap}}
=
\operatorname{span}\{u_n[a]-v_n[a]: |n|\le N_a+1\},
```

with a finite Hermitian matrix `H_a^{\mathrm{cap}}` representing the
restricted form.

### H2.4. Exact `H1 -> H2` input package

At theorem level `H2^f` should consume only:

- exact-or-cap-only cross-sign adapter;
- same-sign boundary term `H_a^{\mathrm{ss}}`;
- finite cap term `C_a^{\mathrm{cap}}`;
- no extra independent compression defect.

This should be treated as a rigid interface, not as soft guidance.

## Reusable theorem packet

The reusable `H2` packet is now:

1. `H2a`:
   ```tex
   V_a^{\mathrm{tail}}
   :=
   \overline{\bigcup_{M>N_a} S_{a,M,N_a}\mathcal P_{M,N_a}}^{\,L^2(-a,a)}.
   ```
2. `H2b`:
   ```tex
   L^2(-a,a)=V_a^{\mathrm{tail}}\oplus A_a^{\mathrm{cap}},
   ```
   with `q_{G,a}`-orthogonality.
3. `H2c`:
   ```tex
   A_a^{\mathrm{cap}}
   =
   \operatorname{span}\{u_n[a]-v_n[a]: |n|\le N_a+1\},
   ```
   with finite Hermitian cap matrix `H_a^{\mathrm{cap}}`.

## Route-kill condition

`H2^f` is in serious trouble if:

- the tail space is not actually closed/stable as the filtered union;
- the complement is not finite-dimensional;
- the complement is not orthogonal in the `q_{G,a}` sense;
- or the cap piece cannot be represented by explicit finite-dimensional data.

Operationally:

```text
if H2 cannot isolate a closed tail space plus finite-dimensional cap
complement, the upper Suzuki bridge stops being a theorem route and reverts to
an unnamed geometric cloud.
```

More explicitly, the bad forms are:

```tex
L^2(-a,a)=V_a^{\mathrm{tail}}\oplus \mathcal R_a,
\qquad
\dim \mathcal R_a=\infty,
```

or

```tex
\langle G_g[a]v,w\rangle \neq 0
\quad
\text{for some }
v\in V_a^{\mathrm{tail}},\ w\in A_a^{\mathrm{cap}}.
```

## What `H2` must not do

- no reopening of `H1` defect classification;
- no reopening of compression neutrality;
- no new basis/rank language;
- no jump to `H3` before the tail/cap split is frozen.

## Handoff after `H2`

If `H2^f` lands, the next honest move is:

```tex
H3^f:\ \text{filtered gap transfer}.
```

At that point the route should already have:

- stabilized tail space;
- finite cap complement;
- finite Hermitian cap matrix.

## Success criterion

This note lands only if the next theorem attempt is no longer
“what exactly is the cap geometry?”, but a clean `H3^f` gap-transfer problem
on the generalized Suzuki form pair.
