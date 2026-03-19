# `PO5` cap separation (2026-03-19)

## Status

Direct successor to `P4` in lane `A`.

Operationally closed on 2026-03-19 as the second Door-2 gate.
This note remains the source artifact for why the same-sign receiver is now
treated as a clean boundary-plus-cap theorem package.

`P4` already froze the same-sign survivor as a named operator object:

```tex
\mathcal D_{a,\partial}^{++}=H_a^{\mathrm{ss}}.
```

So Door 2 now narrows to one honest next question:

```tex
\text{can the remaining cap channel be isolated cleanly?}
```

## Exact target

The narrowest `P5` statement should be:

```tex
\textbf{PO5a.}\qquad \mathcal D_{a,\mathrm{cap}}^{++}=C_a^{\mathrm{cap}}.
```

This is not augmented-cap positivity yet.
It is only cap identification and separation.

Notation freeze for the current direct phase:

```tex
C_a^{\mathrm{cap}}
```

is the canonical theorem symbol.
If some underlying construction still depends on cutoff data or annihilator
choice, that dependence may live inside the definition, but the theorem
receiver should not float between ad hoc notations.

## Exact post-`PO5` split

If `P5` lands, the same-sign receiver should become:

```tex
\mathcal D_{a,N}^{++}
=
H_a^{\mathrm{ss}}
+ C_a^{\mathrm{cap}}.
```

That is the preferred Door-2 endpoint:

- named same-sign boundary operator;
- explicit finite cap term;
- no third independent theorem channel.

## Why this is next

After `P4`, the route no longer needs to ask what the same-sign survivor is.
It needs to ask whether the remaining finite part is genuinely cap and can be
separated from the boundary operator.

So `P5` is the exact gate that turns Door 2 from

```text
boundary object named
```

into

```text
boundary object + explicit cap object.
```

Without `P5`, the route still carries a mixed remainder cloud inside `(++)`.

## Refined source map (2026-03-19)

The 2026-03-19 research refresh makes the `P5` support stack more exact.

### 1. The filtered finite-section note already names the right fallback shape

`docs/insights/h1_filtered_finite_section_2026_03_08.md` already says the
preferred filtered bridge should read:

```tex
S_{a,M}^* G_g[a] S_{a,M}
=
\kappa(a)\widetilde Q_M + F_{a,M},
```

where `F_{a,M}` is zero or an explicit finite-rank Suzuki cap.

Operational reading:

- the surviving finite piece is supposed to be cap-shaped, not a generic
  remainder cloud;
- `P5` is exactly the step that upgrades that fallback wording into a named
  theorem object.

### 2. The raw-entry reduction note already isolates cap as the only live post-bulk brick

`docs/insights/h1_raw_entry_reduction_2026_03_08.md` says the same thing in a
more direct bridge language:

- filtered bulk first;
- then only the finite-dimensional Suzuki cap remains.

This is strong support for treating `P5` as cap identification, not as a new
classification search.

### 3. The old four-block note still points to cap as the only live finite channel

`docs/insights/h1_four_block_bulk_2026_03_08.md` again records that after the
four filtered blocks are matched, the only other live H-bridge problem is the
finite-dimensional Suzuki cap.

So three independent local notes are already aligned:

- filtered finite section;
- raw-entry reduction;
- four-block consequence layer.

### 4. External support is conceptual, not ready-made

The external support stack still helps with language, but not with a turnkey
theorem:

- Suzuki geometry supports cap as finite-dimensional tail/annihilator data;
- classical operator language supports the separation of same-sign boundary
  from the finite cap piece;
- the web sanity-check does not hand us our exact split theorem.

So `P5` remains our theorem to package, but it is well supported as the right
next gate.

## Best existing support

### 1. Same-sign inventory already froze the cap target

`docs/insights/plus_plus_boundary_inventory_2026_03_15.md` already records the
right second same-sign lemma:

```tex
\mathcal D_{a,\mathrm{cap}}^{++}=C_a^{\mathrm{cap}}.
```

That is still the cleanest supporting inventory for `P5`.

### 2. The proof-obligation table already places `PO5` here

`docs/insights/h1_proof_obligation_table_2026_03_16.md` freezes `PO5` exactly
as cap separation after `PO4`.

So `P5` is not a new branch and not a new theorem language. It is the
already-frozen next gate after same-sign boundary identification.

### 3. External foundation stack supports cap as Suzuki geometry

The supporting external picture remains:

- same-sign boundary is operator-theoretic;
- cap is finite-dimensional Suzuki tail/annihilator geometry;
- these two must be separated before compression or positivity work resumes.

### 4. No stronger external theorem was found

The external sanity-check for this blocker did not produce a ready-made theorem
that directly proves our exact cap split in the current `Q_\zeta` language.

That is useful in itself:

- it means we are not overlooking an obvious literature shortcut;
- it also means the correct move is to sharpen the local theorem receiver,
  not to reopen the route.

## Proof-facing packet

### PO5.1. Cap identification

Primary theorem target:

```tex
\mathcal D_{a,\mathrm{cap}}^{++}=C_a^{\mathrm{cap}}.
```

`C_a^{\mathrm{cap}}` must be an explicit finite-dimensional cap object, not a
floating fit term.

At theorem level this should be read as:

- finite-dimensional;
- stable as cap data;
- not merely “whatever remains after subtraction”.

### PO5.2. Boundary/cap separation statement

The receiver should make explicit that:

- `H_a^{\mathrm{ss}}` is the same-sign boundary object;
- `C_a^{\mathrm{cap}}` is the finite cap object;
- neither term is allowed to masquerade as the other.

## Reusable theorem packet

The reusable `P5` packet is now:

1. `PO5a`:
   ```tex
   \mathcal D_{a,\mathrm{cap}}^{++}=C_a^{\mathrm{cap}}.
   ```
2. `PO5b`:
   ```tex
   \mathcal D_{a,N}^{++}=H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}.
   ```
3. `PO5c`:
   there is no third independent theorem channel beyond
   `H_a^{\mathrm{ss}}` and `C_a^{\mathrm{cap}}`.

### PO5.3. No third channel

The same-sign theorem remains viable only if there is no extra theorem-shaped
channel beyond:

```tex
H_a^{\mathrm{ss}}
\quad\text{and}\quad
C_a^{\mathrm{cap}}.
```

## Route-kill condition

Door 2 is in serious trouble if the cap part:

- drifts with `M` like a floating fit artifact;
- cannot be separated from `H_a^{\mathrm{ss}}`;
- or produces a third independent residual channel.

Operationally:

```text
if cap cannot be isolated as explicit finite-dimensional data, Door 2 loses its
clean boundary/cap theorem shape.
```

More explicitly, the bad forms are:

```tex
\mathcal D_{a,N}^{++}
=
H_a^{\mathrm{ss}}+\mathcal R_{a,N}^{\mathrm{fin}},
\qquad
\mathcal R_{a,N}^{\mathrm{fin}}
\not\equiv
C_a^{\mathrm{cap}},
```

or

```tex
\mathcal D_{a,N}^{++}
=
H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}+\mathcal T_{a,N},
\qquad
\mathcal T_{a,N}\neq 0,
```

with `\mathcal T_{a,N}` acting as a third theorem-shaped channel.

## What `P5` must not do

- no reopening of the same-sign boundary identification;
- no compression bookkeeping yet;
- no augmented-cap positivity yet;
- no new basis/rank language as theorem content.

## Handoff after `P5`

If `P5` lands, the next honest step is:

```tex
\textbf{PO6.}\qquad
E_{a,\mathrm{comp}}^{+-}=0,
\qquad
E_{a,\mathrm{comp}}^{++}=0
```

or fully explicit bookkeeping that is not promoted to theorem content.

## Success criterion

This note lands only if the next theorem attempt can be written as:

- one cap-identification lemma for `\mathcal D_{a,\mathrm{cap}}^{++}`;
- one explicit boundary/cap separation statement;
- one clean handoff to `PO6`.
