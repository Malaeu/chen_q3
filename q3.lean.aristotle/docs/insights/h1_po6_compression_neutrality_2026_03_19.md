# `PO6` compression neutrality (2026-03-19)

## Status

Direct successor to `P5` in lane `A`.

Operationally closed on 2026-03-19 as the Door-3 gate.
This note remains the source artifact for why finite descent is now treated as
bookkeeping-only rather than as a new theorem channel.

`P5` already froze the same-sign theorem package as:

```tex
\mathcal D_{a,N}^{++}
=
H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}.
```

So Door 2 is now treated as tight enough, and the next honest question is:

```tex
\text{does finite compression create a new theorem-shaped obstruction?}
```

## Exact target

The narrowest `P6` statement should be:

```tex
\textbf{PO6a.}\qquad
E_{a,\mathrm{comp}}^{+-}=0,
\qquad
E_{a,\mathrm{comp}}^{++}=0,
```

or, if literal zero is too strong at first pass, a weaker but still acceptable
receiver:

```tex
\textbf{PO6a'.}\qquad
E_{a,\mathrm{comp}}^{\sigma\tau}
\text{ is fully explicit bookkeeping and not a new theorem channel.}
```

The packaging line to keep fixed is:

```tex
D_{a,M,N}
=
P_{M,N}\mathcal D_{a,N}P_{M,N}+\mathcal E_{a,M,N},
```

with `\mathcal E_{a,M,N}` read as compression bookkeeping only.

## Why this is next

After `P5`, the route no longer needs to ask what survives in `(++)`.
It needs to show that finite sections do not manufacture a new theorem-shaped
defect after the infinite-tail decomposition is already frozen.

So `P6` is the exact gate that turns:

```text
Door 2 theorem package obtained
```

into:

```text
finite descent adds no new mathematics.
```

Without `P6`, the route could still leak a fake “section-level mystery defect”
back into `H1^f`.

## Best existing support

### 1. The proof-obligation table already fixes `PO6`

`docs/insights/h1_proof_obligation_table_2026_03_16.md` already places `PO6`
exactly here and names the right receiver:

```tex
E_{a,\mathrm{comp}}^{+-}=0,
\qquad
E_{a,\mathrm{comp}}^{++}=0,
```

or explicit bookkeeping that is not promoted to theorem content.

### 2. The `P5` handoff is already clean

`docs/insights/h1_po5_cap_separation_2026_03_19.md` already ends with the
right next move:

- cap is separated;
- boundary is already named;
- compression is next and should stay bookkeeping-level.

### 3. The filtered finite-section route language already supports this

The filtered finite-section and raw-entry notes support the same route order:

- infinite-tail decomposition first;
- finite compression second;
- no new theorem-shaped channel introduced by sectioning.

## Refined source map (2026-03-19)

The 2026-03-19 research refresh makes the `P6` support stack more exact.

### 1. The filtered finite-section note already demotes the finite part

`docs/insights/h1_filtered_finite_section_2026_03_08.md` already packages the
filtered bridge as

```tex
S_{a,M}^* G_g[a] S_{a,M}
=
\kappa(a)\widetilde Q_M + F_{a,M},
```

with `F_{a,M}` zero or an explicit finite-rank Suzuki cap.

Operational reading:

- finite descent is not supposed to create a new bulk theorem;
- the only admissible finite survivor is explicit and section-level.

### 2. The raw-entry reduction note already fixes the theorem order

`docs/insights/h1_raw_entry_reduction_2026_03_08.md` again says:

- filtered bulk first;
- then only the finite-dimensional Suzuki cap remains;
- no return to raw mismatch language.

That is strong support for treating `P6` as compression bookkeeping rather
than as another classification gate.

### 3. The two-sided bridge note already freezes the metric/compression setup

`docs/insights/h1_two_sided_filtered_bridge_2026_03_08.md` already freezes the
exact metric side and the symmetric filtered finite object. This matters for
`P6` because finite descent should only compress an already-frozen infinite
object, not invent a new one.

### 4. External support is sanity-check only

The external sanity-check through finite sections of Toeplitz+Hankel operators
supports the same moral picture:

- section-level stability is its own layer;
- finite sections can fail in general if extra structure is missing;
- therefore our route must explicitly prove compression neutrality rather than
  assume it.

So `P6` remains our local theorem gate, but not a blind one.

## Proof-facing packet

### PO6.1. Compression neutrality statement

Primary theorem target:

```tex
E_{a,\mathrm{comp}}^{+-}=0,
\qquad
E_{a,\mathrm{comp}}^{++}=0.
```

This is the cleanest receiver because it forbids finite sections from
reopening either Door 1 or Door 2.

### PO6.2. Acceptable fallback

If strict zero is not yet the first receiver, the only admissible softer
statement is:

```tex
\mathcal E_{a,M,N}
\text{ is fully explicit compression bookkeeping.}
```

That still keeps compression out of theorem content.

### PO6.3. No new theorem channel

The route remains viable only if no new independent channel appears beyond:

```tex
H_a^{\mathrm{ss}}
\quad\text{and}\quad
C_a^{\mathrm{cap}}.
```

Compression is not allowed to create a third structural term.

## Reusable theorem packet

The reusable `P6` packet is now:

1. `PO6a`:
   ```tex
   E_{a,\mathrm{comp}}^{+-}=0,
   \qquad
   E_{a,\mathrm{comp}}^{++}=0.
   ```
2. `PO6b`:
   ```tex
   D_{a,M,N}
   =
   P_{M,N}\mathcal D_{a,N}P_{M,N}+\mathcal E_{a,M,N},
   ```
   with `\mathcal E_{a,M,N}` explicit bookkeeping only.
3. `PO6c`:
   there is no new theorem-shaped channel created by finite compression.

## Route-kill condition

Door 3 is in serious trouble if finite sections produce:

```tex
D_{a,M,N}
=
P_{M,N}\mathcal D_{a,N}P_{M,N}
+ \mathcal T_{a,M,N},
\qquad
\mathcal T_{a,M,N}\neq 0,
```

with `\mathcal T_{a,M,N}` not reducible to explicit bookkeeping.

Operationally:

```text
if compression creates a new theorem-shaped residue, H1^f loses its clean
descent package.
```

## What `P6` must not do

- no reopening of Door 1;
- no reopening of same-sign boundary identification;
- no reopening of cap separation;
- no augmented-cap positivity;
- no new basis/rank language.

## Handoff after `P6`

If `P6` lands, the next honest step is:

```tex
\textbf{PO7.}\qquad
\text{package the final filtered theorem for }H1^f.
```

At that point the local route should read:

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+E_{a,\mathrm{cap}}^{+-},
```

```tex
M^{++}(a)=\kappa_{+-}(a)\widetilde Q^{++}+H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}.
```

## Success criterion

This note lands only if the next theorem attempt can be written as:

- one compression-neutrality lemma;
- one bookkeeping-only fallback clause;
- one clean handoff to `PO7`.
