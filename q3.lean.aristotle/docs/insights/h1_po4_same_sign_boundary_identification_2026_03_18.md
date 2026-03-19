# `PO4` same-sign boundary identification (2026-03-18)

## Status

Direct successor to `P3` in lane `A`.

Operationally closed on 2026-03-19 as the first Door-2 gate.
This note remains the source artifact for why the same-sign survivor is now
treated as a named operator object `H_a^{\mathrm{ss}}`.

`P3` already froze the right mixed-block asymmetry:

- `(+,-)` bulk is exact;
- cross-sign boundary is required to cancel;
- only a cap-only fallback remains admissible on the mixed side.

So Door 1 is now closed tightly enough for the route to spend theorem energy on
Door 2.

## Exact target

The narrowest `P4` statement should be:

```tex
\textbf{PO4a.}\qquad \mathcal D_{a,\partial}^{++}=H_a^{\mathrm{ss}}.
```

Here `H_a^{\mathrm{ss}}` must be a named operator, not a numerical residual and
not a floating matrix-fit remainder.

Notation freeze for the current direct phase:

```tex
H_a^{\mathrm{ss}}
```

is the canonical theorem symbol.
If some underlying construction still carries cutoff dependence, that may live
inside the definition, but the theorem receiver should not let the notation
float between `H_a^{\mathrm{ss}}` and `H_{a,N}^{\mathrm{ss}}`.

Admissible theorem language:

- Toeplitz-Hankel residue;
- commutator with the cutoff / filtered shift;
- short-range near-edge boundary term.

Non-admissible theorem language:

- “some good rank-`r` basis”;
- unnamed moving residue;
- same-sign correction with no operator source.

## Why this is next

After `P3`, the asymmetry is finally honest:

- `(+,-)` is calibration;
- `(++)` is the only place where a real surviving boundary term may live.

So `P4` is the first Door-2 gate:

```tex
\text{identify the same-sign survivor as a real operator object.}
```

Without this step, the route is still mathematically verbal: we would be
saying that `(++)` is hard, but not yet saying what it actually is.

## Best existing support

### 1. The old same-sign inventory already froze the right receiver

`docs/insights/plus_plus_boundary_inventory_2026_03_15.md` already contains the
correct target:

```tex
\mathcal D_{a,\partial}^{++}=H_a^{\mathrm{ss}}.
```

That note is no longer the active phase artifact, but it remains the main
supporting inventory for `P4`.

### 2. The proof-obligation table already places this as the next gate

`docs/insights/h1_proof_obligation_table_2026_03_16.md` freezes `PO4` exactly
as same-sign boundary identification, followed by `PO5` cap separation.

So `P4` is not a new branch; it is the already-frozen next theorem gate after
the mixed block closes.

### 3. External operator language still supports the same-sign picture

The external foundation stack remains aligned with the route:

- paired-operator language supports the special mixed-block status;
- Toeplitz/Hankel language supports a same-sign boundary or commutator
  survivor;
- nothing in that support stack asks us to reopen mixed-block ambiguity.

### 4. Worker-ingested `P4` report sharpens the receiver

The active worker report adds one useful tightening:

- `PO4` should name the boundary object and stop there;
- the clean post-`PO4` split should be
  `\mathcal D_{a,N}^{++}=H_a^{\mathrm{ss}}+\mathcal D_{a,\mathrm{cap}}^{++}`;
- cap separation belongs entirely to `PO5`;
- the real Door-2 kill gate is not merely nonzero residue, but residue that
  remains unnamed as an operator source.

## Proof-facing packet

### PO4.1. Same-sign boundary identification

Primary theorem target:

```tex
\mathcal D_{a,\partial}^{++}=H_a^{\mathrm{ss}}.
```

This should be attacked as an operator identification problem, not as a small
residual classification problem.

### PO4.2. Admissible operator forms

The current acceptable shapes for `H_a^{\mathrm{ss}}` are:

1. Toeplitz-Hankel correction;
2. explicit commutator term;
3. short-range near-edge boundary operator.

The route does not currently need to choose among these three in advance, but
it must land on one named operator channel.

## Exact post-`PO4` split

The cleanest post-`PO4` receiver is now frozen as:

```tex
\mathcal D_{a,N}^{++}
=
H_a^{\mathrm{ss}}
+ \mathcal D_{a,\mathrm{cap}}^{++}.
```

This is deliberately stronger than a vague “boundary plus something” package
and deliberately weaker than jumping early to
`H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}`.

Meaning:

- `PO4` names the same-sign boundary survivor;
- the only remaining unnamed channel is cap;
- bulk and compression stay out of the theorem receiver at this step.

## Admissible-source table

| Candidate source for `H_a^{\mathrm{ss}}` | Status at `PO4` | Meaning |
| --- | --- | --- |
| Toeplitz-Hankel residue | admissible | cleanest classical same-sign boundary mechanism |
| commutator with cutoff / filtered shift | admissible | keeps the survivor operator-theoretic |
| short-range near-edge boundary term | admissible | matches the observed Door-2 phenotype |
| unnamed moving matrix residual | route-kill | no theorem-grade operator content |
| rank/basis-fit explanation | route-kill | forbidden as theorem content |
| generic bulk mismatch | route-kill | contradicts the boundary/cap picture |

### PO4.3. Bulk exclusion contrast

The same-sign theorem remains clean only if:

```tex
\mathcal D_{a,\mathrm{bulk}}^{++}=0
```

stays the intended contrast. `P4` identifies the boundary object; it must not
quietly reintroduce a generic bulk mismatch.

## Route-kill condition

The current Door-2 picture is in serious trouble if `P4` leaves:

```tex
\mathcal D_{a,\partial}^{++}\neq 0
```

but cannot name the survivor as a real operator channel.

Operationally:

```text
an unnamed same-sign moving residue is a Door-2 route-kill or near-route-kill.
```

More explicitly, the bad form is:

```tex
\mathcal D_{a,N}^{++}
=
\mathcal R_{a,N}^{++}
+ \mathcal D_{a,\mathrm{cap}}^{++},
\qquad
\mathcal R_{a,N}^{++}\neq 0,
```

with `\mathcal R_{a,N}^{++}` not identifiable as Toeplitz-Hankel,
commutator, or near-edge boundary operator.

## What `P4` must not do

- no reopening of mixed-block `(+,-)` ambiguity;
- no cap separation yet;
- no compression bookkeeping;
- no augmented-cap positivity;
- no basis/rank language as theorem content.

## Handoff after `P4`

If `P4` lands, the next honest step is:

```tex
\textbf{PO5.}\qquad \mathcal D_{a,\mathrm{cap}}^{++}=C_a^{\mathrm{cap}},
```

with explicit separation between `H_a^{\mathrm{ss}}` and `C_a^{\mathrm{cap}}`.

## Success criterion

This note lands only if the next theorem attempt can be written as:

- one operator-identification lemma for `\mathcal D_{a,\partial}^{++}`;
- one explicit list of admissible operator sources for `H_a^{\mathrm{ss}}`;
- one clear handoff to `PO5` without reopening Door 1.
