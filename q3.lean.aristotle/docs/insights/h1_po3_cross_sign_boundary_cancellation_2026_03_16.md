# `PO3` cross-sign boundary cancellation (2026-03-16)

## Status

Direct successor to `P2` in lane `A`.

`P2` already froze the right cross-sign posture:

- primary lemma:
  `\mathcal D_{a,\mathrm{bulk}}^{+-}=0`;
- admissible fallback:
  `\mathcal D_{a,N}^{+-}
   =\mathcal D_{a,\partial}^{+-}+\mathcal D_{a,\mathrm{cap}}^{+-}`;
- route-kill:
  any residual outside named boundary/cap channels.

So `P3` is now very sharp:

```tex
\text{kill the cross-sign boundary channel.}
```

## Mandatory research synthesis

The required research pass for this blocker points in one direction rather than
opening a new branch.

1. Local oracle recall again pulls the route back to `Main_closure.tex`: the
   old filtered classifier still records `M^{+-}(a)` as the calibration block
   and explicitly says that no extra section-boundary defect should survive
   once `\widetilde Q_{M,N}` is used correctly.
2. The frozen `h1_four_block_bulk_2026_03_08.md` note says the same thing in
   operator language: filtered bulk is exact first, and section-boundary
   bookkeeping is not allowed to leak back in at the bulk stage.
3. The Day-2 `(+,-)` cancellation ledger already singled out
   `\mathcal D_{a,\partial}^{+-}=0` as the strongest structural guess, with
   cap-only as the only admissible corrected fallback.
4. The worker contract for `P3` therefore should not ask for a new
   classification tree; it should ask for one exact boundary-cancellation lemma
   and one cap-only corollary.
5. External sanity-check material on Toeplitz/Hankel finite sections supports
   exactly this style of theorem packaging: boundary, commutator, and cap
   corrections are natural operator channels, while basis-hunt language is not
   a theorem shape.

So the honest `P3` plan is now:

- attack one exact boundary-cancellation lemma;
- allow only cap-only survival on the `(+,-)` side;
- treat any non-cap cross-sign boundary residue as a route-kill or
  near-route-kill event.

## Refined source map (2026-03-18)

The 2026-03-18 research refresh makes the `P3` support stack more exact.

### 1. `Main_closure.tex` still gives the primary filtered receiver

The main manuscript still points to the same mixed-block calibration story:

- `full/sections/Main_closure.tex` — `eq:H1-filtered-bulk-plus-minus`
- `full/sections/Main_closure.tex` — `prop:H1-raw-entry-reduction`
- `full/sections/Main_closure.tex` — `prop:H1-filtered-q-blocks`
- `full/sections/Main_closure.tex` — `cor:H1-bulk-symmetry-reduction`

Operational reading:

- `(+,-)` is still the filtered calibration block;
- once `\widetilde Q_{M,N}` is used correctly, no extra section-boundary
  defect should survive as theorem content;
- any leftover mixed-block channel therefore has to be cap-only or route-kill.

### 2. The reviewed H1 skeleton confirms the theorem map

`docs/reviewed_notes/2026_03_08_h1_theorem_skeleton_review.md` keeps the same
order:

- raw entry reduction first;
- filtered consequence second;
- finite cap last.

That is exactly the `P2 -> P3 -> cap-only fork` posture, not a return to a
free-floating remainder classifier.

### 3. The old four-block note still survives as consequence-layer support

`docs/insights/h1_four_block_bulk_2026_03_08.md` remains useful in one narrow
sense:

- it still freezes the filtered consequence language for `(+,+)`, `(+,-)`,
  `(-,+)`, `(-,-)`;
- it still says that no extra section-boundary bookkeeping belongs inside the
  filtered mixed block once `\widetilde Q_{M,N}` is the comparison object.

So the old four-block note is not the active frontier, but it still supports
`PO3a`.

### 4. External sanity-check keeps supporting asymmetry, not symmetry

The external foundation stack now reads cleanly:

- paired-operator language supports the special status of the mixed block;
- Toeplitz/Hankel operator language supports same-sign boundary/commutator
  residue as the natural surviving channel;
- nothing in that stack argues for a genuinely new mixed-block boundary term.

So `P3` still points in one direction:

```tex
\mathcal D_{a,\partial}^{+-}=0
\quad\text{or at worst}\quad
\mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}.
```

## Exact target

The primary `PO3` statement should be

```tex
\textbf{PO3a.}\qquad \mathcal D_{a,\partial}^{+-}=0.
```

Equivalent theorem fork:

```tex
\textbf{PO3b.}\qquad \mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}.
```

Preferred stronger version:

```tex
\mathcal D_{a,\mathrm{cap}}^{+-}=0,
```

but `PO3` itself should not require that stronger statement.

## Why this is next

Without `PO3`, the cross-sign side still carries a named dynamic correction,
and then the asymmetry of the whole route remains incomplete.

The intended asymmetry is:

- `(+,-)` should collapse to exactness or cap-only;
- `(++)` is the only place where a same-sign boundary operator may survive.

So `PO3` is the gate that stops the same-sign boundary story from leaking into
the calibration block.

## Best existing support

### 1. Day-2 cancellation ledger already said this

The cross-sign cancellation ledger fixed the strong expectation

```tex
\mathcal D_{a,\partial}^{+-}=0.
```

So `P3` is not a new speculation. It is the formalization of the strongest
already-frozen asymmetric guess.

### 2. Worker-ingested `P2` sharpened the handoff

The worker report made the handoff explicit:

- `P2` kills bulk;
- `P3` kills boundary;
- leftover, if any, is cap-only.

That is exactly the receiver this note should preserve.

### 3. Numerical story still points the same way

The whole moving-boundary / prefix-holdout pathology concentrates in `(++)`,
not in `(+,-)`.

So any surviving cross-sign boundary term is already suspicious and should be
treated as a near-route-kill, not as a routine weakened theorem.

### 4. Macro place of `P3`

`P3` is not an isolated micro-lemma anymore.
It is the boundary half of Door 1 in the compressed route

```tex
\text{Door 1} \to \text{Door 2} \to \text{Door 3} \to H2^f \to H3^f \to H4^f.
```

That is good news: if `P3` lands, Door 1 is very close to closure, and the
whole route becomes visibly asymmetric in the intended way.

## Proof-facing packet

### PO3.1. Boundary cancellation lemma

The narrowest local theorem target is

```tex
\mathcal D_{a,\partial}^{+-}=0.
```

This should be attacked directly, not through new basis language and not
through finite-section numerics.

### PO3.2. Cap-only corollary

If `PO3.1` lands, then the cross-sign tail block reduces to

```tex
\mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}.
```

This is the correct pre-`PO5` endpoint for the `(+,-)` side.

### PO3.3. Final `(+,-)` theorem fork

After `PO3`, the acceptable `(+,-)` theorem outputs are only:

1. exact cross-sign identity;
2. cap-only corrected cross-sign identity.

Nothing else should survive.

### PO3.4. Symmetry handoff

If `PO3a` lands on `(+,-)`, the `(-,+)` block should not become a new theorem
problem.

The expected handoff is:

```tex
\mathcal D_{a,\partial}^{-+}=0
```

by conjugation / self-adjoint symmetry, so the cross-sign side closes as one
package rather than two unrelated lemmas.

## Reusable lemma list

The reusable `P3` packet is now:

1. `PO3a`:
   ```tex
   \mathcal D_{a,\partial}^{+-}=0.
   ```
2. `PO3b`:
   ```tex
   \mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}.
   ```
3. `PO3c`:
   ```tex
   \mathcal D_{a,\partial}^{-+}=0
   ```
   by symmetry once `PO3a` is in place.

## Route-kill condition

The current reset is effectively dead if `PO3` leaves

```tex
\mathcal D_{a,\partial}^{+-}\neq 0
```

as a genuinely non-cap cross-sign boundary term.

Operationally:

```text
any surviving non-cap cross-sign boundary residue is a route-kill or near-route-kill.
```

The reason for “near-route-kill” wording is just caution about wording
discipline; mathematically the intended route no longer wants such a term.

## What `PO3` must not do

- no same-sign `(++)` theorem work;
- no compression bookkeeping;
- no augmented-cap positivity;
- no weakening back into “some structured cross-sign correction”.

## Handoff after `PO3`

If `PO3` lands, the cross-sign branch is essentially done. The next honest
steps are then:

1. `PO4`: identify the same-sign boundary term `H_a^{\mathrm{ss}}`;
2. `PO5`: separate the finite cap term `C_a^{\mathrm{cap}}`;
3. `PO6`: descend to finite filtered sections with no extra mystery channel.

## Success criterion

This note lands only if the next theorem attempt can be written as:

- one exact boundary-cancellation lemma for `\mathcal D_{a,\partial}^{+-}`;
- one cap-only corollary for the final `(+,-)` side.
