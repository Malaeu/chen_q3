# `PO3` cross-sign boundary cancellation (2026-03-16)

## Status

Direct successor to `P2` in lane `A`.

Operationally closed on 2026-03-18 as the Door-1 boundary gate.
This note remains the source artifact for why the mixed block is now treated as
bulk-exact, boundary-cancelled, and cap-only at worst.

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

## Exact proof packet after the 2026-04-11 audit

The audit closes one ambiguity cleanly: the missing brick is not an undefined
"mixed boundary miracle", but one exact boundary-algebra membership lemma.

### Frozen source stack

The minimal stack is now:

1. `full/sections/Main_closure.tex` — `prop:H1-raw-entry-reduction`;
2. `full/sections/Main_closure.tex` — `prop:H1-filtered-q-blocks`;
3. `docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md` — `L3'`
   explicit filtered residual formula;
4. `docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md` —
   `L3'''''` sign-pure boundary lemma;
5. `docs/insights/h1_boundary_cap_reset_2026_03_14.md` — the structural split
   `\mathcal D_{a,N}=H_{a,N}+C_{a,N}`.

These are enough to freeze the real theorem receiver.

### Exact receiver

From `PO2` we already have the mixed filtered residual in exact four-term form:

```tex
R_{mn}^{+-}(a)
=
\delta_{m,-n}(a)
+ \delta_{m+1,-n}(a)
+ \delta_{m,-(n+1)}(a)
+ \delta_{m+1,-(n+1)}(a),
```

with `\delta_{r,s}(a)=w_{r,s}(a)-\kappa(a)q_{r,s}`.

So `PO3a` is no longer a vague cancellation wish. It reduces to proving that
the boundary part of the infinite-tail defect is sign-pure.

### Exact missing lemma

The next theorem attempt should now be stated as:

```tex
\textbf{PO3a-formula.}\qquad
H_{a,N}\in\mathcal B,
```

where `\mathcal B` is the boundary algebra generated by
`P_+`, `P_-`, `\Delta_+`, `\Delta_-`, and tail operators acting only on the
positive or only on the negative side.

Then the sign-pure boundary lemma gives immediately

```tex
P_+H_{a,N}P_-=0,
```

hence

```tex
\mathcal D_{a,\partial}^{+-}=0.
```

So the actual `PO3a` chain is now frozen as:

```tex
H_{a,N}\in\mathcal B
\Longrightarrow
P_+H_{a,N}P_-=0
\Longrightarrow
\mathcal D_{a,\partial}^{+-}=0
\Longrightarrow
\mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}.
```

### What is still missing mathematically

The current stack does **not** yet prove the membership
`H_{a,N}\in\mathcal B`.

That is the honest live blocker.
In other words:

- we already know what the cancellation mechanism would be;
- we do **not** yet have the explicit mixed-boundary formula that places the
  boundary operator inside the sign-pure algebra.

### Route-kill criterion

The route is no longer killed by "any nonzero mixed residue".
It is killed by the sharper event:

```tex
\text{the explicit boundary formula for }H_{a,N}
\text{ requires a genuine cross-sign generator outside }\mathcal B.
```

Equivalently, if after isolating the boundary layer one is forced to keep a
term with nonzero `P_+(\cdot)P_-` that is not finite cap, then `PO3a` fails in
the intended Door-1 sense.

### Control consequence

The proof-packet audit is therefore complete.
The next honest local task is not another search, but a direct attack on
`PO3a-formula`: derive an explicit formula for `H_{a,N}` and prove that every
boundary generator is sign-pure.

## Proof skeleton for the live `PO3a` attack

The next proof attempt should now be written as a rigid five-step packet rather
than a generic "boundary cancellation" search.

### `PO3a.1` Bulk-boundary decomposition

Construct a decomposition

```tex
S_{a,\infty,N}=U_{a,N}+B_{a,N},
```

where `U_{a,N}` is the bulk piece already matched by
`\kappa(a)\Delta_N^*Q_\infty\Delta_N`, and `B_{a,N}` is the genuine boundary
correction.

The intended identity is

```tex
U_{a,N}^*G_g[a]U_{a,N}
=
\kappa(a)\Delta_N^*Q_\infty\Delta_N.
```

Then

```tex
H_{a,N}
=
B_{a,N}^*G_g[a]B_{a,N}
+ U_{a,N}^*G_g[a]B_{a,N}
+ B_{a,N}^*G_g[a]U_{a,N}.
```

So the boundary layer is generated entirely by the correction `B_{a,N}`.

There is now also one exact algebraic starting identity behind this step.
Define the raw sign-pure synthesis `T_{a,\infty,N}` on the algebraic tail basis
by

```tex
T_{a,\infty,N} z^n=\chi_n[a],
\qquad
T_{a,\infty,N} z^{-n}=\chi_{-n}[a]
\qquad (n>N).
```

Then the already frozen `PO1` / `Main_closure` formulas give on basis vectors

```tex
I_0^{(a)}S_{a,\infty,N} z^n=\chi_n[a]+\chi_{n+1}[a],
\qquad
I_0^{(a)}S_{a,\infty,N} z^{-n}=\chi_{-n}[a]+\chi_{-(n+1)}[a],
```

while

```tex
\Delta_N z^n=z^n+z^{n+1},
\qquad
\Delta_N z^{-n}=z^{-n}+z^{-(n+1)}.
```

So one has the exact tail-level factorization

```tex
I_0^{(a)}S_{a,\infty,N}=T_{a,\infty,N}\Delta_N.
```

This is the right entry point for `PO3a.1`: the sign geometry is already
clean at the antiderivative level, so any boundary term must appear only when
passing back from the Volterra-antiderivative side to the actual defect
operator. In particular, the live source of `H_{a,N}` is no longer "some
mixed tail combinatorics", but the Volterra undoing of the raw sign-pure
filtered synthesis.

### `PO3a.2` Boundary expansion

Expand the boundary correction in finite sign-pure form:

```tex
B_{a,N}
=
\sum_r |b_{r,+}\rangle\langle \eta_{r,+}|
+ \sum_s |b_{s,-}\rangle\langle \eta_{s,-}|,
```

with every `b_{r,+}` supported in the positive tail channel and every
`b_{s,-}` supported in the negative tail channel.

This is the first genuinely nontrivial local brick: the route needs an
explicit boundary expansion, not merely the abstract split
`\mathcal D_{a,N}=H_{a,N}+C_{a,N}`.

### `PO3a.3` Kernel sign-preservation on boundary generators

Show that the kernel action preserves the sign purity of the boundary
generators:

```tex
G_g[a]\,b_{r,+}\in \mathcal G_+,
\qquad
G_g[a]\,b_{s,-}\in \mathcal G_-,
```

for the corresponding sign-pure generator families `\mathcal G_\pm`.

This is the real cancellation mechanism behind `PO3a`: once the surviving
boundary generators never cross signs, the mixed block cannot be produced by
the boundary layer.

### `PO3a.4` Boundary algebra membership

From `PO3a.2` and `PO3a.3`, conclude

```tex
H_{a,N}\in\mathcal B.
```

This is the exact missing lemma frozen above as `PO3a-formula`.

### `PO3a.5` Mixed block dies

Apply the sign-pure boundary lemma:

```tex
P_+H_{a,N}P_-=0.
```

Hence

```tex
\mathcal D_{a,\partial}^{+-}=0,
```

and therefore

```tex
\mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}.
```

## Honest difficulty map

The route is now narrow enough that the difficulty split should be frozen
explicitly:

- `PO3a.5` is already formal once `H_{a,N}\in\mathcal B` is available;
- `PO3a.4` is a closure step, not the real obstacle;
- the genuine hard bricks are `PO3a.2` and `PO3a.3`:
  explicit boundary expansion and sign-preservation on the surviving boundary
  generators.

So the next local attack should focus there, not on the final mixed-block
implication.
