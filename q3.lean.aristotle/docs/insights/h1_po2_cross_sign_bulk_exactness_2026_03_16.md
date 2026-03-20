# `PO2` cross-sign bulk exactness (2026-03-16)

## Status

First post-`P1` direct theorem receiver in lane `A`.

Reactivated on 2026-03-20 as the first undischarged proof-critical gate on the
actual path to RH.

The upper bridge `H2^f -> H3^f -> H4^f` is now packaged tightly enough at the
theorem-shell level, but it is still conditional on the unresolved `H1^f`
input. So the honest blocker is no longer route description. It is whether the
cross-sign tail block is bulk-exact in the strong sense required by `PO2`.

`P1` already froze:

- the tail defect object `\mathcal D_{a,N}`;
- its sign-block split;
- Hermitian recovery of `(-+)`, `(--)`.

So the next honest question is narrower:

```tex
\text{does the cross-sign tail block carry any genuine bulk residue?}
```

## Why this is next

The whole asymmetry of the current route depends on one strong claim:

- `(+,-)` is the calibration block;
- `(++)` is where any same-sign boundary term should live.

That asymmetry does not become theorem-grade until the cross-sign block is
shown to be bulk-exact before any boundary/cap discussion.

## Exact target

The `PO2` receiver should be written in the following equivalent forms.

### PO2a. Bulk vanishing statement

```tex
\mathcal D_{a,\mathrm{bulk}}^{+-}=0.
```

### PO2b. Boundary/cap-only remainder statement

Equivalently,

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\partial}^{+-}
+ \mathcal D_{a,\mathrm{cap}}^{+-}.
```

This is the strongest acceptable `PO2` output before `PO3`.

It says:

- no genuine bulk mismatch survives in `(+,-)`;
- whatever remains must already belong to the later
  boundary/cap classification problem.

## Worker-ingested refinement

The first worker pass on `P2` confirmed the right asymmetry and sharpened one
important policy decision:

- the **primary** `PO2` lemma must stay pure:
  `\mathcal D_{a,\mathrm{bulk}}^{+-}=0`;
- the **fallback** form must already name both admissible remainder channels:
  boundary and cap;
- compression must stay out of `PO2` entirely and remain deferred to `PO6`.

So the correct theorem posture is:

```text
prove pure bulk vanishing in PO2;
name boundary/cap in the equivalent fallback;
do not let compression or same-sign language leak into this stage.
```

## Strongest existing anchors

### 1. Old strongest filtered thesis

`Main_closure.tex` already records the finite filtered receiver

```tex
M^{+-}(a)=\kappa(a)\widetilde Q_{M,N}^{+-}+F_a^{+-},
```

with the explicit remark:

```text
no extra section-boundary defect once \widetilde Q_{M,N} is used.
```

So `PO2` is not inventing a new theorem shape. It is isolating the bulk part
of the old strongest filtered thesis.

### 2. Exact four-block filtered bulk formulas already exist

The four-block note already freezes

```tex
M_{mn}^{\sigma\tau}(a)
=
W(\psi_n^\sigma[a]*\widetilde{\psi_m^\tau[a]}).
```

So the cross-sign bulk is not heuristic. It is already an exact filtered
operator expression.

### 3. Raw mismatch is not the issue here

The dead raw identity

```tex
w_{rs}(a)=\kappa(a)q_{rs}
```

does not obstruct `PO2`, because `PO2` is already formulated on the filtered
tail object `\mathcal D_{a,N}^{+-}`, not on the raw Toeplitz-vs-Weil entries.

## Research synthesis for this blocker

Local embedding search on `q3_docs` keeps returning the same four anchors:

- `h1_four_block_bulk_2026_03_08.md` as the exact filtered bulk formula layer;
- `Main_closure.tex` as the strongest older finite receiver for exact `(+,-)`;
- `h1_raw_entry_reduction_2026_03_08.md` as the place where raw mismatch is
  explicitly separated from the filtered target;
- `IMPLEMENTATION_PLAN.md` / `PROJECT_ORCHESTRATOR.md` as confirmation that
  the direct filtered bulk identities are still the live mathematical route.

External sanity-check from the finite-section / Toeplitz-Hankel side does not
push against this picture: the natural place for any non-bulk remainder is a
boundary/finite-section channel, not a mysterious floating bulk defect. So the
working `PO2` posture stays aggressive:

```tex
\text{either cross-sign bulk vanishes, or the current reset is wrong.}
```

## Proof-facing reduction

The note is only useful if it shrinks to a short local packet.

### PO2.1. Entrywise filtered bulk receiver

For `n,m>N`, freeze the cross-sign filtered entries as

```tex
M_{mn}^{+-}(a)
=
\left\langle G_g[a]\phi_n^+[a],\phi_m^-[a]\right\rangle
=
W(\psi_n^+[a]*\widetilde{\psi_m^-[a]}).
```

This is the exact Suzuki-side bulk object that must be compared to the
corresponding entries of `\kappa_{+-}(a)Q_\infty^{+-}`.

### PO2.2. Bulk exactness lemma

The first real theorem attempt inside `P2` should be the tail-level statement

```tex
\mathcal D_{a,\mathrm{bulk}}^{+-}=0.
```

Equivalent receiver:

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\partial}^{+-}
+ \mathcal D_{a,\mathrm{cap}}^{+-}.
```

That is the narrowest acceptable theorem output before `PO3`.

### PO2.3. Bulk route-kill lemma

Any statement of the form

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\mathrm{bulk}}^{+-}
+ \cdots,
\qquad
\mathcal D_{a,\mathrm{bulk}}^{+-}\neq 0,
```

with no operator reclassification into boundary or cap, is not a weakened win.
It is the explicit route-kill event for the current boundary/cap reset.

## Compact proof plan

The next real attack on `PO2` should stay brutally short.

### Step 1. Freeze the exact cross-sign tail object

Work only with

```tex
\mathcal D_{a,N}^{+-}
=
P_{+,N}\mathcal D_{a,N}P_{-,N},
```

not with finite-section diagnostics and not with the same-sign block.

### Step 2. Expand the filtered Suzuki side entrywise

Use only the exact filtered bulk formulas from the four-block note:

```tex
M_{mn}^{+-}(a)
=
\bigl\langle G_g[a]\phi_n^+[a],\phi_m^-[a]\bigr\rangle
=
W(\psi_n^+[a]*\widetilde{\psi_m^-[a]}).
```

So the left-hand side is already a genuine filtered bulk object.

### Step 3. Expand the Q3 side through the pulled-back block

Compare against

```tex
\kappa(a)\widetilde Q_{N}^{+-}
\quad\text{or finite shadows }\quad
\kappa(a)\widetilde Q_{M,N}^{+-},
```

using only the frozen two-sided filter `\Delta_N`.
The key point is that both sides must be read through the same four-term
stencil induced by the two-sided adjacent-packet filter.

### Step 4. Kill the common bulk stencil first

The first theorem attempt is not “classify all remainders”, but:

```tex
\mathcal D_{a,\mathrm{bulk}}^{+-}=0.
```

So the shared filtered stencil must cancel before any cap analysis.
If it does not, the route is not weakened; it is killed.

### Step 5. Name the only admissible remainder channels

After bulk cancellation, the only allowed output is

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\partial}^{+-}
\mathcal D_{a,\mathrm{cap}}^{+-}.
```

No compression term belongs here.
No same-sign operator belongs here.
No unnamed matrix residue belongs here.

### Step 6. Immediate handoff

If bulk vanishing lands, the next theorem attempt is forced:

```tex
PO3:\qquad
\mathcal D_{a,\partial}^{+-}=0.
```

If bulk vanishing does not land, do not climb back to `H2/H3/H4`.
Treat the current `H`-bridge as still conditional and unresolved.

## Exact lemma package for the next attack

The next proof-facing move should no longer say “work on `PO2`”.
It should say exactly which three local lemmas we are trying to land.

### L1. Common filtered stencil on the Suzuki side

From `Main_closure.tex`, Proposition `prop:H1-raw-entry-reduction`, we already
have for `N<n,m\le M`:

```tex
M_{mn}^{+-}(a)
=
w_{m,-n}(a)
+ w_{m+1,-n}(a)
+ w_{m,-(n+1)}(a)
+ w_{m+1,-(n+1)}(a).
```

This is the exact four-term filtered stencil on the Weil/Suzuki side.
So there is no ambiguity left about what the cross-sign bulk object is.

### L2. Common filtered stencil on the Q3 side

From `Main_closure.tex`, Proposition `prop:H1-filtered-q-blocks`, we already
have:

```tex
\widetilde q_{mn}^{+-}
=
q_{m,-n}
+ q_{m+1,-n}
+ q_{m,-(n+1)}
+ q_{m+1,-(n+1)}.
```

So the pulled-back Q3 block is built from the exact same four-term stencil.
This is the key local reason `PO2` is even plausible.

### L3. Cross-sign bulk cancellation lemma

The real theorem attempt is now reduced to:

```tex
M_{mn}^{+-}(a)-\kappa(a)\widetilde q_{mn}^{+-}
```

for all tail indices `m,n>N`.

The cleanest target is:

```tex
M_{mn}^{+-}(a)=\kappa(a)\widetilde q_{mn}^{+-}
\qquad (m,n>N),
```

which upgrades directly to

```tex
\mathcal D_{a,\mathrm{bulk}}^{+-}=0.
```

The only acceptable weaker output is that the whole residual operator already
belongs to the named boundary/cap channels.

### What not to do inside these lemmas

- do not revive the dead global raw identity `w_{rs}(a)=\kappa(a)q_{rs}`;
- do not move to finite sections first;
- do not let `(++)` leak into the argument;
- do not accept a “small numerically” cross-sign residue.

### Immediate theorem fork

After `L1` and `L2`, the proof splits cleanly:

1. either `L3` lands exactly and `PO2` is done;
2. or `L3` fails but the residual is already theorem-grade
   `\mathcal D_{a,\partial}^{+-}+\mathcal D_{a,\mathrm{cap}}^{+-}`;
3. or an unnamed bulk residue survives and kills the route.

## Admissible remainder channels after `PO2`

If `PO2` lands, only these channels may still remain in `(+,-)`:

| Channel | Allowed after `PO2`? | Why |
| --- | --- | --- |
| `\mathcal D_{a,\partial}^{+-}` | yes, temporarily | it is the exact subject of `PO3` |
| `\mathcal D_{a,\mathrm{cap}}^{+-}` | yes | cap-only fallback remains admissible |
| unnamed bulk residue | no | route-kill |
| finite compression term | no at this stage | belongs later to `PO6`, not to the tail bulk theorem |

## Route-kill condition

The current theorem picture dies immediately if `PO2` produces:

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\mathrm{bulk}}^{+-}
+ \text{other terms},
\qquad
\mathcal D_{a,\mathrm{bulk}}^{+-}\neq 0,
```

with no operator-theoretic reclassification into boundary or cap.

In words:

```text
an unnamed persistent cross-sign bulk residue kills the boundary/cap reset.
```

## Preferred theorem fork

### Best case

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\mathrm{cap}}^{+-},
```

with preferred stronger version

```tex
\mathcal D_{a,\mathrm{cap}}^{+-}=0.
```

### Acceptable pre-`PO3` case

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\partial}^{+-}
+ \mathcal D_{a,\mathrm{cap}}^{+-},
```

where `\mathcal D_{a,\partial}^{+-}` is now a named residual targeted next by
`PO3`.

This is also the right place to name cap explicitly without letting the cap
analysis consume the `PO2` proof itself.

### Failure case

```tex
\mathcal D_{a,\mathrm{bulk}}^{+-}\neq 0.
```

This is not “one more correction channel”. It is the exact route-kill event.

## Exact handoff to `PO3`

If `PO2` lands in acceptable form, the next note should not reopen the whole
cross-sign story. It should read only:

```tex
\mathcal D_{a,\partial}^{+-}=0.
```

So the correct handoff contract is:

- `PO2` is allowed to leave a named boundary term;
- `PO3` is required to kill it;
- the cap channel may remain explicit throughout this handoff;
- compression stays out of scope until `PO6`.

This is exactly the part of the worker report worth keeping: the handoff should
remain one-line and asymmetric, not reopen the full cross-sign classifier.

## Ingest checklist for worker input

If a parallel worker report arrives on `PO2`, it should be judged against the
following checklist rather than absorbed wholesale.

### Keep immediately

- an exact theorem-shaped statement equivalent to
  `\mathcal D_{a,\mathrm{bulk}}^{+-}=0`;
- an equivalent `boundary/cap-only` reformulation;
- a sharper route-kill condition than the one already recorded here;
- a cleaner handoff contract from `PO2` to `PO3`.

### Keep only as supporting rationale

- operator-theoretic explanation of why cross-sign bulk should vanish;
- comparison with the same-sign block that sharpens the asymmetry;
- clarification of whether the cap channel should already be named in `PO2`.

### Reject on sight

- anything that reopens rank/basis language;
- anything that introduces finite-section numerics into `PO2`;
- anything that treats a surviving unnamed bulk residue as “still acceptable”;
- any attempt to turn `PO2` into a same-sign `(++)` theorem.

## Local next move if no worker result lands

If the worker remains silent, the next local tightening should be:

1. rewrite `PO2a` as one exact lemma statement plus one equivalent finite-shadow
   corollary;
2. make explicit whether the preferred theorem output is exact cross-sign
   identity or cap-only fallback;
3. only then advance to `PO3`.

## What `PO2` must not do

- no finite-section compression bookkeeping;
- no rank/basis language;
- no same-sign boundary discussion beyond contrast;
- no premature positivity/cap-absorption claims.

## Immediate next receiver

If `PO2` lands, the next packet is forced:

```tex
PO3:
\qquad
\mathcal D_{a,\partial}^{+-}=0.
```

Only after that does the route spend proof energy on the same-sign channel
`H_a^{\mathrm{ss}}`.

## Success criterion

This note lands only if the next theorem attempt can be written as:

- one exact bulk-vanishing lemma for `\mathcal D_{a,N}^{+-}`;
- one explicit theorem fork saying the only admissible remainder is
  boundary/cap-only.
