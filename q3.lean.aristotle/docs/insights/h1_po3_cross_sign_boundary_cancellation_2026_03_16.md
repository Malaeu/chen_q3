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
