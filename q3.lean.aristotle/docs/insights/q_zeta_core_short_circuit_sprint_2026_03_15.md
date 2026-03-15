# `Q_\zeta`-core short-circuit sprint (2026-03-15)

## Status

This note freezes the current execution plan after the `Q_\zeta`-core sync.

The point is not to widen abstraction, but to run a short two-lane sprint on
the already-frozen assets.

## Public route stays unchanged

```text
T0-pd -> H-bridge -> H4 -> RH
```

with

```text
H1^f -> H2^f -> H3^f -> H4^f
```

as the primary live mainline, and `PSD-pd` as the explicit fallback route.

## Sprint logic

Run two lanes in parallel.

### Lane A: operator defect calculus

Target:

```tex
D_{a,M,N}
:=
S_{a,M,N}^*G_g[a]S_{a,M,N}
-\kappa(a)\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}.
```

Question:

- exact filtered intertwining?
- explicit boundary/cap correction?
- short-range local / commutator / Toeplitz-Hankel correction?
- genuine bulk mismatch?

### Lane B: fallback certificates

Target:

```tex
S_J(\theta)=A_J(\theta)-P_J(\theta)
```

on finite admissible dictionaries, together with coefficient bounds,
Poisson-regularized verification, and explicit error budget.

## Exact division of labor

### Proshka

Give Proshka only the structural math:

- theorem-shape for the first adapter theorem in the `(+,-)` block;
- blockwise cancellation table;
- same-sign surviving term in `(++)`;
- preferred operator decomposition at the infinite-tail level;
- kill list.

### Local agent

Keep locally:

- exact formula ledger;
- notation freeze;
- compression bookkeeping;
- proof-obligation table;
- finite fallback `PSD-pd` work on the smallest admissible blocks.

This avoids duplicate labor.

## First theorem-sized target

The first adapter theorem is:

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+E_a^{+-}.
```

Decision:

- best case: `E_a^{+-}=0`;
- acceptable case: `E_a^{+-}` is an explicit transparent boundary/cap term;
- bad case: no stable theorem-grade shape.

If this lands, then:

- `\kappa(a)=\kappa_{+-}(a)` becomes structural instead of fitted;
- all real risk collapses into `(++)`;
- `H1^f` becomes asymmetrical in the correct way.

## Same-sign target after that

On the frozen `\kappa_{+-}(a)` scale:

```tex
M^{++}(a)-\kappa_{+-}(a)\widetilde Q^{++}
=
H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}.
```

The point is to identify a same-sign boundary / commutator /
Toeplitz-Hankel term, not a new rank fit.

## 7-day execution plan

1. Day 1:
   freeze the sprint, send Proshka the adapter prompt, and build the local
   `(+,-)` adapter ledger.
2. Day 2:
   build the `(+,-)` cancellation ledger and exact theorem target.
3. Day 3:
   build the `(++)` boundary-term inventory and compression split.
4. Day 4:
   assemble the proof-obligation table
   `H1^\infty -> H1^\partial -> H1^f`.
5. Day 5:
   continue the smallest explicit `PSD-pd` finite-block step in parallel.
6. Day 6:
   absorb Proshka's answer into one theorem memo.
7. Day 7:
   take the binary decision:
   adapter theorem is viable or the route must be narrowed / cut.

## Exact success criteria

At the end of the sprint we need at least:

1. one theorem-grade `(+,-)` shape;
2. one explicit candidate decomposition for `(++)`;
3. one proof-obligation ledger without rank/basis language;
4. one live finite `PSD-pd` certificate step.

## Exact stop list

Do not spend sprint time on:

- a new global rank hunt;
- reviving the raw identity `w_{rs}(a)=\kappa(a)q_{rs}`;
- augmented cap positivity before symbolic defect classification;
- theorem-grade common `(++)` basis talk while prefix holdout is still bad;
- a new RH architecture outside `H-bridge` and `PSD-pd`.
