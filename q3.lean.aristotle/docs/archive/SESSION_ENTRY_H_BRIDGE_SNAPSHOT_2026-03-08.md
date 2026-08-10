# Archived Session-Entry H-bridge Snapshot

Status: `HISTORICAL_ONLY`

Archived: 2026-08-06

Verbatim full predecessor is preserved by Git at
`99acf3ff6cc3de4433e264aeed4861278b808f09:q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md`.
This file preserves the mathematical payload removed from the live session
router; it does not select work.

## Public route stated by the snapshot

`T0-pd -> H-bridge -> H4 -> RH`

The snapshot treated `H1^f -> H2^f -> H3^f -> H4^f` as the primary operator
backend and `PSD-pd` as a fallback Weil-side route. Its preferred finite object
was the symmetric two-sided filtered-tail package

```text
P_{M,N}, Delta_{M,N}, phi_n^±[a], S_{a,M,N},
B_{M,N} = Delta_{M,N}* Delta_{M,N},
Q~_{M,N} = Delta_{M,N}* Q_{M+1} Delta_{M,N}.
```

The exact raw identity was retained only as a zero-defect special case. The
working theorem shape was filtered intertwining modulo an explicit finite
boundary/cap correction, with `(++),(+-)` as the primary blocks and the other
two blocks derived by symmetry.

## Frozen normalization payload

```text
Q_M^raw = T_M[P_A] - Pi_M
Pi_M = (2M+1) T_P^Ray(t,M)
q_rs = A_{r-s} - sum_n lambda_n exp(2 pi i (s-r) xi_n)
lambda_n = (2 Lambda(n)/sqrt(n)) Phi_{B,t}(xi_n)
kappa_A3 = 1
```

The snapshot explicitly rejected the global exact shape
`w_rs(a) = kappa(a) q_rs`: the Q3 matrix is Toeplitz with constant diagonal,
whereas the raw Suzuki matrix has logarithmically growing diagonal. It kept
the compact scalar package diagnostic-only and the finite-prime Gram machinery
as engineering support, not a third RH route.

## Why it left the live entry

By 2026-08-06 its monitors were parked or dormant, while Route B had a separate
physical bus. Keeping this dated frontier in the unconditional startup path
made a new executor select stale work. The formulas remain available here and
in the pinned predecessor; current work is selected only by live physical
state under `docs/CODEX_CONTROL.md`.
