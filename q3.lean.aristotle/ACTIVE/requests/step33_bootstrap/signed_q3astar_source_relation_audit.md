# Signed-Q3AStar Source Relation Audit

Status: diagnostic only; no payload, radius-floor, or LDL data was mutated.

Louise/Pro decision applied:

```text
Canonical semantic signed finite-Weil A remains
  -centeredBSplineArchKernelProfile
SignedQ3AStar may not feed Step33A unless a source relation theorem
proves equality or a semantically valid correction decomposition.
```

## Summary

### primary (primaryK11)

```text
d=0 canonical signed midpoint : -1.233644453639219513e-01
d=0 SignedQ3AStar midpoint   : 7.889774143023171860e+01
d=0 correction               : 7.902110587559563726e+01
max |correction|             : 7.902110587559563726e+01
rank tol 1e-8                : 23
operator norm correction     : 1.018377950055125467e+02
max offdiag correction       : 1.616291113275569913e+01
P0-like relative residual    : 9.983951639990945592e-01
Q^T S Q relative residual    : 9.958525960706896551e-01
ker(Q) compressed relative   : 9.910438320396598444e-01
```

Interpretation:

```text
Correction is not diagonal, not rank-one/rank-two, not Q^T S Q-like,
not zero on ker(Q), and not P0-like at the tested finite matrix level.
```

### control (controlK9)

```text
d=0 canonical signed midpoint : -2.624890365877484422e-02
d=0 SignedQ3AStar midpoint   : 7.520513017099183628e+01
d=0 correction               : 7.523137907465060437e+01
max |correction|             : 7.523137907465060437e+01
rank tol 1e-8                : 23
operator norm correction     : 1.003603283864453743e+02
max offdiag correction       : 1.780869526361660604e+01
P0-like relative residual    : 9.974606868849912322e-01
Q^T S Q relative residual    : 9.967988230513105119e-01
ker(Q) compressed relative   : 9.906049224803802344e-01
```

Interpretation:

```text
Correction is not diagonal, not rank-one/rank-two, not Q^T S Q-like,
not zero on ker(Q), and not P0-like at the tested finite matrix level.
```

## SIGNED_Q3ASTAR_SOURCE_RELATION

```text
equality holds: no, numerically impossible against current receiver
correction structure: full-rank finite Toeplitz-like correction
zero on ker(Q): no
Q^TQ-like: no
P0-like: no
recommended route: reject SignedQ3AStar as Step33A A-hbox source unless
  a new semantic theorem retargets finite-Weil A itself
```

Next theorem route:

```lean
centeredBSplineSignedQ3AStarPayloadProfile_eq_signedFiniteWeilAProfile
```

is false for the current numeric surface.  The only honest next theorem
would be a correction decomposition theorem, but the correction is not
boundary/penalty/P0-like in this finite audit.
