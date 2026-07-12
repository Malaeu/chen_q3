# D0.7e T1 — persisted-vector bDet judges

Status: `PARTIAL_BLOCKED_MISSING_LAMBDA17_PERSISTED_VECTOR / NOT_RH`.

This run reads only the persisted normalized `k1` coefficient vectors. It does
not rebuild a packet, choose `N(lambda)`, or define `alpha`, `DeltaE`, a filter,
or `WPrime`. Reproducer: `d0_7e_t1_persisted_judges.py`; machine record:
`D0_7E_JUDGE_CERTIFICATES.json`.

| cell | c0 sign | bDet | bDet sign | abs(bDet)sqrt(lambda) | direct-integral relative residual |
| --- | --- | ---: | --- | ---: | ---: |
| `(13,90)` | negative | `0.5921835835971867` | positive | `1.124455315736602` | `1.284e-16` |
| `(13,120)` | negative | `0.5921835835971867` | positive | `1.124455315736602` | `1.284e-16` |
| `(14,120)` | negative | `0.5929138322605350` | positive | `1.146894819822029` | `1.281e-19` |
| `(17,120)` | — | — | — | — | `T1_LAMBDA17_PERSISTED_COEFFICIENT_VECTOR_MISSING` |

The N-stability factor at lambda-squared 13 is
`1.00000000000000000000000000000000000000000000000000000000000166`,
well inside the registered factor-3 judge. Direct midpoint quadrature of the
persisted finite Fourier vector agrees with `sqrt(L)c0` at binary machine zero
on every available cell. Zeroing the stored `c0` entry makes `bDet` exactly
zero and fires `B_CENTRAL_ZERO_CELL` on all three shadows; the plant is live.

On the two available N=120 cells, the FIT_NOT_LAW quantity
`abs(bDet)sqrt(lambda)` changes by factor `1.0199558878`, so P3 passes only as a
two-cell diagnostic. It is not fully scored because the pre-registered
lambda-squared 17 vector is absent.

The displayed enclosures propagate the stored Q192-vs-Q96 coefficient
difference and a conservative enclosure around the owner-input decimal for
`zeta(1/2)`. They certify the numerical input signs, not a proof-grade bound on
the unknown true quadrature error. Exact nonvanishing of `zeta(1/2)` remains
the separate eta-series theorem.

T2 is not legally instantiated from the current persisted corpus: the
lambda-squared 17 tracker is missing, and no pinned canonical `WPrime` or
`delta_dict` table exists. Historical ladder-law values use diagnostic alpha
and the superseded `bPilot`, so substituting them would violate the sprint
firewall rather than calibrate H3e.

Nonclaims: no asymptotic bound, no cofinal nonvanishing, no selector/filter,
no H3e theorem, and no RH implication.
