# 013 — EStarUpperEdgeSignOrKill · этап A

Date: `2026-07-27`

```text
UPPER_EDGE_DIAG_SINGLE_SIGN
FLOAT64 DIAGNOSTIC — NOT A PROOF
CHALLENGER / NOT_RH
BUS_010_VOID
```

## 1. Coefficient-line lock

011:

\[
hTrial_m
=\frac{I_{4,\lambda}h_{0,\lambda}
       -I_{0,\lambda}h_{4,\lambda}}
      {\sqrt{I_{0,\lambda}^2+I_{4,\lambda}^2}}.
\]

Canonical Proshka form:

\[
\pm\frac{I_{4,\lambda}h_{0,\lambda}
       -I_{0,\lambda}h_{4,\lambda}}
      {\sqrt{I_{0,\lambda}^2+I_{4,\lambda}^2}}.
\]

The source phase is the `+` choice.  The coefficient rows coincide:

```text
СОВПАДАЕТ
```

## 2. Upper-edge diagnostic

The grid is exactly

```text
linspace(1/2, 1, 2003)[1:-1]
```

in `t=x/lambda`, hence 2001 points strictly inside
`x ∈ (lambda/2,lambda)`.

Direct Legendre summation is cancellation-limited in this tail and produces
spurious sign flips at the `1e-16` floor.  The reported float64 evaluation
instead uses:

1. the same even-sector tridiagonal eigenvalues and source phase as the
   canonical probe constructor;
2. a regular-endpoint Frobenius series at `t=1`;
3. dynamically rescaled backward DOP853 integration;
4. signed-log evaluation of
   `(I4*h0-I0*h4)/sqrt(I0^2+I4^2)`.

| m | lambda | c0 = I4/D | c4 = -I0/D | sign changes | sign on grid | zero positions | min abs h |
|---:|---:|---:|---:|---:|---|---|---:|
| 13 | 3.60555127546 | 0.518588011520 | -0.855024253637 | 0 | negative | none | 6.14340935948e-31 |
| 53 | 7.28010988928 | 0.521368520277 | -0.853331627249 | 0 | negative | none | 6.86493807306e-137 |
| 257 | 16.0312195419 | 0.522056182709 | -0.852911098588 | 0 | negative | none | float64 underflow; log10 abs = -679.394357209 |

The first/last sampled values are:

| m | h at first grid point | h at last grid point |
|---:|---:|---:|
| 13 | -2.68234444373e-4 | -6.14340935948e-31 |
| 53 | -4.32618518591e-18 | -6.86493807306e-137 |
| 257 | -9.75465937721e-92 | -0.0 (`log10 abs=-679.394357209`) |

No zero bracket occurs in any of the three cells.  Re-running with
`(endpoint epsilon, segment length) = (5e-9,0.005)` and `(2e-8,0.02)` leaves
all three sign counts at zero and agrees in the displayed leading digits.

Artifacts:

```text
ACTIVE/requests/routeB_lamport_rh_closure/
  upper_edge_sign_probe.py
  UPPER_EDGE_SIGN_PROBE.csv
  UPPER_EDGE_SIGN_PROBE.json
```

## 3. Exact-route memo

1. The local Mathlib source has Picard–Lindelöf/ODE uniqueness and Rolle, but
   no ready Sturm–Liouville oscillation or second-order zero-count theorem.
2. Therefore a direct `by exact Mathlib.sturm...` route is unavailable.
3. An interval certificate is viable only after the exact prolate modes,
   characteristic values, normalization, and their ODE are Lean objects.
4. On the single interval `[1/2,1]`, certify a rational enclosure for the
   signed logarithmic derivative or for a Chebyshev/Legendre approximation
   plus a uniform remainder.
5. Mathlib supplies polynomial roots/rule-of-signs and basic interval
   structures, but not a turnkey transcendental interval evaluator for PSWF.
6. Alternative A: formalize a tailored Sturm comparison proving the last zero
   lies left of `1/2`.
7. Alternative B: prove a Hermite-tail approximation with an explicit
   uniform remainder strong enough to preserve the negative sign.
8. Recommended stage B: interval ODE certificate on `[1/2,1]`; it matches the
   successful stable diagnostic and avoids a general Sturm library project.

No sign theorem, Mellin statement, zeta statement, STATE mutation, or RH
consequence is asserted.
