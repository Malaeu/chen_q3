# D0.7e.5d — PO_D0_7E_XWALK address migration

Status: `PROVED_MIGRATION_CORRECTNESS_ONLY / H3E_OPEN / NOT_RH`

This leaf proves only that the already registered obligation has moved from
the D0 tier to `H3e_ExactWPrimeTrackingTheorem`. It neither proves nor weakens
the obligation. The text below is a verbatim quotation of
`D0_7E_OWNER_INPUT.md:78-98`; in particular, any definitional-looking formula
inside the quotation remains quarantined as OPEN historical wording and is not
adopted as a D0 definition.

## Verbatim registered obligation

```text
W_PRIME_CROSSWALK (theorem statement; registered obligation PO_D0_7E_XWALK):
  Let v1 be the even-sector ground with phase <v1, k1_even> >= 0 (D0 F4.4),
  alpha_(m,N) the canonical parity-projected Rayleigh excess (D0 F3.2),
  DeltaE_(m,N) the true complementary spectral distance of the H4 ledger, and
    WPrime_(m,N)^2 := |bDet_(m,N)|^2 * lambda_m * alpha_(m,N) / DeltaE_(m,N),
  with bDet the scalar defined ABOVE (independently of any spectral data).
  THEOREM SHAPE to be proved: if the two-sided bound of interface I-b2 holds
  (0 < c_low <= |bDet|*sqrt(lambda_m) <= C_b * lambda_m^(q_b + 1/2)), then for
  every compact K subset S there exist A_K < infinity and eps_(m,N,K) -> 0:
    sup_K |Fhat_(m,N) - bDet_(m,N) * Xi|
      <= A_K * [ WPrime_(m,N) + |bDet_(m,N)| * delta_dict_(m,N) ] + eps_(m,N,K),
  where the first term arises from the strip-evaluation constant of F5.1
  (sqrt(2 log lambda) * lambda^(1/2 - delta_K)) composed with the two-step
  Davis-Kahan / Kato-Temple bound sqrt(alpha/DeltaE) <= eta/DeltaE of the H4
  two-level ledger, and delta_dict is the H3c dictionary convergence term of
  the calibrated ground tracker. Proof route: F5.1 strip bound + Kato-Temple
  + two-level Davis-Kahan + Groskin-dictionary pointwise convergence +
  Vitali. NON-TAUTOLOGY: bDet is defined by a central VALUE of the tracker;
  WPrime is defined by SPECTRAL quantities; the theorem CONNECTS the two —
  WPrime is at no point redefined, and the inequality direction (tracking
  error controlled by WPrime) is exactly what roof 3.3' consumes.
```

## New address

```text
owner: H3e_ExactWPrimeTrackingTheorem
dependencies: D0, H3a, H3b, H3c, H4c, H4d
external requirements: PO-1/A1, PO_XWALK_UNIFORM_EVAL
tracking proof status: OPEN
```

The dependency graph remains acyclic. `D0.7e.5d` certifies only preservation
of wording and address; it does not close `H3e`, `PO_XWALK_UNIFORM_EVAL`,
`D0.7e.5a`, or `D0.7e.5c`.

Verdict: `D0_7E_XWALK_MIGRATION_LOCKED / NOT_RH`.
