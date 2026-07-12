# D0.7e.5a — WPrime consumer and calibration-orientation audit

Status: `OWNER_CONTRACT_RATIFIED / CANONICAL_ACTIVE_LEAF / PARTIAL_MATH_PROVED / SOURCE_BLOCKED / LEAN_UNPINNED / NOT_RH`

Partial exits:

```text
D0_7E_CENTRAL_NONZERO_LOCUS_LOCKED
D0_7E_BCAL_INVERSE_NORMALIZER_IDENTITY_LOCKED
```

Success code not issued: `D0_7E_B_ORIENTATION_LOCKED`.

## 1. Inputs and scope

The latest Pro review requires an independently existing `FZeo`/`WPrime`
consumer before the detector coefficient is wired into it. The physical owner
ruling `D0_7E_5_PRO_REVIEW_DECISION.md` proposes instead to define

```text
WPrime_(m,N)=|bDet_(m,N)| sqrt(lambda_m)
              sqrt(alpha_(m,N)/DeltaEfin_(m,N)).
```

That owner-ratified formula is a possible new amplitude convention, but it is
not an independently recovered ZEO consumer. This audit therefore preserves
the ruling as input and does not use it to close the requested crosswalk.

A second physical review, `D0_7E_PRO_REVIEW_RESPONSE.md`, retypes the parent as
a `TypedWPrimeConsumerSlot` and pre-registers `SLOT_VACUITY` as its likely
failure. The owner has now physically ratified R1-R5 in
`D0_7E_BPRIME_OWNER_RATIFICATION.md`, so this audit is the canonical active
child `D0.7e.5a`. Ratification supplies an interface decision, not the missing
independent consumer; the consumer must still be located before this child can
close.

No H3c or H4 statement is imported. Both finite indices `(m,N)` are retained.

## 2. Exact central locus

On `TrialNonzero`, the already locked scalar is renamed only descriptively:

```text
bCal_(m,N) := bDet_(m,N)
            = Fhat_(m,N)(0)/Xi(0)
            = sqrt(L_m)c0(k1_(m,N))/zeta(1/2).
```

`Xi(0)`, `zeta(1/2)`, `gammaC(1/2)`, and `sqrt(L_m)` are nonzero on the
finite carrier. Consequently the following equivalences hold on
`TrialNonzero`:

```text
c0(k1_(m,N)) != 0
<-> Fplus_(m,N)(0) != 0
<-> Fhat_(m,N)(0) != 0
<-> bCal_(m,N) != 0.                              (2.1)
```

Define the single dependent locus

```text
CentralValueNonzero
 := {(m,N) in TrialNonzero : c0(k1_(m,N)) != 0}.
```

By (2.1), this equals `FhatAtZeroNonzero`, `BCalNonzero`, and the existing
`BDetNonzero` locus.

`TrialNonzero` does not imply this condition. Even inside the even unit sphere,
`(V_1+V_-1)/sqrt(2)` has norm one and central coefficient zero. No theorem in
the repository excludes that possibility for the selected trial. This fires
`D0_7E_TRIALNONZERO_NOT_CENTRALNONZERO`.

Since `V_0` lies in the even sector, a nonzero `V_0` coefficient implies a
nonzero even projection. Thus

```text
CentralValueNonzero subset EvenTrialNonzero.         (2.2)
```

## 3. Multiplier versus divisor

On `CentralValueNonzero`, define the central-value normalizing multiplier

```text
bZeoMul_(m,N) := Xi(0)/Fhat_(m,N)(0).
```

Then exactly

```text
bZeoMul_(m,N) = bCal_(m,N)^(-1),
bZeoMul_(m,N) bCal_(m,N) = 1,
G_(m,N) = Fhat_(m,N)/bCal_(m,N)
          = bZeoMul_(m,N) Fhat_(m,N),
G_(m,N)(0)=Xi(0).                                    (3.1)
```

Therefore `bCal` and a ZEO normalizing multiplier are inverse scalars, not
aliases. The equation `bZeoMul=bCal` would require the unproved special
condition `bCal^2=1`. The namespace alias is forbidden by
`D0_7E_BCAL_BZEO_ALIAS_CONFLICT`.

This algebra does not decide what the historical `b` in `WPrime` means. The
two possible consumers

```text
WPrime_amp  = |bCal|    sqrt(lambda) sqrt(alpha/DeltaE),
WPrime_norm = |bZeoMul| sqrt(lambda) sqrt(alpha/DeltaE)
```

have reciprocal `b` factors and reverse the sign of any registered power
exponent for that factor. They cannot be merged by notation.

## 4. Provenance scan and exact audit scope

In the repository snapshot at pre-audit commit
`33101a9221ef692dd44c9f6d79f4fe0b525c5293`, audited at 2026-07-12 10:16 CEST,
the exact tree
scan found no independent definition of `FZeo`, `F_Zeo`, `bCal`, or `bZeo`.
Exact Git-history searches with `git log --all -S` returned no historical
commit for those exact names. This is a pinned-snapshot search verdict, not a
claim that no future or external source can supply the missing consumer.
`bDet` is the new owner-ratified central ratio, not an older recovered ZEO
object.

The W-prime formula occurs in several distinct source classes:

- `docs/ROUTE_B_THEOREM_CONTRACT_v2.md:28-29` is the canonical target contract;
  it requires the formula but is not a proof or independent consumer source.
- `docs/ALPHA_DEMAND_AUDIT.md:3,17,20-24` explicitly says
  `NOT_A_DEFINITION_SOURCE`, marks `b` missing, and records the formula as an
  audited/reconstructed target.
- `docs/CODEX_REORIENT_BRIEF_2026-07-10.md:27-29` and
  `docs/ALPHA_DETECTOR_OBJECT_LOCK.md:16,25-36` classify the row as a sketch
  with the export `OPEN_CRITICAL` and the `b` object missing.
- `ladder_law_v1.md:35-45` and `out/ladder_law_v1.json` are diagnostics marked
  `FIT_NOT_LAW`; they report unscaled and b-scaled values separately.

The common target shape is

```text
W' = |b| sqrt(lambda) sqrt(alpha/(mu3-mu1)),
```

None of the classified pinned sources defines the independent normalized ZEO
approximant whose coefficient orientation is under review.

The primary paper proves that the regularized determinant is a phase times the
Fourier transform of the finite ground vector and states only that suitable
constants should normalize the large-parameter limit to Xi. It defines no
project-local `FZeo`, `WPrime`, `bCal`, or `bZeo`, and explicitly lists the
quantitative trial-to-ground comparison as a missing step.

Accordingly, no independent consumer was found in the audited pinned snapshot
from which the calibration orientation can be recovered. A new physical source
may change this verdict and must then be re-audited.

## 5. Lamport verdict

```text
STATUS: STOP
PRIMARY CODE: D0_7E_WPRIME_CONSUMER_MISSING
Exact consumer definition: NOT_FOUND_IN_AUDITED_PINNED_SNAPSHOT
Exact orientation: normalized multiplier = bCal^(-1); historical WPrime b = UNPINNED
Exact nonzero domain: CentralValueNonzero = BDetNonzero, not TrialNonzero
Source files/lines:
  docs/CODEX_REORIENT_BRIEF_2026-07-10.md:27-29
  docs/ALPHA_DETECTOR_OBJECT_LOCK.md:16,25-36
  literature/zotero/H8ULBMAL/fulltext.md:1063-1079,1240-1255,1469-1477
  D0_7E_OWNER_INPUT.md:23-52,78-98
  D0_7E_5_PRO_REVIEW_DECISION.md:42-54
  D0_7E_PRO_REVIEW_RESPONSE.md:53-87,148-175
Dependency list: D0.5, D0.6, D0.7e.2, D0.7e.3, D0.7e.4
Namespace scan: no independent FZeo/F_Zeo/bCal/bZeo definition found in audited pinned snapshot
Commands and stdout:
  rg exact tree scan -> no independent hits
  git log --all -S'FZeo'/-S'bCal'/-S'bZeo' -> no commits
  q3_docs four-query search -> no relevant consumer result
Files touched: this audit/control-plane artifacts only; owner inputs unchanged
No H3c/H4 import: CONFIRMED
No Bus 010: CONFIRMED
NOT_RH: CONFIRMED
```

Secondary codes:

```text
D0_7E_ZEO_NORMALIZATION_ORIENTATION_MISSING
D0_7E_TRIALNONZERO_NOT_CENTRALNONZERO
D0_7E_BCAL_ZERO_OR_UNPROVED
D0_7E_BCAL_BZEO_ALIAS_CONFLICT
D0_7E_SOURCE_NORMALIZATION_CONFLICT
```

Owner ratification R1--R5 is now locked. The remaining required input is the
physical source-pinned independent definition requested in
`D0_7E_5A_CONSUMER_SOURCE_REQUEST.md`: the exact ZEO approximant and `WPrime`
consumer, including whether its named `b` is the amplitude ratio `bCal`, the
normalizing multiplier `bCal^(-1)`, or a third explicitly crosswalked scalar.
Until that arrives, `D0.7e.5a`, `D0.7e.5`, `D0.7e`, and all ancestors remain
blocked.
