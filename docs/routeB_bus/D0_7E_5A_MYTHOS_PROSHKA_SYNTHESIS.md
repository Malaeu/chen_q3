# D0.7e.5a — Mythos + Proshka synthesis

```yaml
STATUS: RATIFIED_DOCUMENTATION_SYNTHESIS
PRIMARY: SOURCE_PARTIAL_NEIGHBORING_DETERMINANT_ONLY
DATE: 2026-08-03
PIN:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: 6af9170d15a38e451a76f8dbf2ad8725d62b6f5f
  ACTIVE_ADDRESS: RB-LAMPORT-D0 / D0.7e.5a
INPUTS:
  MYTHOS: D0_7E_5A_MYTHOS_SOURCE_ACQUISITION_VERDICT.md
  PROSHKA: D0_7E_5A_PROSHKA_SOURCE_AUDIT_VERDICT.md
MAP: maps/2026-08-03_d0_7e_5a_mythos_source_acquisition_verdict.svg
CONTROL_PLANE:
  ROUTE_STATE: CHALLENGER_NOT_RH
  LEAN_EDITS: false
  ROUTE_STATE_EDITS: false
  BUS_010: VOID
  ROUTE_PROMOTION: false
  RH_CLAIMED: false
SUCCESS_CODE:
  D0_7E_B_ORIENTATION_LOCKED: NOT_ISSUED
STOP_CODE: D0_7E_WPRIME_CONSUMER_MISSING
```

## One-line verdict

CCM supplies a genuine finite rank-one operator, a finite Fourier
approximant, and a theorem-level regularized-determinant observable; it does
not supply the source-defined nonnegative `WPrime` consumer required by
D0.7e.5a.

## Agreement between the two audits

Mythos and Proshka agree on the substantive source recovery:

- the CCM perturbed scaling operator is real source material;
- the regularized determinant identity is a genuine theorem with independent
  meaning;
- the source package contains no `alpha`, `DeltaE`, or 5c RHS tautology;
- no source-defined historical `WPrime` was found on the checked surfaces;
- the boundary normalization is not proved equal to the project central-value
  calibration;
- no Lean, route-state, Bus 010, route-promotion, or RH action follows;
- `D0_7E_WPRIME_CONSUMER_MISSING` remains the stop.

## Repair to the Mythos conclusion

Mythos's phrase “the missing item is exactly one orientation line” does not
survive the independent audit. The missing conjunction is:

```text
SourceWPrimeDefinition
+ SourceWPrimeIndependentSemantics
+ exact source approximant for that consumer
+ FZeoToProjectGCrosswalk
+ source/project parameter and carrier crosswalk
+ finite normalization crosswalk
+ CentralValueNonzero domain theorem
+ bCal / bCal^(-1) / third-scalar orientation
+ separately proved WPrimeEquation5c
```

The determinant theorem is therefore neighboring H2b/finite-real-zero evidence,
not a `WPrime` consumer. This is a categorical distinction between typed
objects, not a naming preference.

## Final source classification

```text
SOURCE_PARTIAL_NEIGHBORING_DETERMINANT_ONLY
```

Safe imported statement:

> At arXiv:2511.22755v1, under the simple-even finite Weil-ground hypothesis
> and normalization `delta_N(xi)=1`, CCM defines the rank-one perturbed
> scaling operator `D_log^(lambda,N)` on
> `L²([lambda^-1,lambda],d*u)` and proves
> `det_reg(D_log^(lambda,N)-z) = -i*lambda^(-iz)*xi_hat(z)`, with `xi_hat`
> entire and all its zeros real.

This supplies:

- a source-defined finite operator;
- a source-defined finite Fourier approximant;
- an independently meaningful determinant observable.

It does not supply:

- `WPrime : D -> R>=0`;
- a theorem connecting `WPrime` to the determinant;
- a source `FZeo` identified with project `G`;
- the exact `lambda²=m` object/carrier crosswalk;
- the legal `CentralValueNonzero` crosswalk;
- the `bCal` versus `bCal^(-1)` orientation;
- equation 5c.

## Decision boundary

No further broad literature grep is justified without a new pinned lead. The
next belief-changing evidence would have to be an exact source formula that
simultaneously gives:

```text
WPrime : D -> R>=0
+ independent semantics
+ a theorem relating it to the recovered determinant or another observable
```

Absent that, the owner must choose whether to preserve source lock or change
the mathematical contract.

### Recommended immediate path

1. Reclassify the recovered CCM operator/determinant package as neighboring
   finite-real-zero/H2b source evidence.
2. Keep D0.7e.5a stopped at `D0_7E_WPRIME_CONSUMER_MISSING`.
3. Preserve `CHALLENGER / NOT_RH` and `Bus 010 VOID`.
4. Ask the owner for one explicit decision:
   - retain source lock and close this D0 ladder as unavailable under the
     checked provenance surface; or
   - authorize a new-definition transaction with independent semantics and a
     separately proved 5c theorem.

The first path is the cheapest and most honest under the current contract.
The second is a genuine scope change and must not be described as source
recovery.

## Paste-ready owner request

```text
Respond in English only.

At pin 6af9170d15a38e451a76f8dbf2ad8725d62b6f5f, Mythos source
acquisition and an independent Proshka audit converge on the following:

RATIFIED SOURCE PARTIAL:
- CCM defines the finite rank-one perturbed scaling operator
  D_log^(lambda,N).
- CCM proves the regularized determinant identity
  det_reg(D_log^(lambda,N)-z) = -i*lambda^(-iz)*xi_hat(z).
- This is genuine neighboring finite-real-zero/H2b source evidence.

NOT RECOVERED:
- a source-defined WPrime : D -> R>=0;
- independent WPrime semantics linked to the determinant or another exact
  observable;
- a source FZeo-to-project-G crosswalk;
- the source/project parameter and carrier crosswalk;
- a CentralValueNonzero domain theorem;
- bCal versus bCal^(-1) orientation;
- a separately proved equation 5c.

Therefore the repaired classification is:
  SOURCE_PARTIAL_NEIGHBORING_DETERMINANT_ONLY

The stop remains:
  D0_7E_WPRIME_CONSUMER_MISSING

No Lean or route-state edit was made. Bus 010 remains VOID. Route B remains
CHALLENGER / NOT_RH.

OWNER DECISION REQUIRED — choose exactly one:

A. KEEP_SOURCE_LOCK_AND_CLOSE_THIS_D0_LADDER
   Accept that no IndependentWPrimeConsumer was recovered on the checked
   provenance surface; reclassify the CCM package as neighboring H2b evidence;
   do not create Bus 010.

B. AUTHORIZE_EXPLICIT_NEW_DEFINITION_TRANSACTION
   Authorize a new typed IndependentWPrimeConsumer with a nonnegative scalar,
   independent semantics, legal CentralValueNonzero domain, exact FZeo/G and
   b crosswalks, and equation 5c as a separate theorem. This is new
   mathematics, not source recovery.

C. AUTHORIZE_CONTRACT_REPLACEMENT_BY_DETERMINANT_OBSERVABLE
   Replace the historical WPrime contract with a determinant-based consumer
   and re-prove all downstream interfaces. This is a major route revision;
   equation 5c does not survive automatically.

Codex recommendation: A, unless the owner explicitly intends to change the
source-lock/no-new-definition rule. B is the smallest constructive scope
change. C is not recommended without a new route design.

Return exactly:

PRIMARY: <A | B | C>
OWNER_AUTHORIZATION: <exact authorized scope>
ROUTE_EFFECT: <none | explicit revision>
BUS_010: VOID
SUCCESS_CODE: <issued or NOT_ISSUED>
STOP_CODE: <retained or replaced>
NEXT_SMALLEST_ACTION: <one action only>

Do not edit Lean, route state, MAP, MANIFEST, or create a bus goal in this
decision response.
```

## Anti-overclaim ledger

Do not claim any of the following:

```text
determinant observable = WPrime consumer
delta_N normalization = bCal orientation
"suitable constants" = normalization theorem
b orientation is the only missing row
TrialNonzero = CentralValueNonzero
source line number = PDF page number
```
