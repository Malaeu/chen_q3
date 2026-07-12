# D0.7e.5 — PRO REVIEW DECISION (owner/Mythos ruling on ExactWPrimeZeoCrosswalk)

Date: 2026-07-12 · Channel: Mythos (owner/pro) · Answers: PRO_REVIEW_REQUEST in `D0_7E_CENTRAL_MELLIN_CALIBRATION.md` (sha of audited owner input a0f8ef78…f0bfed). NOT_RH.

## Primary verdict

```text
OPTION B — RATIFIED.
D0.7e requires ONLY the non-circular algebraic bDet consumer identity.
The full compact-strip tracking theorem is downstream material (D0.8 / H3),
NOT a D0.7e obligation. The owner input over-scoped field 7; this ruling
fixes the intended reading: "consumed by the W'/ZEO identity" = typed
definitional wiring, not the tracking estimate.
```

## Exact D0-internal consumers (closing D0_7E_ALPHA_DELTAE_UNDEFINED)

All objects below use only locked D0 nodes (D0.3g WeilOp, D0.4 sectors,
D0.5 trial types, D0.7a–d normalizations, D0.7e.1–.4 bDet). No H1–H4 import.

```text
EvenTrialNonzero := {(m,N) in TrialNonzero : ||Pi_even k1_(m,N)|| > 0}

k1even_(m,N) := ||Pi_even k1_(m,N)||^(-1) * Pi_even k1_(m,N)

a1even_(m,N) := < k1even, WeilOp_even_(m,N) k1even >

mu1even_(m,N) <= mu2even_(m,N) <= ...  (even-sector spectral namespace, D0.3g)

alpha_(m,N)  := a1even_(m,N) - mu1even_(m,N)
   Lemma (one line, D0-internal): alpha >= 0 on EvenTrialNonzero, because a
   unit-vector Rayleigh value dominates the sector minimum (min-max). No
   numerical sign is used.

DeltaEfin_(m,N) := mu2even_(m,N) - mu1even_(m,N)
   (finite same-sector spectral distance of the canonical finite detector;
    defined when dim(even block) >= 2; strict positivity NOT claimed.)

GapNonzero := {(m,N) : DeltaEfin_(m,N) > 0}
```

## The consumer identity (the actual D0.7e.5 content — closable now)

On `BDetNonzero ∩ EvenTrialNonzero ∩ GapNonzero` DEFINE

```text
WPrime_(m,N) := |bDet_(m,N)| * sqrt(lambda_m) * sqrt( alpha_(m,N) / DeltaEfin_(m,N) ).
```

Typed algebraic crosswalk theorem (acyclic): the scalar consumed by this
identity is exactly the D0.7e.2 CentralMellinCalibration bDet — by
construction, with every factor a previously locked D0 object on an explicit
dependent locus. Nothing about size, limits, or tracking is asserted.
Suggested exit: `D0_7E_WPRIME_CONSUMER_IDENTITY_LOCKED`.

Relation to the true complementary distance is explicitly a DOWNSTREAM
theorem (H4c): substituting DeltaEfin for the true distance in any ESTIMATE
without that theorem is the standing failure code `MODEL_GAP_SUBSTITUTION`.

## Migration of the tracking theorem

The compact-strip inequality of owner-input lines 78–98 is REMOVED from
D0.7e scope and re-registered downstream:

```text
PO_D0_7E_XWALK  -->  PO_H3_TRACKING_WITH_WPRIME   (H3-side target),
with D0.8 carrying the same-object crosswalk that identifies H3's W_j with
the WPrime defined above.
```

Its known gaps stay attached to the migrated obligation, verbatim from the
audit: joint-limit quantifier (owner default to declare at H3c: iterated
limit N -> infinity at fixed m FIRST, then m -> infinity along m in N;
any diagonal requires a proved selector); uniform A_K
(`D0_7E_XWALK_UNIFORM_CONSTANT_GAP` — two admissible repair routes, decision
at H3: (i) absorb the strip factor sqrt(L_m)*lambda_m^a into the definition
of the tracking quantity W_j per compact K [owner default], or (ii) prove a
cancellation-improved evaluation estimate for the DIFFERENCE
Fhat_trial - Fhat_ground); b-bound contract mismatch resolves at
PO_B_BOUNDS by declaring q_b once, two-sided, per Contract v2 §3.

## N-selector ruling

Concur with rejection. D0 remains two-parameter (m,N). Any `N(lambda)`
selector (including the withdrawn `kappa` rule) is H3c joint-limit material
and must arrive there as a proved selector theorem, never as a D0 constant.
Code `D0_7E_N_SCHEDULE_UNPINNED` stands until then.

## Owner acknowledgments (K6, on the record)

1. The owner input cited unfrozen chat-pen lines (F3.2/F4.4/F5.1/F5.2/F5.4)
   and a nonexistent destination file. Defect acknowledged: source pointers
   must resolve on disk. Repair path: freezing `docs/EXACT_OBJECT_FAMILY.md`
   (command pending with Ылша) will materialize the cited lines; until then
   the audit's treatment of them as absent is correct.
2. The over-scoped field 7 is an owner error, corrected by this ruling.
3. The eta-series upgrade of `zeta(1/2) != 0` and the D0.6 reflection
   `Fplus(z) = T_m(k1)(-z)` are accepted as strict improvements over the
   owner text.

## Plants for the closing step (pre-registered)

- CONSUMER_ALIAS: replacing alpha by a1even alone (dropping mu1even) must
  fail the min-max sign lemma's dependency check.
- SECTOR_SWAP: computing DeltaEfin across parity sectors must trip the
  D0.3g namespace firewall.
- LOCUS_LEAK: evaluating WPrime outside the declared dependent loci must fail.

## Nonclaims

```text
NO_TRACKING_THEOREM_IN_D0 · NO_UNIFORM_A_K · NO_TRUE_GAP ·
NO_COFINAL_LOCUS · NO_BDET_BOUNDS · NO_N_SELECTOR · NOT_RH
```
