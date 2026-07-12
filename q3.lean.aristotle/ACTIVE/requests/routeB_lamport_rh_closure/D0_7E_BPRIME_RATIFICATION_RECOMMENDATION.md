# D0.7e — Codex recommendation for B-prime owner ratification

Status: `CODEX_RECOMMENDATION / OWNER_DECISION_PENDING / NOT_RH`

This file does not ratify anything on behalf of the owner. It turns the five
open decisions in `D0_7E_PRO_REVIEW_RESPONSE.md` into one exact recommended
owner block, with current-disk corrections.

## Recommended decisions

### R1 — approve B-prime structurally, keep the slot fail-closed

Approve the acyclic rehoming of the full compact-strip/joint-limit tracking
theorem out of D0 and into the H3 tier. Do not close `D0.7e.5` merely because a
typed slot can be written. The `SLOT_VACUITY` and `TAUTOLOGY` plants are
mandatory, and the later browser review's independent-consumer requirement
must pass before `D0_7E_B_ORIENTATION_LOCKED` can be issued.

### R2 — choose H3e, not PO-10

Choose a distinct leaf

```text
H3e ExactWPrimeTrackingTheorem.
```

Canonical Contract v2 already assigns `PO-10 DetectorBridge` to the theorem
whose output is `SafeAlphaUpper` (`ROUTE_B_THEOREM_CONTRACT_v2.md:110`). The
WPrime/Xi compact-strip tracking theorem has a different input/output type.
Folding it into PO-10 would conflate two theorems and recreate the naming
ambiguity the review is trying to remove.

`D0.8` remains only the same-object QW/ground/Dlog/transform crosswalk. It does
not own uniform tracking.

### R3 — pin the canonical Contract-v2 direct exponent

Use the v2 convention

```text
0 < c_b <= |b(lambda)| lambda^(-q_b) <= C_b,
```

equivalently `|b(lambda)|` has power `q_b`. Then the registered owner
expectation `|bDet| sqrt(lambda) approximately constant` means
`q_b=-1/2`, and the SafeRate condition stays

```text
r_Delta-r_alpha > 2 q_b + 1.
```

The Pro response's statement that only Contract v1 exists is stale on the
current disk: v1 line 3 says it is superseded, and v2 line 6 says it replaces
v1. The historical conversion

```text
q_b^(v1)=q_b^(v2)+1/2
```

should be kept only as a glossary crosswalk, not as two live conventions.

### R4 — keep the two-parameter carrier

Keep independent `(m,N)` throughout D0/H3. Do not pin `kappa` and do not define
`N(lambda)` until a source-backed selector theorem exists. In particular, do
not infer `kappa` from the diagnostic anchor `(lambda^2,N)=(13,120)`.

### R5 — alpha is born in H0/A1

Confirm that the unique canonical definition of `alpha` belongs to H0 slot A1
(`ExactDetectorDictionary`). D0.7e may consume a typed alpha parameter but may
not mint `alpha := ...`. The exact D0-to-H0/H3 crosswalk remains a separate
one-dictionary obligation.

## Additional H3 obligation

Register

```text
PO_XWALK_UNIFORM_EVAL
```

at the H3 tier. The raw evaluation factor
`sqrt(L_m) lambda_m^a/c_low` diverges even at `a=0`; choosing another `q_b`
cannot repair it. A cancellation-improved or weighted evaluation theorem is
genuinely required.

## Paste-ready owner block

```text
OWNER_RATIFICATION_D0_7E_BPRIME:
R1 = APPROVE_BPRIME_REHOME_TO_H3_TIER_WITH_SLOT_VACUITY_AND_TAUTOLOGY_GUARDS
R2 = H3e_ExactWPrimeTrackingTheorem
R3 = CONTRACT_V2_DIRECT_QB_CONVENTION
R4 = TWO_PARAMETER_m_N_NO_KAPPA_NO_SELECTOR
R5 = ALPHA_DEFINITION_HOME_H0_A1
GUARD = D0.7e.5_REMAINS_BLOCKED_UNTIL_INDEPENDENT_CONSUMER_AND_ORIENTATION_PASS
NOT_RH
```

Until the owner supplies that line (or different explicit choices), this file
is advisory only and the active mathematical stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`.
