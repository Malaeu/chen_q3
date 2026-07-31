# GOAL 040 POST-CLOSE REQUIREMENTS AUDIT

```text
status: POSTCLOSE_REVIEWER_REQUIREMENTS
normative_for_goal_040_execution: false
modifies_goal_040_contract: false
```

Date: 2026-07-31 · Materialized by: conductor-CLI (Claude Code, Linux) on owner's
order, per Proshka verdict DRAFT_041_HOLD_FOR_VERSIONED_REPAIR.

Goal 040 is CLOSED (`PL2_RAW_POLE_MISMATCH_WITNESS_PROVED`, theorem
`exists_rawZetaMellin_not_continuousAt_one`, green build, zero taint, standard
axiom triple). This artifact records the reviewer requirements that arrived
AFTER closure. They are post-close reviewer guards for any future PL2-consuming
step; they are NOT conditions retroactively claimed as executed by the 040 proof.

## Reviewer guards (verbatim from ratified corrections)

A1.1 STRICTNESS PRECONDITIONS (explicit named fields; deleting either must break the
strict sign of the log-moment):
  bump_mass > 0                              (m = ∫ tent)
  right_support_lower > left_support_upper   (c2 - r > c1 + r; touching supports yield only <=0)

A1.2 NO-SKIP CLAUSE: no arrow of the chain
  translated equal-mass bumps => ∫h = 0 => ∫ h·log u du < 0
  => deriv (Mellin h) 1 ≠ 0 => ¬ContinuousAt (fun w => riemannZeta w * Mellin h w) 1
may be replaced by numerical integration or by an unproven "differentiation under the
integral sign". ∫ h·log u du < 0 alone is NOT PL2: without the proved identification
deriv (Mellin h) 1 = ∫_{Ioi 0} h u * Real.log u du the run returns
PL2_DERIV_IDENTIFICATION_API_GAP, not success.

A1.3 Additional registered prediction:
P040-PL2 (Proshka): the generic simple-zero => raw-product discontinuity closes by
reuse of the existing residue/slope theorem; the dominant Lean friction is the exact
derivative identification, not the final discontinuity proof.

## Route classification (per Proshka DRAFT_041 verdict)

The tent/translation/log-bound route above is classified SOUND BUT SUPERSEDED,
not as the factually used proof route. The actual 040 proof used a cheaper exact
witness: the compact quadratic function

  h(u) = 1_{(0,1]}(u) * u - (3/2) * 1_{(0,1]}(u) * u^2

with exactly computed Mellin transform, zero mass, and
deriv (Mellin h) (1) = -1/12.

## Provenance history (honest, includes the reverted misstep)

1. 2026-07-31, commit 19a4dcbf: AMENDMENT A1 was appended to the CLOSED goal-040
   file (both copies) on Mythos instruction and owner's same-day order
   (goal SHA changed 48172cdb… -> 2aac67d5…).
2. Proshka verdict DRAFT_041_HOLD_FOR_VERSIONED_REPAIR ruled this retroactive
   contract mutation FORBIDDEN (a closed goal is immutable; later reviewer
   requirements need a separate artifact).
3. This commit: goal 040 restored byte-identical to its pinned pre-A1 state
   (SHA-256 48172cdbc16f527b2cc4b3c1c28772b4cbaf7f036b57326001e4e69046989300,
   both copies verified), and the requirements moved HERE as post-close guards.

The interim mutation remains visible in git history (19a4dcbf); it is not hidden.

## Registered invariant (from the verdict, binding for the future)

A closed goal is immutable; later reviewer requirements need a separate
versioned artifact. Forbidden future move: rewrite a proved contract to match
later feedback.
