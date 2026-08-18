# STATUS: GATE_RED_THEN_REPAIRED — SOURCE AS COMMITTED DID NOT COMPILE; AFTER A ONE-TOKEN SYNTAX REPAIR THE KERNEL GATE IS GREEN

```yaml
PRIMARY: SAME_FAMILY_GROUND_TRIAL_COMPOSITION_CORE_KERNEL_VALIDATED_AFTER_REPAIR

REPO: Malaeu/chen_q3
BRANCH: rh_clean
GATE_RUN_BY: LINUX_BODY
GATE_RUN_AT_HEAD: d6d7df317e4f1c41f32fb5daae4943019c38756f

SOURCE_COMMIT_AS_WRITTEN: 9cc3e01b9e1974ac1283940422fa8a4177d0664f
SOURCE_BLOB_AS_WRITTEN: cc41c6e8b5e1489c2eaae6517f8bc6823a8f79ef
FIRST_GATE_RESULT: RED
FIRST_GATE_EXIT: 1
FIRST_GATE_ERROR: "SameFamilyGroundTrialCompositionCore.lean:60:4: expected '*' or checkColGt"
FIRST_GATE_AXIOMS: [propext, sorryAx, Classical.choice, Quot.sound]

REPAIR_COMMIT: 4893c9c5
REPAIR_BLOB: 782115dc
REPAIR_EXTENT: one token; `at` moved from the end of line 59 to the start of line 60
STATEMENT_CHANGED: false
TACTICS_CHANGED: false
PROOF_STRUCTURE_CHANGED: false

SECOND_GATE_RESULT: GREEN
SECOND_GATE_EXIT: 0
SECOND_GATE_AXIOMS: [propext, Classical.choice, Quot.sound]
Q3_CHECK: ok

THEOREM: Q3.RouteB.sameFamilyGroundTrialCompositionCore
SCOPE: ABSTRACT
VERIFIER: LEAN

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
ROUTE_B_STATE: NOT_TOUCHED

PUSHED_HEAD: 01094bf5
```

## 1. What the gate found

The file as committed in `9cc3e01b` did not parse. Line 59 ended with `at` and
put the rewrite targets on line 60. Lean 4 rejects that placement. The parse
error did not stop the axiom print, so the theorem reported

    [propext, sorryAx, Classical.choice, Quot.sound]

`sorryAx` means the theorem was not proved. The source read as complete and the
blob matched the SOURCE_LOCK byte for byte; neither fact says anything about the
kernel. Text verification and kernel verification are different acts.

## 2. Repair

    -  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU] at
    -    htracking htail hnormalization ⊢
    +  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    +    at htracking htail hnormalization ⊢

Nothing else changed. The statement, the hypotheses, the tactic sequence and the
proof structure are untouched. This is a parser fault, not a mathematical one.

## 3. Gate commands that actually run

    WORKDIR: q3.lean.aristotle
      lake env lean Q3/Proofs/RouteB/SameFamilyGroundTrialCompositionCore.lean
    WORKDIR: <repo root>
      bash scripts/q3_check.sh Q3/Proofs/RouteB/SameFamilyGroundTrialCompositionCore.lean

Two defects in the recorded gate block, both now fixed in the protocol:

- The verdict shipped `cd q3.lean.aristotle` followed by `./scripts/q3_check.sh`.
  The script lives at the repository root and resolves the root from its own
  location, so that path does not exist from inside `q3.lean.aristotle`. The
  canonical form in `Q3_OBSTRUCTION_ATLAS.md` lines 108-109 keeps the two
  commands in different working directories; the verdict merged them under one
  `cd`.
- `scripts/q3_check.sh` is tracked with mode `100644` and is therefore not
  executable. It must be invoked through `bash`. The canonical form does not say
  this and fails as written for every body.

## 4. Fate of registered predictions

    P-SF1  "lake env lean passes without source edits", p=0.78   REFUTED
    P-SF2  "axioms are exactly the three standard ones", p=0.97  REFUTED on the
           committed source; CONFIRMED only after the repair.

No retroactive repair: both predictions were made against `9cc3e01b`, and
`9cc3e01b` fails.

## 5. Boundary the gate does not close

The theorem is proved, and it proves less than its framing suggests. The three
errors enter as free parameters together with `hdecomp` as a hypothesis. Setting

    trackingError := finiteGroundTransform - ccmTrialTransform
    projectionTail := 0
    normalizationError := 0

satisfies `hdecomp` and turns the tracking premise into the conclusion. The
docstring forbids this in prose; the type does not. The same-family firewall
holds against changing the family between premises — one `ι`, one filter, one
domain — and does not hold against defining an error as the conclusion.

Telescoping through intermediate families does not close it either: with
`P = T` and `N = T` the tail and normalization errors vanish and the tracking
error is again the conclusion. Closing it requires the errors to be computed
from named objects by given operators — a projection operator and a normalizer
as arguments — so that `hdecomp` becomes a proved identity rather than a
hypothesis. That belongs to the source-specific layer, not to this one.

## 6. Open

    COFINAL_SOURCE_RESIDUAL_GAP_TRANSFORM_TAIL_BUDGET  unchanged
    ROUTE_B_STATE                                      not updated; the gate
                                                       result is recorded here
                                                       and the state entry is a
                                                       separate decision
