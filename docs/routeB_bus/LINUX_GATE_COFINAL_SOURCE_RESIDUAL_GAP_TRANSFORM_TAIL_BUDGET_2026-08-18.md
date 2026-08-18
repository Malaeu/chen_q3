# STATUS: GATE_RED_THEN_REPAIRED — SOURCE AS COMMITTED DID NOT COMPILE; AFTER REMOVING TWO DEAD TACTIC BRANCHES THE KERNEL GATE IS GREEN

```yaml
PRIMARY: COFINAL_SOURCE_RESIDUAL_GAP_TRANSFORM_TAIL_BUDGET_KERNEL_VALIDATED_AFTER_TACTIC_REPAIR

REPO: Malaeu/chen_q3
BRANCH: rh_clean
GATE_RUN_BY: LINUX_BODY

SOURCE_COMMIT_AS_WRITTEN: 2aa5dc5def4f8be8895634a809c9560ceecee947
SOURCE_BLOB_AS_WRITTEN: cd910e8485b6ce816b51080b42c8c0c0af1aa75c
PARENT: 648f240f8f01d05a19e666da1941dba2a1be28ec
RECEIPTS_CHECKED: blob, verdict blob, parent — all three match the claim

FIRST_GATE_RESULT: RED
FIRST_GATE_EXIT: 1
FIRST_GATE_ERROR: "line 180: No goals to be solved (abel after a closing simp)"
SECOND_GATE_RESULT: RED
SECOND_GATE_EXIT: 1
SECOND_GATE_ERROR: "line 174: No goals to be solved (second convert bullet, convert produced one goal)"
RED_GATE_AXIOMS: [propext, sorryAx, Classical.choice, Quot.sound]

REPAIR_EXTENT: tactics only; 2 lines replace 5; statement, hypotheses and
  proof strategy untouched
THIRD_GATE_RESULT: GREEN
THIRD_GATE_EXIT: 0
THIRD_GATE_AXIOMS: [propext, Classical.choice, Quot.sound]
Q3_CHECK: ok

THEOREM: Q3.RouteB.cofinalSourceResidualGapTransformTailBudget
DEFINITION: Q3.RouteB.sourceUnitRayleighResidual
SCOPE: COFINAL_FAMILY
VERIFIER: LEAN

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## 1. Receipts

Every claimed hash matches: Lean blob `cd910e84`, verdict blob `b2407caf`,
parent `648f240f`. Source and verdict arrived in one commit, so W5 holds. This
is the third consecutive time the receipts were exact and the file still did
not compile.

## 2. What the gate found

Two dead tactic branches, both reported as `No goals to be solved`:

- line 180: `abel` after a `simp [q]` that already closed the goal;
- line 174: a second `convert` bullet, where `convert … using 1` produced one
  goal, not two.

While either error stood, the theorem carried `sorryAx` and was not proved.

## 3. Repair

    -    · ext i z
    -      simp [e, smul_sub]
    -    · ext z
    -      rfl
    +    ext i z
    +    simp [e, smul_sub]

    ·  ext i z
       simp [q]
    -  abel

Tactics only. The statement, the hypotheses, the imported suppliers and the
proof strategy are untouched.

## 4. What this node actually fixes

The free-error loophole of the previous composition core is closed. No error
family and no decomposition identity appear as arguments. The tracking error
is built inside the proof from `ground`, `finiteProjection`, `sourceTrial`,
`normalizer` and `evaluation`; the residual is computed by
`sourceUnitRayleighResidual` from the same operator and the same vector. The
old substitution — define an error as the desired conclusion — no longer
typechecks.

## 5. What it does not fix

`gap : ι → ℝ` is a free parameter. Nothing in the type ties `gap i` to the
spectrum of `sourceOperator i`. This is the same class of hole one level down:
the true complement floor is a number a supplier brings, not a quantity
computed from the named operator. It is not free to abuse — a small `gap`
weakens `hprojectiveResidualGap` but breaks `hcompactBudget`, since
`√(2‖r‖²/gap²)` grows, and a large `gap` does the reverse — but the binding is
arithmetic, not typed.

A degenerate instantiation still passes: take `sourceTrial := ground` and
`finiteProjection := id`. Then `q i = ground i`, the tracking term vanishes,
and the conclusion is the `htail` premise. The theorem stays true and says
nothing. Unlike the previous hole this is visible in the type: it requires
equating the trial with the ground state by name.

`hcompactBudget` merges two suppliers into a single existential: the envelope
`C` and the rate `C · √(2‖r‖²/gap²) → 0`. The verdict names them separately.
Whoever supplies the envelope must supply the rate in the same object.

## 6. Finding: a hypothesis that does no work

    line 59: warning: unused variable `hnormalizerNonzero`

`hnormalizerNonzero : ∀ i, normalizer i ≠ 0` is never used. The theorem holds
without it. The normalizer enters only inside
`evaluation i z (normalizer i • x)`, and the bound `≤ C i * ‖x‖` already
absorbs it, so nondegeneracy is never needed.

This matters because the verdict lists normalizer nondegeneracy among the
open suppliers. In this type it carries no load: a reader may believe the
hypothesis constrains the normalization when it does not. Either drop it, or
replace it with a hypothesis that does work — for instance a lower bound
forcing the normalized projected transform not to collapse.

## 7. Fate of registered predictions

    P_CRGTTB_1  "source passes unchanged", p=0.68   REFUTED
    P_CRGTTB_2  "axioms are exactly the three standard ones", p=0.95
                REFUTED on the committed source (sorryAx present);
                CONFIRMED after the repair.

The predicted first-defect class was also wrong. The forecast was
`CONTINUOUS_LINEAR_MAP_OR_SQRT_API_MISMATCH`; the actual defects were two dead
tactic branches. Both `Real.sqrt_le_sqrt` and the continuous-linear-map API
went through unchanged.

## 8. Next

    LITERAL_CCM_COFINAL_RESIDUAL_FLOOR_ENVELOPE_AND_TRANSFORM_TAIL

plus the exact CCM object crosswalk: `sourceOperator`, `finiteProjection`,
`evaluation` and `trialTarget` are abstract here and must be shown to be the
production CCM objects rather than neighbouring surrogates.
