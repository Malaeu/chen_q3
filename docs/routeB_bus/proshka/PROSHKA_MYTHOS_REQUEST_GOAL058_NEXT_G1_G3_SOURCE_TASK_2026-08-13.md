# Goal 058 joint request — next literal G1/G3 source task for Aristotle

Date: 2026-08-13

Roles:

- Proshka is the mathematical judge and must return the authoritative exact
  Aristotle prompt or an honest no-task stop.
- Mythos is the independent proof-architecture attacker and must try to break
  the selected source theorem before execution.
- Aristotle is only the later proof-search executor.

## Phase and source lock

```yaml
GOAL_ID: Goal058_G1_G3_CofinalGroundTracking
PROOF_ADDRESS: RouteB.Goal058.G1G3.CofinalGroundTracking
FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
SOURCE_OBJECT_FAMILY: literal ccmWeilMatFinite / sourceCCMComplexRow / Proposition59 family
BASE_HEAD: 66ed3c3365e9b522dc28de6c92c38cf5743b4759
BASE_BRANCH: rh_clean
BASE_ORIGIN: origin/rh_clean
CONTROL: P9_STRICT_PASS
CARTOGRAPHER: 207 RouteB files; 1834 declarations; missing 0; stale 0
ROUTE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
G1: OPEN
G3: OPEN
```

The response must re-pin to the exact commit containing this request before
emitting an executable task. A changed source must be re-read, not silently
adapted.

## New exact result already proved

Aristotle project `7e661f28-7943-4c6b-83e9-787c2eed4683`, task
`f958ac79-9673-4110-b9f7-538ee6673d38`, produced the kernel-checked file

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  CCMProposition59ComplexHermitianConnector.lean
sha256 dc5e858863647224c17256b3cf629efc000ca81cbea4fb9cfd02fef28a6bc4eb
```

The public theorem
`Q3.RouteB.proposition59CCMTransform_sub_sourceProjection_le` proves, for the
literal complex unit row `D0Pstar.sourceCCMComplexRow S i` and a real P59 row
`xi`, that

```text
|P59(xi)(z) - projectionScalar * P59Complex(sourceRow)(z)|
  <= proposition59CCMKernelL2(L,N,z)
     * sqrt(sourceCCMGroundProjectionErrorSq(S,i,xi)).
```

It also proves the exact identity

```text
sourceCCMGroundProjectionErrorSq S i xi
  = sum_j normSq((xi_j : Complex) - projectionScalar * sourceRow_j).
```

The result assumes no realification, parity, eigenvector, bottomness,
simplicity, spectral gap, complement coercivity, tracking, rate, cofinal
schedule, global positivity, or RH statement. It is finite and does not assert
that the projective error is small.

Validation at production Lean 4.26:

```text
direct lake env lean: PASS
target lake build: PASS (7792 jobs)
full lake build: PASS (7817 jobs)
q3_check: PASS
forbidden proof tokens: NONE
public theorem axioms: [propext, Classical.choice, Quot.sound]
```

Closeout:

```text
q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
  GOAL058_COMPLEX_HERMITIAN_P59_CONNECTOR_CLOSEOUT_2026-08-13.md
sha256 9268197ca616da5b7a9c03a5dff887f9a4a11336c110f88a58173e78def7355a
```

## What remains, exactly

```text
G1: prove a uniform literal-CCM spectral separation for the selected finite
    simple-even bottom family; a generic receiver or a finite numerical gap is
    not a supplier.

G3: on the same precommitted cofinal family, prove
      sourceCCMGroundProjectionErrorSq S_j i_j xi_j -> 0
    with the compact P59 kernel control needed by the connector; an abstract
    tracking receiver or a trial residual with no true separation is not a
    supplier.
```

Exact repository and knowledge searches after integration found no declaration
whose conclusion is either source statement. The prior exact commutator is
compatible with a nonsimple kernel. The finite M1 cell is evidence only and
cannot be promoted to a cofinal theorem.

## Required decision

Select exactly one primary:

```text
ARISTOTLE_G1_LITERAL_CCM_GAP_SOURCE
ARISTOTLE_G3_LITERAL_PROJECTIVE_DECAY_SOURCE
ARISTOTLE_JOINT_LITERAL_FESHBACH_SOURCE
ARISTOTLE_LITERAL_SOURCE_NO_GO
NO_SOUND_ARISTOTLE_SOURCE_TASK_AVAILABLE
```

Preference is not a vote. Select the strongest theorem actually derivable from
the pinned source. A difficult or non-obvious theorem is welcome. A circular
theorem is not.

### A. G1 literal source

An admissible theorem must derive a nonzero separation or complement floor for
the literal `ccmWeilMatFinite` selected family. It may not take any renamed
spectral gap, endpoint envelope, complement coercivity, simplicity, or bottom
isolation as a premise.

### B. G3 literal source

An admissible theorem must derive an actual bound or cofinal decay for
`sourceCCMGroundProjectionErrorSq` on the exact same family. It may not take
ground-to-trial tracking, projective decay, residual decay divided by a supplied
gap, leakage decay, or a post-selected schedule as a premise.

### C. Joint literal Feshbach source

An admissible joint theorem may derive G1 and the finite projective estimate
from one full-source block/Feshbach argument. It must use the literal matrix,
literal complex trial line, literal ground row, and one precommitted family.
It may not hide the result in a positive complement block, small coupling,
small residual, or endpoint-envelope hypothesis unless that quantity is itself
proved in the same owned file from existing source declarations.

### D. Literal no-go

A bounded kernel-checked no-go theorem is admissible only if it decisively
proves that the current source contract cannot imply a proposed G1/G3 supplier,
and names the smallest genuinely new mathematical binder required next.

## Proshka output contract

After the strongest attack, return exactly one primary and one attachment-ready
Aristotle task with:

```yaml
TARGET_ID:
PRIMARY_CLASS:
PIN:
OWNED_FILE:
ALLOWED_IMPORTS:
FORBIDDEN_IMPORTS:
EXACT_EXISTING_DECLARATIONS:
EXACT_BINDERS:
EXACT_THEOREM_HEAD:
WHY_BINDERS_ARE_DERIVABLE:
REQUIRED_AUXILIARY_LEMMAS:
MANDATORY_FALSIFIER_PLANTS:
EXPECTED_OUTPUT:
SUCCESS_CODE:
TYPED_STOP_CODES:
AXIOM_GATE:
VALIDATION_COMMANDS:
EVIDENCE_BOUNDARY:
```

The task must own one new Lean file only and forbid edits elsewhere. It must
forbid `sorry`, `admit`, `exact?`, `native_decide`, new `axiom`, and `opaque`.
It must require direct Lean, target build, full build, `q3_check`, forbidden
token scan, `#print axioms`, and diff check.

Mandatory falsifiers must include at least:

1. wrong-family/operator substitution;
2. finite-cell-to-cofinal substitution;
3. hidden realification or parity;
4. scalar-commutator tautology;
5. renamed gap/complement-floor premise;
6. renamed tracking/projective-decay premise;
7. post-outcome schedule selection;
8. generic receiver relabeled as literal source supplier.

If no exact theorem survives, return
`NO_SOUND_ARISTOTLE_SOURCE_TASK_AVAILABLE` and the smallest missing source
lemma signature. Do not manufacture a task merely to keep Aristotle busy.

## Mythos attack contract

Independently inspect the same pinned evidence and return:

```yaml
MYTHOS_VERDICT: SURVIVES | REJECT | REVISE | NO_TASK
ATTACKED_PRIMARY:
FIRST_HIDDEN_BINDER_OR_OBJECT_MISMATCH:
COUNTEREXAMPLE_OR_REASON:
SMALLEST_REPAIR:
RECOMMENDED_EXACT_THEOREM_HEAD:
```

Mythos should prefer a concrete counterexample or binder audit over narrative
agreement. If it proposes a theorem, it must obey the same literal-source and
non-circularity rules.

## Evidence boundary

This request authorizes task design and architecture attack only. It does not
close G1 or G3, does not authorize Route B promotion, does not make a PX or RH
claim, and does not turn finite numerics into a uniform or cofinal theorem.
