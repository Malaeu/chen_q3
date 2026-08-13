# Proshka request — design the exact Aristotle task after the Goal 058 source preflight

Date: 2026-08-13

Requested role: Proshka is the mathematical judge and task designer. Aristotle
will be the proof-search executor only after Proshka returns one exact
source-locked task.

## Phase key

```yaml
GOAL_ID: Goal058_G1_G3_CofinalGroundTracking
PROOF_ADDRESS: RouteB.Goal058.G1G3.CofinalGroundTracking
FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
SOURCE_LOCK: literal ccmWeilMatFinite / sourceCCMComplexRow / Proposition59 family
ASSUMPTION_BUDGET: no gap, simplicity, tracking, RH, global positivity, or off-line-zero assumptions
PROMOTION_LEVEL: NONE
```

## Current pin

```text
repo: Malaeu/chen_q3
branch: rh_clean
base HEAD = origin/rh_clean = 6d7437e257c5101b06df9f5aff53dc8ff4984cc8
strict startup: P9_STRICT_PASS
Route B: CHECK: OK
G1: OPEN
G3: OPEN
```

The response must re-pin to the exact commit containing this request and the
preflight artifacts before giving the Aristotle prompt.

## Evidence to adjudicate

Read in this same commit:

1. `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SOURCE_ARCHITECTURE_RATIFICATION_2026-08-13.md`
2. `q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean`
3. `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_FULL_SOURCE_TRIAL_LINE_SCHUR_PREFLIGHT_REPORT_2026-08-13.md`
4. `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/PARITY_SECTOR_GROUND_TO_TRIAL_BOUND_ONE_CONTROL_CELL_REPORT_2026-08-12.md`
5. `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteSourceResidual.lean`
6. `q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean`
7. `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundLagrangeZeroSetBridge.lean`
8. `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean`
9. `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilParity.lean`

The preflight is kernel-checked:

```text
direct Lean: PASS
pinned 3x3 gap-collapse harness: PASS
lake build: PASS (7817 jobs)
q3_check: PASS
proof-hole/new-axiom scans: PASS
git diff --check: PASS
public theorem axioms: [propext, Classical.choice, Quot.sound] or none
```

## Exact facts now proved

### A. Missing literal real-even source carrier

The exact source row is

```lean
D0Pstar.sourceCCMComplexRow S i : CCMModeFinite i.N -> Complex
```

and is exactly unit. Current source binders do not supply a single unit phase
and a real reflection-even row `q` satisfying

```lean
forall j, phase * D0Pstar.sourceCCMComplexRow S i j = (q j : Complex).
```

Lean records this exact missing proposition as
`sourceCCMHasRealEvenPhase`, without assuming it. Lean proves:

- a unit phase realification preserves the exact unit Euclidean norm;
- exact real-row evenness would force exact reflection-evenness of the
  original complex source row;
- choosing phase one and `Re(row)` requires the original row to be exactly
  real coordinatewise.

Typed stop:

```text
GOAL058_SOURCE_COMPLEX_REAL_GROUND_CROSSWALK_MISMATCH
```

### B. Conditional P59 phase transport

On the exact `-N,...,N` carrier and source-locked pole order `n -> -n`, Lean
proves

```lean
proposition59CCMTransform L N q z =
  phase * proposition59CCMComplexTransform L N row z
```

under the exact coordinate realification equality. The existing
`-L*z/(2*pi)` coordinate is preserved. This does not produce the missing
phase-realification supplier.

### C. Exact full trial-line algebra

For `P = vecMulVec q q` and `Q = 1-P`, Lean proves `P*P=P` from
`q dot q=1` and the exact identity

```text
K = P*K*P + P*K*Q + Q*K*P + Q*K*Q.
```

It specializes to literal `ccmWeilMatFinite` and defines
`trialRayleigh`, `trialCoupling`, `evenComplementBlock`, `oddSectorBlock`, and
`oddTrialMass`. No positivity, gap, rate, or cofinal theorem is present.

### D. Scalar commutator candidate is exactly tautological

Lean proves

```text
q dot ((D*K - K*D) * q) = 0
```

for every real `q` whenever `D` and `K` are symmetric. Hence this observable
is zero for literal `ccmModeDiagFinite` and `ccmWeilMatFinite`, independently
of eigenvector status. An exact `CCMModeFinite 1` real-even non-eigenvector
plant verifies the same classification:

```text
LAG_SOURCE_TAUTOLOGICAL_ZERO
```

The independent pinned 3x3 harness additionally proves that the exact
rank-two commutator is compatible with a nonsimple kernel.

## Owner's requested move

Design one exceptionally precise Aristotle task that gives Aristotle a real
chance to find a non-obvious source-level connection. Do not ask Aristotle to
solve Goal 058 or RH. Ask it to prove exactly one bounded theorem (or return an
honest typed stop) whose truth can be checked by Lean in the present project.

The task may be difficult and structurally clever, but its conclusion must be
strong enough to materially reduce one of the two current walls:

```text
G1 = uniform literal CCM spectral-gap source
G3 = same-family/cofinal ground-to-trial tracking source
```

## Candidate classes Proshka must compare

Proshka must compare at least these four and may add one better class:

1. `COMPLEX_HERMITIAN_TRIAL_LINE`
   - avoid forcing the complex source row through an unavailable real-even
     carrier;
   - formulate a Hermitian rank-one projection with `vecMulVec q (star q)`;
   - specify the exact bridge, if any, to the real Proposition-59 ground row;
   - reject it if the bridge merely renames G3.

2. `SOURCE_REALIFICATION_THEOREM`
   - attempt a theorem deriving a common global phase and reflection relation
     from the literal prolate / `E_star` definitions;
   - identify the exact missing pointwise reality/conjugation binder;
   - reject it if the conclusion is not derivable from current fields.

3. `NONSCALAR_COMMUTATOR_OR_SCHUR_IDENTITY`
   - replace the killed scalar expectation by an exact vector-, block-, norm-,
     or bilinear-valued identity that survives a real-even non-eigenvector;
   - it must contain new source information, not just `(K-mu I)q` or a renamed
     complement-coercivity assumption.

4. `LITERAL_SOURCE_OBSTRUCTION_OR_NO_GO`
   - prove a bounded counterexample/no-go theorem showing that the current
     source contract cannot imply the desired realification or non-tautological
     observable;
   - this is acceptable falsification progress if it decisively rules out a
     family of future attempts.

## Required response format

Return exactly one primary:

```text
ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR
ARISTOTLE_SOURCE_REALIFICATION
ARISTOTLE_NONSCALAR_SOURCE_OBSERVABLE
ARISTOTLE_SOURCE_NO_GO
NO_SOUND_ARISTOTLE_TASK_AVAILABLE
```

Then return a single authoritative attachment-ready prompt with these fields:

```yaml
TARGET_ID:
PRIMARY_CLASS:
PIN:
OWNED_FILE:
ALLOWED_IMPORTS:
FORBIDDEN_IMPORTS:
EXACT_INPUT_OBJECTS:
EXACT_BINDERS:
EXACT_THEOREM_HEAD:
REQUIRED_AUXILIARY_LEMMAS:
EXPECTED_OUTPUT:
SUCCESS_CODE:
TYPED_STOP_CODES:
AXIOM_GATE:
VALIDATION_COMMANDS:
```

The prompt must also include:

1. a plain-language mathematical interpretation of the theorem;
2. why it is not a renamed G1/G3 assumption;
3. exact existing declaration names Aristotle may consume;
4. one owned Lean file only;
5. no edits outside that file;
6. no `sorry`, `admit`, `exact?`, `native_decide`, new `axiom`, or `opaque`;
7. all required `#print axioms` heads;
8. at least four mandatory falsifiers, including:
   - wrong family;
   - hidden realification/parity;
   - commutator tautology;
   - circular gap or tracking premise;
9. exact validation through direct Lean, target build, full build, q3_check,
   forbidden-token scan, and diff check;
10. a strict evidence boundary: no G1/G3 close, route promotion, or RH claim.

## Judge's strongest-attack obligation

Before emitting the Aristotle prompt, Proshka must attack the selected theorem
for:

- binder non-derivability;
- wrong-family substitution;
- hidden real/even assumption;
- a statement true only because a scalar commutator vanishes;
- complement-coercivity or source-decay smuggled in as a hypothesis;
- finite-to-cofinal substitution;
- receiver relabeled as supplier.

If the proposed theorem fails this attack, return
`NO_SOUND_ARISTOTLE_TASK_AVAILABLE` rather than an attractive but circular
prompt.

## Execution boundary

Proshka designs and judges the prompt. Codex will independently byte-lock the
returned prompt, submit it through the current Aristotle workflow, download
the result, scan it, compile it, and integrate only hole-free source-faithful
proofs.

This request does not authorize any G1/G3 closure, Bus creation, route
promotion, PX claim, or RH claim.
