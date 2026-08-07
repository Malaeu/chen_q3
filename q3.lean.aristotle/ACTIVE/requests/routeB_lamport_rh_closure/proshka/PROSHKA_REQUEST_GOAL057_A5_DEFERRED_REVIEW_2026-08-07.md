# PROSHKA REQUEST — Goal 057 A5 deferred R1/R4 and actual-numerator review

```yaml
STATUS: READY_TO_SEND
GOAL: 057
TRANSACTION: UNIFIED_CHAIN_R1_R4_AND_ACTUAL_NUMERATOR_DEFERRED_REVIEW
SELF_CONTAINED_WITH_ATTACHED_CONTEXT_PACK: true
CHAT_CONTINUITY: SAME_LIVING_CHAT
BATCH_BUDGET: EXACTLY_ONE
ANSWER_NOW_SHORTCUT: FORBIDDEN

REPO: Malaeu/chen_q3
BRANCH: rh_clean
HEAD_AND_ORIGIN: 21ff34778401d013b5a54a6d66b006e042ebb9da
WORKTREE_ARTIFACTS: UNCOMMITTED_BUT_BYTE_PINNED
CONTEXT_PACK: goal057_proshka_deferred_context.md
CONTEXT_PACK_SHA256: cf3c4d6d0438003b617c31eb82e05de8f1e5273393574e87dd60e225bfbdba28

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
G2_CCM: FROZEN
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 1. Exact source lock

| Object | SHA-256 |
|---|---|
| original unified-chain owner brief | `490f322e083a5f7ed37d0b3ad4a3ae03597962563b4bdc33eaeb5bc3e52046ff` |
| superseding CCM penalty verdict | `0642538f4fed8970dfa777949155d78d3b5c74eb9f464e9105770bf1f0096f72` |
| Goal 057 through A5, canon=mirror | `66d95c90e31f474e79486cc0eea7d0156c7e792a9033171cd9fa20d55bcb5bfa` |
| Phase 0 report | `135a1e45f6d7ca68ee7fda0c030fc0b66feb38e709154613dae6721ab234993b` |
| Phase 1 report | `5776807be33117f4d3fbb98e1a8a9b08cfd85932733fd8d0c9101253db1a1eae` |
| Phase 2 report | `40b645862ccc4173377f3718296458ce3aa594d0698a945ce2cc9167d33f347e` |
| capability receiver audit | `837117c64323cfeb72119a16449922dcc6ed2574dfdff6ad919732f2cbd8e3cd` |
| Phase 3 report | `4d85f32fd5837d2298c072afc75e4ec22b6638865356ac7c312288b8df895b2d` |
| Phase 3 script | `60ea1dab2d1d62aa386d69cb3885da4158ac727d2cfb76e2ce0c9e77bd7e1c29` |
| Phase 3 result | `dd60446849839256b08f8dd4cf78968987c501d7f196cdafffdd4b2f9640cb71` |

The attachment contains exact snapshots of all listed review inputs.  Do not treat the
uncommitted artifacts as remote-visible merely because HEAD equals origin; use their byte pins.

## 2. What is already settled

`R2 VERIFY_AND_BIND` is no longer open: Goal 056 Phase 4L supplied
`SelectedProjectionTailDecay`; the remaining 056q premise is
`SelectedTrialNormalizerBounded`.

`R3 RATIFY_PROBE` was superseded by and executed under the pinned CCM penalty verdict.
Its authorized scientific transaction is now complete:

```yaml
PHASE_0: PASS_SOURCE_CROSSWALK_AND_ARCH_REPRODUCTION
PHASE_1: CCM_CONTROL_CELL_CERT_INTERVAL_PASS
PHASE_2: CCM_FIXED_Q_BETA_N_INTERVAL_PROFILE_PASS
PHASE_2_CLASS: FIXED_Q_PROFILE_FINITE_POSITIVE_NOT_STABILIZED
PHASE_3: CCM_DELTA_RATE_PROFILE_FINITE_INTERVAL_PASS_RATE_UNRESOLVED
PHASE_3_RATE_CLASS: DELTA_RATE_UNRESOLVED
PHASE_3_INTERVAL_CELLS: 18/18_PASS
PHASE_3_INDEPENDENT_RUMP_CELLS: 3/3_PASS
PHASE_3_CONTROLLING_SECTOR: ODD_GROUND_AT_ALL_NINE_CELLS
PHASE_3_STABILIZED_M_VALUES: []
```

The precommitted `N=90 -> 120` relative midpoint drifts were:

```text
m=12: 0.09367920739081191
m=13: 0.13880987106120885
m=14: 0.16689570126707496
gate: <= 0.01
```

Therefore no `m` entered the slope fit.  The prolate scale remained a separate proxy.  The
actual trial numerator, `sigma_num`, and `log(numerator/Delta)` remain unavailable.

## 3. Existing proved receivers found by the capability layer

The repository contains and Lean-checks two previously unused sorry-free receivers:

1. `SectorIsolationRadius.sectorIsolationRadius_certificate` applies to each finite Phase-3
   cell with `epsilonPlus1=even_ground`, `epsilonPlus2=next_even`, and
   `epsilonMinus1=odd_ground`.  The odd clause binds everywhere and yields the positive
   finite radius `Delta/2`.
2. `PerturbativeTrueGapLower.true_gap_lower_of_abs_endpoint_perturbations` can consume exact
   endpoint-error bounds.  The JSON records Arb midpoint/radius payloads, but those become
   theorem inputs only after an exact Lean ball import.  A finite grid does not establish
   the filter-indexed eventual hypotheses, and Arb numerical radii are not a
   finite-to-continuum bridge.

The two counterexamples in `PerturbativeTrueGapLower.lean` remain load-bearing: do not drop
either endpoint bound or allow the errors to consume the model gap.

## 4. Required ruling R1 — AUDIT_CHAIN

Re-audit the original conditional chain S1–S5 after the resolved R2/R3 facts and the failed
Phase-3 stabilization gate.  Return exactly one operative class:

- `TRY_CHAIN_REPAIRED` with the exact repaired theorem statement and named remaining
  suppliers; or
- `KILL_CHAIN_AS_STATED` with the first invalid implication and a replacement target.

In particular decide whether the chain can remain a theorem with the actual-numerator and
finite-to-continuum bridges explicit as hypotheses, or whether the target itself must change
to a cluster projection/determinant statement.

## 5. Required ruling R4 — JUDGE_INTEGRITY

Judge whether the current source pins, independent solver, precision doubling, exclusion of
all unstabilized points, explicit proxy separation, and capability counterexamples provide
adequate planted-violation coverage for this phase.  Return one operative class:

- `RUN_JUDGE_INTEGRITY_ACCEPT_WITH_NAMED_NEXT_PLANT`;
- `TRY_JUDGE_INTEGRITY_REPAIR` with the exact missing plant; or
- `KILL_CURRENT_VERDICT_AS_UNDERCONTROLLED` with the verdict-changing defect.

Do not approve merely because all finite intervals are positive.  Attack the inference from
finite sectional gaps to an asymptotic or true-operator gap.

## 6. Required ruling RNUM — actual numerator source-target bridge

The smallest live scientific obstruction is not a missing numeric value; it is the absent
identity or one-sided inequality from a named source trial object to the exact Input-B
numerator consumed by the Route-B residual/gap receiver.

Return exactly one:

- `TRY_ACTUAL_NUMERATOR_BRIDGE`: name source object, target object, exact theorem statement,
  source file/paper location, normalization, carrier, and joint filter;
- `KILL_CURRENT_ACTUAL_NUMERATOR_BRIDGE`: give the exact type/object mismatch and name the
  replacement object or receiver; or
- `RUN_NUMERATOR_SOURCE_AUDIT_FIRST`: name a bounded audit whose success/failure decides
  between the preceding two classes.

The prolate deficit `m^(9/2) exp(-4*pi*m)` may not be substituted for the actual numerator
without an equality or a proved one-sided bridge.

## 7. Prediction fate and next child

Score the registered prediction

```text
P-DELTA-R: the effective sectional-gap rate is subcritical relative to the actual
trial-numerator rate after N-stabilization.
```

Codex recommendation is `UNSCORED_INSTRUMENT_UNREADY`: no sampled `m` passed the registered
stabilization gate and the actual numerator was unavailable.  Confirm this class or replace
it with a more precise non-retroactive score.

Then select exactly one shift-sized child, or explicitly return `NONE_BLOCKED` with the named
missing source.  The candidates are not pre-ranked:

- a new precommitted larger-`N` stabilization ladder;
- the bounded actual-numerator source audit/bridge;
- one exact R1 chain repair named by your ruling.

No child is executed, no Lean file is edited, and no Aristotle job is submitted inside this
review transaction.

## 8. Required response schema

```yaml
STATUS: <OPERATIVE_OR_BLOCKED>
OPERATIVE_CLASS: <TRY_|KILL_|RUN_...>

R1_AUDIT_CHAIN:
  ruling: <TRY_|KILL_...>
  exact_statement_or_first_invalid_implication: <text>
  named_remaining_suppliers: [<...>]

R4_JUDGE_INTEGRITY:
  ruling: <RUN_|TRY_|KILL_...>
  verdict_changer: <text-or-NONE>
  next_required_plant: <text-or-NONE>

RNUM_ACTUAL_NUMERATOR:
  ruling: <TRY_|KILL_|RUN_...>
  source_object: <exact-or-NONE>
  target_object: <exact-or-NONE>
  theorem_shape_or_audit: <exact text>
  source_pointer: <exact path/citation-or-NONE>

P_DELTA_R_SCORE: <UNSCORED_INSTRUMENT_UNREADY-or-correction>

FIRST_SHIFT_CHILD:
  selection: <one named child-or-NONE_BLOCKED>
  stop: <exact stop code>
  success: <exact success code>

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
G2_CCM: FROZEN
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE

iteration:
  target: <text>
  status: <text>
  failed_strategy: <text>
  cognitive_operator_used: <text>
  new_gap_name: <text>
  invariant_learned: <text>
  forbidden_future_move: <text>
  next_decisive_test: <text>
  progress_class: <text>
  route_score: <integer>
```

Return the verdict body only.  Do not assume authority to promote Route B or claim PX/RH.
