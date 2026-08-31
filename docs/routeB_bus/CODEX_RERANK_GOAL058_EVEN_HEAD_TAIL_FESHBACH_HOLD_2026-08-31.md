# Goal 058 rerank — even head/tail Feshbach

Date: 2026-08-31
Base: `f58c0f1ced43b6d177c93d17343890890da23e92`

```yaml
TASK_ID: GOAL058_INDEPENDENT_DEPENDENCY_ROOT_RERANK
BODY: CODEX
INDEPENDENT_REVIEW: CODEX_SUBAGENT
STATUS: HOLD
RESULT: HOLD_SELECTED_FERRERS_EVEN_HEAD_TAIL_FESHBACH_NO_SELECTED_SHIFT_PACKAGE
SELECTED_ROOT: SELECTED_FERRERS_EVEN_HEAD_TAIL_FESHBACH
NOVELTY_AXIS: SOURCE_DEFINED_EVEN_HEAD_TAIL_SCHUR_AT_SELECTED_RAYLEIGH_SHIFT
ROUTE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
```

## Decision

The next independent Goal 058 root is the even head/tail Feshbach
representation.  It is the highest-value remaining dependency root after the
current Satz9/Fuchs, parity-floor and weighted-residual shelves were killed.
It changes the representation rather than renaming the weighted-residual gap.

The root is not executable on the current shelf.  No Lean node is authorized.
The correct terminal state for this rerank is `HOLD`, not `TRY` and not a claim
that the mathematical target is false.

## Exact downstream position

The live tail consumer is
`selectedFerrersTrackedGroundTail_exists_cofinal_reindex_of_eventually_sectorFloors`.
It still requires, on one selected cofinal family:

1. an eventual literal trial-complement floor;
2. an eventual odd-sector floor;
3. an eventual finite-CCM residual/floor ratio below one.

The selected even-sector floor is an upstream dependency of the complement
floor.  Closing it alone would not silently discharge the odd floor or the
ratio.  Its value is that a successful even Feshbach theorem would reopen the
highest-value parity-sector route into the unchanged consumer.

## Rerank eliminations

- `GOAL056_CONSTRUCTIVE_SCHEDULE` is superseded at the current production
  consumer.  The selected W5 assembly already proves the projection-tail
  theorem on the fixed production schedule, and the live ground-tail consumer
  does not consume `SelectedProjectionTailDecay`.
- `RATIO_DIRECT` controls the finite CCM Rayleigh residual.  The banked
  Galerkin decay controls a different projection-minus-full residual and cannot
  be substituted for it.
- Reopening the odd Feshbach path first would repeat a fixed-shift head-sign
  wall.  The existing Goal 057 tail coercivity is real and uniform over
  `PairIndex`, but its public Schur target is fixed at `m = 13` and
  `c0 = 10^-58`; no adapter to the selected `a_k` exists.

## Shelf evidence

- `sourceWeilOddTailAmbientCoercive_explicit` proves explicit odd-tail
  coercivity for every `PairIndex`.
- `sourceWeilOddTargetFloorSchurComplement` uses the fixed shift
  `sourceWeilOddTargetFloor = 10^-58`.
- `SourceWeilOddTargetFloorSchurPositive13` is restricted to `m = 13` and all
  auxiliary `N`; its positivity is a receiver, not a proved certificate.
- `selectedFerrersFiniteCCMRayleigh P k` is the literal selected, cell-dependent
  shift required by Goal 058.
- No `SourceWeilEvenTail`, selected-even head synthesis, selected-shift Schur
  complement, or exact implication to the even-sector consumer exists in the
  live Route B tree.

The strongest attack is shift loss: positivity of `K - c0 I` does not imply
positivity of `K - a_k I`.  The loss is exactly `a_k - c0`; the shelf supplies
no eventual uniform upper control of this quantity, and the finite Schur-head
sign is independently open.

## Smallest named missing package

`SELECTED_FERRERS_EVEN_TAIL_COERCIVITY_AND_SCHUR_MARGIN_AT_EXACT_RAYLEIGH_SHIFT`

It must provide, on the precommitted selected schedule:

1. a source-defined reflection-even tail orthogonal to the exact even trial
   component;
2. a uniform tail lower bound for `K_k - a_k I`;
3. an exact finite head and coupling ledger in the same metric;
4. a positive Schur margin uniform eventually;
5. an exact implication to the selected even-sector floor used upstream of the
   unchanged ground-tail consumer.

Reentry requires this package or a strictly weaker direct-consumer theorem
with a proved implication.  A finite cell, the odd-tail theorem, a prolate
gap, the fixed `10^-58` shift, or the Galerkin residual is not reentry evidence.

## Closeout

This transaction performs no Lean edit, numerical probe, Aristotle submission,
Route promotion or RH claim.  Goal 058 remains open as mathematics, while the
current rerank transaction is terminally `HOLD` with one named reopen package.
