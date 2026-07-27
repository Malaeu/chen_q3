# GenericZeroTransfer PIN_HASH_DRIFT audit

## Pin

- Path: `q3.lean.aristotle/Q3/Proofs/RouteB/GenericZeroTransfer.lean`
- Pinned commit: `248c6c9e3995a56874fea3d3a2618445e8f7847d`
- Pinned SHA-256: `7ec141740def3c8b40edb8e1c85f480cd733660909577cba10ad60829820b77b`
- Changing commit: `ae5b000fbf20fa68099f35b42768f19ddea48451`
- Current SHA-256: `4385ec71f6af59f1b5432128cd9b708854182e1248efcc0c764dc6dcf71fcc63`
- Owner-sign: `PROSHKA_VERDICT_S1_ANCHOR_2026-07-27.md`

## Diff classification

`ae5b000fbf20fa68099f35b42768f19ddea48451` is the authorized goal-005
strip refactor.  The diff is substantive (`+53/-13`), but its scope is closed:

1. factor the old whole-plane zero-transfer theorem through a new local theorem
   taking `DifferentiableOn` and local nontriviality on the open convergence
   domain;
2. retain the old theorem name and signature as a compatibility wrapper;
3. add the strip-local `ZerosApproachOn` theorem consumed by the goal-005 roof;
4. add only the corresponding `#print axioms` checks.

`git diff` reports no later uncommitted modification of this Lean file.

## Verdict

`BENIGN_005_STRIP_LOCAL_REFACTOR`

Re-pin is authorized to
`4385ec71f6af59f1b5432128cd9b708854182e1248efcc0c764dc6dcf71fcc63`.
This audit does not change the Route B verdict: `CHALLENGER / NOT_RH`.
