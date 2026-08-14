# Proshka verdict — accept Goal 058 G3 mode-four Hermitian negative-count stability repair

Date: `2026-08-14`

Capture: normalized from the completed response in the standing Proshka chat.
Natural reasoning time shown by the UI: `11m 28s`.

## Primary verdict

```yaml
STATUS: PROVED — ACCEPT REPAIRED LEAF
PRIMARY: ACCEPT_REPAIRED_NEGATIVE_COUNT_STABILITY
PRIMARY_COUNT: 1
REPAIRED_LEAF:
  theorem: mode4HermitianNegativeEigenvalueCount_eventually_eq_of_tendsto_of_det_ne_zero
  lean_sha256: e410ff104210aac32b6e71f93e41f335ca9fe813944ce7ffd3b15dbd61429793
  closeout_sha256: 0dce18ba241a7c1b2d3f9f9da3cf9e8bb09b0be102cc91c61fb8b6db466c8c70
  exact_public_head: PASS
  public_theorems: 1
  public_definitions: 0
  positive_dimension_binder_leaked: false
  plants: 5_OF_5_PASS
  axiom_gate: [propext, Classical.choice, Quot.sound]
  scope: ABSTRACT
  verifier: LEAN
COMMIT:
  isolated_two_file_commit_authorized: true
  push_origin_rh_clean_authorized: true
  exact_file_count: 2
  unrelated_files_forbidden: true
NEXT_BOUNDED_LEAF:
  id: G3_MODE4_BACKWARD_TAIL_SCHUR_APPROX_TENDSTO_LITERAL
  operative_class: TRY_FIXED_CARRIER_EXACT_TAIL_CONVERGENCE
  executor: CODEX_LOCAL
  Aristotle_authorized: false
  commit_authorized_in_next_transaction: false
  push_authorized_in_next_transaction: false
G1: OPEN
G3: OPEN
OFFSET_ZERO: NOT_PROVED
ENDPOINT_COUNTS_2_3: NOT_AVAILABLE
ROUTE_B_PROMOTION: false
RH_CLAIM: false
```

## Accepted transaction

The repair is accepted with the exact public theorem head, no leaked
`hK` binder, one public theorem, zero public definitions, five private plants,
and the standard-only axiom profile.

The authorized isolated commit contains exactly:

- `Q3/Proofs/RouteB/D0Mode4HermitianNegativeCountStability.lean`;
- `ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_MODE4_HERMITIAN_NEGATIVE_COUNT_STABILITY_CLOSEOUT_2026-08-14.md`.

Required gates are: exactly two staged files; unchanged accepted SHA-256
hashes; no Route, Bus, runtime, or protocol edits; after push,
`HEAD = origin/rh_clean` and the worktree is clean.

## Authorized next bounded leaf

```yaml
TARGET: G3_MODE4_BACKWARD_TAIL_SCHUR_APPROX_TENDSTO_LITERAL
OPERATIVE_CLASS: TRY_FIXED_CARRIER_EXACT_TAIL_CONVERGENCE
EXECUTION_ORDER:
  - commit and push the accepted repaired stability leaf
  - re-pin to the resulting clean HEAD = origin/rh_clean
  - execute only this bounded leaf
MODE:
  owned_Lean_files: 1
  reports: 1
  executor: CODEX_LOCAL
  Aristotle: false
  commit: false
  push: false
  Route_Bus_runtime_edits: false
OWNED_FILE: Q3/Proofs/RouteB/D0Mode4BackwardTailSchurConvergence.lean
REPORT: ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_MODE4_BACKWARD_TAIL_SCHUR_CONVERGENCE_REPORT_2026-08-14.md
DIRECT_IMPORT: Q3.Proofs.RouteB.D0Mode4HermitianNegativeCountStability
ADDITIONAL_DIRECT_Q3_IMPORTS: forbidden
PUBLIC_DEFINITIONS: 1
PUBLIC_THEOREMS: 2
```

The new object is only the exact fixed-carrier approximation obtained by
substituting the finite backward-tail approximant into the one literal
tail-dependent diagonal entry.  It must not be called the actual finite DLMF
Schur complement before the later finite-block/Haynsworth identity is proved.

The smallest open object is named
`Mode4BackwardTailSchurApproxTendstoLiteral`.  The next decisive test is the
exact `(0,0)` entry identity followed by entrywise lifting of
`mode4BackwardTail_tendsto_rightTailLimit`.

The generic stability leaf is confirmed.  The finite-to-literal inertia
crosswalk, offset zero, endpoint counts `2/3`, G1, G3, Route B promotion, and
RH remain open.
