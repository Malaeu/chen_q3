# Autonomous review transport repair — 2026-08-30

## Defect

The unified workflow stopped before reviewer transport. Its compiled plan
hard-coded `CODEX_LINUX_ONLY`, asserted zero reviewer calls, and represented
scoped delivery only as permanently false. The Route B conductor repeated the
same prohibition. As a result, a valid byte-locked request could be prepared
and pushed while the active Codex body still asked the owner to perform the
final browser click.

## Repair

- `workflow_runtime.py review-plan` now validates the exact `.txt` bytes,
  UTF-8 decoding, final LF, expected SHA-256, request commit, committed Git blob,
  worktree Git blob, active phase and living-chat handle.
- Dispatch additionally binds the request and boundary IDs and requires the
  queue section to be exactly `OPEN`; `IN_REVIEW`, `ANSWERED`, `DROPPED` or a
  missing section fail closed against duplicate sends.
- A green plan names `CURRENT_CODEX_BODY` as transport owner and sets
  `repository_owner_confirmation_required=false`; mandatory host UI safety
  confirmation remains an external runtime boundary and is never bypassed.
- A plan remains distinct from delivery: only observation of the sent message,
  exact single attachment tile and natural reasoning supplies the receipt.
- The conductor now instructs Codex to execute the authorized same-chat upload
  and send itself. The controlling body remains forbidden in the composer, a
  fresh chat remains forbidden, and `Answer now` remains forbidden.
- Scoped commit/push is represented as a required post-green action under the
  existing goal grant, not as something permanently excluded from the loop.
- `session_start.sh` now parses request sections instead of looking only one
  line behind `STATUS: OPEN`; it distinguishes `OPEN` from `IN_REVIEW` and no
  longer reports an outstanding request as “all answered”.

The live UI audit also rejected an earlier false delivery claim: the ODDFLOOR
request was absent from the living chat even though a click had previously been
reported as successful. Its queue state therefore remains `OPEN`. Only the
observable sent message may trigger `OPEN -> IN_REVIEW`.

## Plants

The workflow runtime tests cover:

1. exact bytes + commit/blob + living-chat acceptance;
2. mutated worktree bytes rejection;
3. missing final LF rejection;
4. expected SHA mismatch rejection;
5. duplicate recorded boundary rejection;
6. no owner-confirmation regression;
7. host-neutral logical transport ownership;
8. plan/delivery separation.
9. startup visibility of `OPEN` versus `IN_REVIEW` review lifecycle.

## Boundary

This repair grants no Route promotion and makes no RH claim. It does not weaken
request/verdict binding, semantic quarantine, kernel gates or the one-living-chat
phase rule. `PX_RH_CLAIM` remains owner-only.
