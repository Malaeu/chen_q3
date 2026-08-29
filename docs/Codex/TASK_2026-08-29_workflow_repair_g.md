# TASK: Workflow Repair G — executable closed loop

```yaml
schema: q3_workflow_repair_g.v1
status: CLOSED
scope: CONTROL_AND_WORKFLOW_ONLY
source_commit: 78975474a3302bd5959ac413eaa74921f0a2ea55
owner_authorization: FULL_SCOPED_COMMIT_REBASE_PUSH
mathematics_changed: false
PX_RH_CLAIM: NOT_MADE
```

## Objective

Repair the gap between the Block-F report and the executable workflow. The
stateless front door must bind one physical goal, run one reusable startup
receipt, expose exact owned scope and writes, execute a verified close-node
transaction, and fail closed before any writer on red startup or missing
scope/event evidence.

Phase close must run the registered derived closure, gates, verdict migration,
scoped assembly debt, and publication-blueprint regeneration in that order.
Session start, session close, phase close, and workflow planning must consume
one dependency registry and one byte-bound current-worktree receipt contract.

## Acceptance

- `run --through close-node` executes registered commands; it is not an alias
  for `plan`.
- startup red, missing owned scope, missing attempt event, failed search,
  failed supplier preflight, failed kernel, and failed close writer all stop.
- the startup receipt binds HEAD, owned worktree bytes, goal, phase/control,
  semantic receipt, and request-ledger bytes and is reused inside the run.
- assembly debt is limited to the selected goal's `ASSEMBLY_CHAIN`.
- verdict migration is validated after write; blueprint is regenerated only
  after green gates and migration.
- continuous phase gates exclude the frozen P9/P10 transaction checkers whose
  receipts bind the historical foreign-dirty snapshot; those receipts remain
  immutable evidence and are not live worktree invariants.
- a successful generator receipt makes an immediate repeated close a no-op
  while remaining noncanonical and byte-bound.
- MAP contains no dynamic next-step verdict or retired commit/push authority.
- applicable unit plants, strict Control, phase close, and repository checks
  pass before scoped commit/rebase/push.

## Closeout

Closed by `REPORT_2026-08-29_workflow_repair_g.md`. Five non-READY rows remain
visible in the selected Goal-058 assembly chain; they are mathematical work,
not residual Workflow Repair G defects.
