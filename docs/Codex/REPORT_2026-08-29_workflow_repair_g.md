# WORKFLOW REPAIR G — EXECUTABLE CLOSED LOOP

```yaml
status: DONE
scope: CONTROL_AND_WORKFLOW_ONLY
source_commit: 78975474a3302bd5959ac413eaa74921f0a2ea55
mathematics_changed: false
PX_RH_CLAIM: NOT_MADE
```

Workflow Repair G closes the gap between the Block-F plan compiler and an
executable node-close transaction. `orchestrator/workflow_runtime.py run
--through close-node` now consumes one byte-bound startup receipt, requires an
exact owned scope and attempt event, runs shelf search and supplier preflight,
optionally runs the registered kernel command, and only then calls the close
writer. Every failed prerequisite stops before downstream writes.

The startup receipt binds HEAD, current owned-worktree bytes, the physical goal,
Control and phase state, semantic attestation, request ledgers, tool registry,
and derived-artifact registry. Session start, session close, phase close, and
the unified runtime use the same dependency evaluator. Derived receipts bind
their exact input/output hashes and repair command; a command change invalidates
the receipt. The immediate repeated close is a no-op.

Phase close now performs the ordered transaction:

1. consumer-scoped derived repair;
2. continuous gates;
3. verdict migration and post-write dry-run validation;
4. publication-blueprint repair;
5. scoped manual-debt report.

The previous glob over every `scripts/check_*.sh` was not a valid recurring
gate set. Three P9/P10 migration checkers require a historical foreign-dirty
snapshot and fail after that old worktree debt is removed. Their committed
receipts remain immutable evidence, but they are not live worktree invariants.
The continuous set is arch-floor quarantine, axiom/build audit, import
firewall, portability, root-artifact classification, and semantic-quarantine
history successor.

Publication generation is now self-preparing. It hashes the complete local
Lean import closure of all 367 Route-B source modules, runs `lake query Q3` and
EnvDump only when that source fingerprint changes, and records the ignored
byte-bound receipt. The acceptance dump covered 367/367 modules and 3362
declarations with zero `sorryAx` and zero other non-standard axioms. The first
full dump was intentionally expensive; the immediate repeated prepare and
blueprint generation completed in 0.16 seconds.

Acceptance evidence:

- 124 workflow/control tests passed after all changes.
- Python compile checks, Bash syntax, tool-manifest validation, and `git diff
  --check` passed.
- the full Lean build completed successfully with 7821 jobs in this isolated
  checkout; the explicit Route-B library query covered 8181 jobs.
- all six continuous phase gates passed.
- verdict migration post-write dry-run reported zero new strategy rows and zero
  new verdict-kill rows; the write pass admitted the previously pending
  `VERDICT_CONTROL_V9_OWNER_ROOT_VERDICT_BRIDGE_2026_08_29` strategy and its
  evidence without duplicating an existing semantic row.
- the generated blueprint check passed: 69 rows, 22 green, 3 validation-only,
  18 open mathematics, and 26 unresolved exact-declaration receipts.
- phase-close reports exactly five non-READY rows for
  `REALZERO_GROUND_DIAGONAL_TO_XI` and no card or changed-scope insight debt.

MAP and the Route-B conductor skill no longer contain a dynamic next-step
verdict, retired browser-composer transport, or per-action commit authority.
No Lean theorem was changed, no mathematical row was promoted, and no RH claim
was made.
