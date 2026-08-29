# WORKFLOW REFACTOR — BLOCKS C AND D

```yaml
status: DONE
blocks: [C, D]
closes:
  - PHASE_CLOSE_ENTRY_MISSING
  - ASSEMBLY_INSIGHT_CARD_DEBT_SILENT
opens: [WORKFLOW_BLOCK_E_ROUTEB_BUILD_COVERAGE]
```

`specs_docs/phase_close.py` is one fail-closed phase-close entry. It consumes
the Block-A evaluator, then invokes the continuous registered gates in stable
order, stops at the first failure, runs the existing blueprint check, and
emits one JSON receipt. It does not reimplement any gate. The original
all-`check_*.sh` discovery was repaired by Workflow Repair G: P9/P10 migration
checkers bind a historical foreign-dirty snapshot and are immutable transaction
receipts, not recurring live-worktree invariants.

The receipt always contains addressable non-READY assembly rows, changed-scope
insight debt, and card debt. These are manual semantic debts: the tool never
sets assembly `READY`, invents insight content, or upgrades mathematical status.

Validation: six dependency/session/phase plants PASS. A real read-only probe
reported all derived artifacts FRESH and 21 addressable assembly-review rows.
The isolated worktree lacks the gitignored EnvDump required by blueprint; the
final canonical gate must therefore run on the canonical checkout rather than
turn that absence into a false green.
