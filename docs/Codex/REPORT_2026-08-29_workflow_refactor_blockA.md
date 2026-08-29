# WORKFLOW REFACTOR — BLOCK A

```yaml
status: DONE
block: A
closes:
  - DUPLICATE_INVENTORY_STALENESS_DEFINITION
  - ROUTEB_ATOMS_STALENESS_UNDEFINED
  - NEEDS_CARDS_CONTRADICTION_INVISIBLE
opens:
  - WORKFLOW_BLOCK_B_SESSION_CLOSE
```

One data registry, `docs/cartographer/DERIVED_ARTIFACTS.yaml`, now declares the
three probe dependencies. One evaluator,
`orchestrator/dependency_registry.py`, proves freshness from committed Git
baselines plus committed and uncommitted input changes. It never uses mtime.

`session_start.sh` consumes this evaluator in report-only mode. Later close
consumers will use the same result and differ only in reaction.

Current real-tree result in the isolated clean worktree:

```text
routeb-inventory FRESH
routeb-atoms FRESH
litreview-needs-cards FRESH
```

The cards detector distinguishes an exact contradiction (`NEEDS_CARDS` names
an existing card) from honest `MANUAL_DEBT` without an exact binding. It never
guesses semantic source-to-card equivalence.

Validation: two adversarial fixtures PASS; `git diff --check` PASS; a second
status run performs no writes and returns the identical result.
