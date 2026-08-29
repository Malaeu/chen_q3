# WORKFLOW REFACTOR — BLOCK 0 REPORT

```yaml
schema: q3_workflow_refactor_block_report.v1
block: 0
status: DONE
date: 2026-08-29
scope: CONTROL_HOT_PATH_ONLY
mathematics_changed: false
control_semantics_changed: false
px_rh_claim: NOT_MADE
```

## CLOSES

- `REQUEST_HISTORY_PER_COMMIT_SUBPROCESS_EXPLOSION`
- `SPINE_DUPLICATE_VALIDATION_WITHIN_ONE_RUN`
- `WORKFLOW_BLOCK0_PERFORMANCE_BASELINE_MISSING`

## OPENS

- `WORKFLOW_BLOCK_A_DERIVED_ARTIFACT_DEPENDENCY_REGISTRY`
- Existing unrelated baseline debt remains visible:
  `CODEX_CURRENT_CLOSED_TEST_EXPECTS_ACTIVE`, missing `jsonschema` in the current
  repo venv, one unmigrated verdict, and one pending `docs/_inbox` file.

## Defect and repair

`validate_request_file_binding()` formerly walked every first-parent commit and
spawned one `git rev-parse <commit>:<path>` for each request-state. At the
2026-08-29 baseline this meant up to:

```text
2 request-state files × 3039 commits = 6078 Git subprocesses
```

The repair asks the same exact `commit:path` questions through one
`git cat-file --batch-check` process per request. The first-parent history is
read once per repository-gate run and shared by all request bindings.

This preserves the old semantics:

- exact first-parent order;
- the tree state of merge commits;
- missing/deleted paths;
- the first appearance when a blob later disappears and reappears;
- exact comparison with `request_introducing_commit`.

Line breaks in a filesystem path are rejected before entering the Git batch
protocol.

`spine.main()` formerly called `validate_p9a()`, then called it again through
`build_state()`, and could call it a third time through `write_outputs()`.
The same immutable validation object is now passed through state construction,
rendering, and writing inside one invocation. A separate invocation still
validates independently.

## Benchmarks on the real repository history

| Entry | Before | After | Result |
|---|---:|---:|---|
| `goal_runtime.py --json` | 68.41 s | 1.37 s | ~49.9× faster |
| `spine.py --stdout --reason session-start` | approximately 184 s to strict result | 1.09 s base render | duplicate validation removed |

Post-repair trace for `goal_runtime.py --json`:

- 104 total Git process starts across the complete physical-goal selector;
- exactly 1 first-parent `rev-list`;
- exactly 2 request-history `cat-file --batch-check` processes;
- no per-history-commit `rev-parse` loop.

The remaining `git show` calls belong to physical goal/answer validation and
are outside Block 0. They are now visible as a later optimization candidate,
not a blocker for the ≤5 s selector target.

## Validation

```text
python3 -m unittest \
  orchestrator.tests.test_signed_offline_semantic_attestation \
  orchestrator.tests.test_three_body_loop \
  orchestrator.tests.test_goal_runtime \
  orchestrator.tests.test_workflow_block0_hot_path

Ran 109 tests in 11.914s
OK
```

Additional gates:

- `python3 -m py_compile` on all changed Python modules: PASS.
- `git diff --check`: PASS.
- real `goal_runtime.py --json`: PASS, selected physical Goal 058 with the
  unchanged phase-key hash.
- real non-strict Spine render: PASS.

The broad `unittest discover` run is not used as a false green: it currently
has pre-existing environment/control drift unrelated to Block 0. The system
Python lacks `pytest` and `jsonschema`; the repo venv also lacks `jsonschema`;
and `test_codex_current_task` expects `CURRENT: ACTIVE` while the canonical
pointer is `CLOSED`. The complete applicable Control-v9, selector, and new
Block-0 suite above is green.

### Post-push canonical gate

After fast-forwarding the canonical dirty checkout and preserving all foreign
changes through autostash:

- combined applicable suite: **123 tests, OK**;
- canonical selector: **1.36 s**, same Goal 058 and phase-key hash;
- semantic refresh: PASS, receipt bound to commit `cbac53b5`;
- final strict Spine: **1.70 s**, `P9_STRICT_PASS`, semantic index PASS,
  tool manifest PASS, authority unchanged.

## Changed paths

- `orchestrator/three_body_loop.py`
- `orchestrator/spine.py`
- `orchestrator/tests/test_workflow_block0_hot_path.py`
- `docs/Codex/REPORT_2026-08-29_workflow_refactor_block0.md`

No Lean source, mathematical state, semantic quarantine state, Control policy,
tool manifest, Proshka transport, commit automation, or publication surface was
changed.
