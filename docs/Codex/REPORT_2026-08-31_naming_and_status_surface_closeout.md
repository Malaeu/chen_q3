# Naming and status-surface closeout

```yaml
date: 2026-08-31
task: docs/Codex/TASK_2026-08-31_naming_and_status_surface_closeout.md
base_head: abe6a74abe725c40bb941a1cb939e1ba999d1dee
branch: rh_clean
scope: CONTROL_PLANE_AND_LEAN_RENAME
mathematics_changed: false
proof_bodies_changed: false
route_b_rank: CHALLENGER
route_b_rh_status: NOT_RH
PX_RH_CLAIM: NOT_MADE
```

## Outcome

Blocks A-D are implemented. The misleading `RH_proven*` declaration names are
gone from live Lean declarations without aliases. The two buildable wrappers
retain the same axiom profile. The root `Clean/MainClean.lean` duplicate is now
registered as `LEGACY / BROKEN / BROKEN_BUILD`. The frozen Route B control
surface is explicitly historical, and the live checker enforces its marker
from the status-surface registry.

The Aristotle generator now resolves the repository root correctly, skips
files without `sorry` before parsing them, and excludes `Q3/Archive/` from the
active task queue. The owner accepted the resulting complete non-archive queue
refresh. The live queue contains exactly:

```text
axiom::Q3.prime_term_le_at_t_critical_axiom
sorry::Q3/Clean/MainClean.lean
```

Archived files remain searchable history but cannot mint active Aristotle
tasks.

## Block A — legacy export names

Renames:

```text
RH_proven       -> RH_of_legacyBroadConeAxioms_compat
RH_proven_clean -> RH_conditional_on_Gate_clean_broken
```

No compatibility alias remains. The delegation/proof bodies were not changed.
The existing `sorry` in both `MainClean.lean` copies remains deliberately
untouched because the module class is `LEGACY / BROKEN / BROKEN_BUILD`.

The pre-change and post-change `#print axioms` profile of both buildable
wrappers is identical:

```text
propext
Classical.choice
Q3.Weil_criterion
Q3.prime_term_le_at_t_critical_axiom
Quot.sound
```

`git grep -n "RH_proven" -- '*.lean'` now returns only the four dated
"Renamed from" docstring lines outside archive.

## Block B — module registry

`q3.lean.aristotle/Clean/MainClean.lean` is registered as the root duplicate of
`q3.lean.aristotle/Q3/Clean/MainClean.lean`, with the same legacy/broken class
and `BROKEN_BUILD` trait. Neither file was deleted or deduplicated.

## Block C — status surfaces

- `ROUTE_B_EXECUTION_CONTROL.md` retains its frozen body and now carries an
  explicit `HISTORICAL / selector_effect NONE / FROZEN_DAG_CONTRACT` marker.
- `SESSION_ENTRY.md` resolves to the tracked ACTIVE router and names master
  route 058 as the executable DAG.
- The v2 theorem contract and execution-control snapshot are described as
  historical; their still-binding discipline is preserved.
- The ratified addendum is referenced without rewriting its historical
  `TIP_AT_DRAFT` or its separate ratification/evidence pins.

## Block D — K1 checker

The status registry row for the historical execution-control surface carries
one nonempty `required_marker`. `routeb_status.py --check` reads path and marker
from that registry and returns exit 5 with
`STALE_MONITOR_MISSING_HISTORICAL_MARKER` when the marker is absent. It performs
no repair. The negative plant removed the marker temporarily, observed exit 5,
restored the exact bytes, and then observed `CHECK: OK`.

Because the status-surface registry is a closed input to the P5 state schema,
the schema and built-in validator were extended to admit `required_marker`
only on `HISTORICAL` rows. Poison tests reject an empty marker and a marker on a
non-historical row.

The same live P5 reconciliation retired six Mythos draft paths from the current
`foreign_worktree_denylist`. Commit `77e4a9a6` had already made those paths
intentional tracked repository content, so continuing to classify them as
foreign worktree debris made the closed P5 builder internally inconsistent.
This transaction updates the live registry, validator constants, source
receipts, generated project state, and generated views together. Immutable
historical P9/P10 migration receipts were not rewritten and retain their
original evidentiary meaning. The owner's end-to-end grant to continue the
closeout through a coherent, error-free commit and push covers this necessary
live-state repair; it does not authorize any historical-receipt rewrite.

## Generator repair and queue receipt

The first canonical refresh exposed a real generator defect: its former root
calculation scanned only `q3.lean.aristotle/`, while generated graph inputs are
repository-relative. The repair sets the repository root from the script
location, retains Q3-relative task paths, and adds an explicit archive filter.
Regression plants cover:

1. repository-root discovery;
2. no task from `Q3/Archive/`;
3. a live non-archive `sorry` remains queued.

The four generated graph files were retained because their changes are the
deterministic timestamp/input-hash/source-scan consequence of the accepted
refresh. No graph is proof authority.

## Verification

Passed:

- `env -u LD_LIBRARY_PATH bash scripts/q3_check.sh q3.lean.aristotle/Q3/MainTheorems.lean q3.lean.aristotle/MainTheorems.lean`;
- explicit Lean compilation of both buildable wrappers;
- `env -u LD_LIBRARY_PATH lake build Q3` — 8181/8181 jobs;
- generator tests — 3 passed;
- module-class registry tests — 19 tests plus 41 subtests passed;
- route-status targeted test — passed;
- `routeb_status.py --check` — `CHECK: OK`;
- D4 negative marker plant — expected exit 5, then restored `CHECK: OK`;
- import-firewall receipt refresh and check — passed;
- canonical P5 build and validation — passed;
- `git diff --check` — passed;
- semantic-index refresh — 3044 indexed documents, semantic plants passed;
- `specs_docs/session_start.sh` — `P9_STRICT_PASS`, exit 0.

The first complete `uv run pytest orchestrator/tests/` probe finished with
622 passed and 15 failed. Task-local failures exposed by that probe were then
repaired through the canonical builders: the import-firewall receipt, the P5
registry/schema digest, authoritative state hashes, and the obsolete live
six-path foreign-worktree denylist. The P5 builder and validator are now
coherent, and the targeted post-repair suite passes 66 tests. Failure families
from the original full-suite probe that are outside the recurring live gates
were:

- `docs/Codex/CURRENT.md` is owner-controlled and `CLOSED`, while its dedicated
  plant unconditionally expects `ACTIVE`;
- P7/P9/P10 migration tests replay immutable historical foreign-dirty receipts.
  The repository's Workflow Repair G report already classifies those migration
  checkers as non-recurring live-worktree invariants after the old dirty debt
  was removed;
- one root-artifact plant mutates the real Git index and is not dirty-worktree
  safe; one toolbelt invocation exceeded its fixed 15-second test timeout.

The live P5 conflict is resolved in this transaction. Historical P7/P9/P10
receipts remain unchanged; they are evidence of their original migrations, not
inputs to the current recurring-state validator.

The final complete-suite rerun finished with 627 passed, 93 subtests passed,
and 10 failed. All 10 failures belong to the already separated non-live
families above: one owner-controlled `CURRENT: CLOSED` expectation, one
historical P7 append-history replay, seven historical P9/P10 foreign-dirty
receipt replays, and one root-artifact test whose temporary descendant mutates
the real Git index and is not dirty-worktree safe. No targeted live-state,
generator, route-status, import-firewall, P5, Lean, or queue test failed.

## Honesty boundary

No theorem statement, import, proof body, axiom, Route/Goal object, verdict,
arsenal card, or mathematical execution state was changed. No Route B
promotion occurred. The result is repository-semantic cleanup only.

```text
PX_RH_CLAIM: NOT_MADE
```
