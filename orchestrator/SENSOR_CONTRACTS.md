# Q3 Sensor Contracts

Status: `LIVE_WITH_NUMERIC_ZERO_COVERAGE`

The sensor tier is disposable observability. It locates source holes, import
boundaries, propagation, root/axiom structure, numeric evidence, and channel
timing. None of these rows is Lean truth or a durable mathematical decision.

## Source-to-database map

| Source | Generator and live input | What it means | `observability.db` mapping |
|---|---|---|---|
| `DEPS_TREE_MAIN.json` | `build_dependency_tree.py`; successful `lake env lean Q3/CheckAxioms.lean` | All `#print axioms` roots and their standard/project axiom dependencies; not the file DAG | `proof_root`, `axiom_dependency` |
| `SORRY_FRONTIER.json` | `build_sorry_frontier.py`; ripgrep candidates plus comment/string-aware verification and import closure | Exact active `sorry` sites and whether they are in a configured root closure | `sorry_site`, `proof_root`, `root_membership` |
| `TAINT_GRAPH.json` | `build_taint_graph.py`; fresh sorry frontier plus internal import graph | Direct source holes/import boundaries and transitive propagation. `NO_OBSERVED_ISSUE` is not a proof verdict | `file_state`, `import_edge`, `taint_edge`, `proof_root` |
| `TAINT_SOURCES.json` | same taint generator; derived in the same run | Transitive origin set explaining why a file is contaminated | `taint_root` |
| `PROOF_GRAPH.json` | `build_proof_graph.py`; fresh axiom inventory, taint graph, and alternative-path config | Compact root-to-axiom projection. A source-clean project axiom remains a project axiom | `proof_node` |
| `NUMERIC_CHECKS_REPORT.json` | `numeric_sanity_check.py`; explicit project-local command config | Reproducible finite diagnostics only. FAIL/TIMEOUT never become Lean failure, taint, DOOMED, or route kill | `numeric_check`; source health is `ZERO_COVERAGE` while config is empty |
| `PROSHKA_REASONING_TIME_LOG.md` | append-only operational ledger | Channel duration and no-interrupt/Answer-now observability | `proshka_run` |
| `AUTOPSY_MAP.json` | `build_autopsy_map.py`; canonical answer/verdict files plus the closed AUTOPSY schema | Structured dropped-shape events, live wall observations and non-promoting namewatch flags; legacy lines stay unclassified | `autopsy_event`, `wall_state`, `namewatch_candidate` |

## Refresh transaction

```bash
python3 orchestrator/sensors.py refresh --dry-run
python3 orchestrator/sensors.py refresh
python3 orchestrator/sensors.py status
```

`refresh` builds every generated source in a temporary workspace, checks that
all roots and file counts agree, verifies that numeric evidence has not entered
taint/proof authority, then publishes the bundle. Only after publication does
it atomically rebuild `observability.db` and regenerate Spine. A generator or
cross-source failure leaves the live bundle and database untouched.

## Current observed state (2026-08-05)

- two Lean roots; five axiom dependencies each: three standard and two project;
- 3316 active Lean files and 5544 internal import edges;
- zero active `sorry` sites and zero root-tainted files;
- one peripheral import boundary outside both root closures:
  `Q3/Proofs/Q_Lipschitz_Bridge.lean -> Q3.Clean.AxiomsTier1`;
- numeric runner is live but has `EMPTY_CONFIG / ZERO_COVERAGE`;
- raw observations may reach `knowledge.db` only through a reviewed compact
  belief-changing conclusion with provenance.
- legacy AUTOPSY lines are visible but ineligible; zero structured events is
  honest zero coverage, not a successful namewatch claim.
