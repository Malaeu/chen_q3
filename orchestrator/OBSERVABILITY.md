# Q3 Observability Spine Adapter

```yaml
CONTROL_ID: Q3_OBSERVABILITY_ADAPTER
STATUS: LIVE_ADAPTER_DEPENDENCY_AWARE_NUMERIC_ZERO_COVERAGE
TRIGGER_OWNER: Codex
EXISTING_GATES:
  - MANUAL_OBSERVABILITY_REBUILD
  - SESSION_START_SPINE_READ
  - GOAL_CLOSE_AFTER_SENSOR_REFRESH
SPINE_WIRING: observability_snapshot
FAIL_CLOSED_CODE: OBSERVABILITY_SNAPSHOT_INVALID
DATABASE: q3.lean.aristotle/aristotle_db/observability.db
SCHEMA: q3.lean.aristotle/aristotle_db/observability_schema.sql
```

`observability.db` is one atomically rebuilt materialized view over current
sensor JSON and the Proshka reasoning-time ledger. It is deliberately separate
from both project truth layers:

- `knowledge.db` owns reviewed semantic decisions, kills, moves and closeouts;
- `aristotle_proofs.db` owns proof/artifact metadata;
- `observability.db` owns derived holes, dependencies, taint, numeric results,
  structured AUTOPSY/wall/namewatch rows and operational timing projections.

Raw observability rows never establish a proof, route decision, promotion, or
PX/RH claim. A sensor/timing observation may enter `knowledge.db` only as one
reviewed compact conclusion with provenance through an existing journal gate.

## Rebuild and read

```bash
python3 orchestrator/sensors.py refresh --dry-run
python3 orchestrator/sensors.py refresh
python3 orchestrator/sensors.py status
python3 orchestrator/observability.py rebuild
python3 orchestrator/observability.py sources
python3 orchestrator/observability.py summary
```

Rebuild writes a complete temporary database, runs SQLite integrity checking,
and atomically replaces the old snapshot. Missing inputs are recorded as stale
instead of being silently treated as empty. The source ledgers remain
canonical; the database can always be discarded and rebuilt.

The complete source contract and table mapping are in
`orchestrator/SENSOR_CONTRACTS.md`. Numeric health remains deliberately
degraded as `ZERO_COVERAGE` because its configuration contains no diagnostics.
A fresh empty report is never PASS. AUTOPSY observations are derived and never
auto-promote a wall or arsenal card.

The source layer keeps the complete 3316-file import graph while avoiding full
reads of heavy non-root `PrimeCert` payloads. Root closures and the explicit
live-supplier allowlist are always scanned transitively. Every omitted payload
is stored as `CONTENT_SCAN_SKIPPED_GENERATED_NONROOT`, never as green proof
evidence; policy drift fails the refresh before the database is replaced.
