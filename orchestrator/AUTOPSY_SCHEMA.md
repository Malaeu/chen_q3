# Structured AUTOPSY and live wall-map contract

```yaml
CONTROL_ID: Q3_AUTOPSY_WALL_NAMEWATCH
STATUS: ACTIVE
TRIGGER_OWNER: Codex
EXISTING_GATES: [GOAL_CLOSE, VERDICT_MATERIALIZATION, SPINE_REFRESH]
SPINE_WIRING: autopsy_wall_map_and_namewatch
FAIL_CLOSED_CODE: AUTOPSY_SCHEMA_INVALID
```

Every `INCONCLUSIVE`, `WALL`, or `KILLED` result carries one or more lines:

```text
AUTOPSY: dropped=<AUTOPSY_TAG_V1>; note=<nonempty one-line text>
```

The closed tags are defined once in `docs/CODEX_CONTROL.md` and imported by
`scripts/build_autopsy_map.py`. A legacy free-text line is preserved as
`LEGACY_UNCLASSIFIED`; it is never auto-retagged and never enters namewatch.

Namewatch eligibility additionally requires a precommitted shape token at the
start of the note:

```text
AUTOPSY: dropped=COUPLING; note=shape=LINEAR_TO_QUADRATIC | exact explanation
```

The read-only generator requires the same `(tag, shape)` in at least two
distinct goals and two distinct fronts. It stays silent when an existing wall
or arsenal card covers the tag. A hit creates only `NEW_FLAG?`; it never mints
or promotes a card. Under the current authority rule, Codex and Proshka decide
promotion; the owner boundary remains only `PX_RH_CLAIM`.

Canonical hand-reviewed wall identities live in `orchestrator/WALL_REGISTRY.json`.
Generated events, wall observations and flags live in `observability.db` and
the derived Spine state. Reviewed durable conclusions enter `knowledge.db`
only through its explicit journal/kill interface.
