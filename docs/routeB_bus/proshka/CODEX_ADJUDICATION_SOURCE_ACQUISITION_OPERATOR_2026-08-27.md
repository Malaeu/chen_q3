# CODEX adjudication: historical `SOURCE_ACQUISITION` operator

```yaml
SCHEMA: q3_historical_cognitive_operator_adjudication.v1
STATUS: RATIFIED_HISTORICAL_RECEIPT_ONLY
ACTOR: CODEX
DATE: 2026-08-27
OWNER_AUTHORITY:
  kind: GOAL_SCOPED_OPERATIONAL_GRANT
  goal_thread: 01a041db-d153-7ca1-92ec-d021e86e0ac2
  scope: P3_THROUGH_P10_SEMANTIC_QUARANTINE_MIGRATION
  permits: [SCOPED_REPOSITORY_WRITES, SCOPED_COMMITS, PUSH_RH_CLEAN]
  excludes: [DELETE, FORCE_PUSH, REPOSITORY_SETTINGS, EXTERNAL_PUBLICATION, PX_RH_CLAIM]
SOURCE_OCCURRENCE:
  path: docs/routeB_bus/proshka/PROSHKA_VERDICT_OWNER_NEXT_STEP_WEIGHTED_DIRICHLET_AND_VITALI_LITERATURE_TRIAGE_2026-08-27.md
  blob: 8cc3bd491381030464d414bb6d391ae11db27b0a
  field: COGNITIVE_OPERATOR
  original_token: SOURCE_ACQUISITION
ADJUDICATION:
  relation: RELATED_NOT_EQUIVALENT
  related_canonical_token: LITERATURE_BRIDGE
  direct_alias: false
  live_vocabulary_extended: false
  normalization_allowed: false
  query_grouping_allowed: false
```

## Decision

`SOURCE_ACQUISITION` is preserved byte-for-byte as historical provenance in
the pinned source verdict. It is related to, but is not an alias for,
`LITERATURE_BRIDGE`.

The historical token names the acquisition and triage of candidate sources.
The canonical `LITERATURE_BRIDGE` operator has a stronger and narrower binding
role: it imports a primary-source theorem only after an explicit
source-to-project interface audit. Acquisition may end without a usable
theorem or adapter, so the two operations are not equivalent.

This adjudication does not alter the immutable source verdict, add a ninth live
Proshka M2 token, authorize new writes of `SOURCE_ACQUISITION`, or normalize
historical records. It authorizes exactly one receipt for the pinned occurrence
above. Any other occurrence is invalid under receipt schema v1 and requires an
explicit schema/version update plus a separately pinned adjudication.

The owner authorized autonomous scoped repository writes, commits, and pushes
through P10. Repairing this pre-existing control gate is the prerequisite for
that migration; it does not broaden the grant beyond the exclusions recorded
above.
