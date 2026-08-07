# STATUS: CONDITIONAL — PROSHKA M2 RATIFIED AS CANONICAL; LOSSLESS LEGACY REGISTRY MATERIALIZATION OPEN

```yaml
PRIMARY: RATIFY_M2_CANONICAL_WITH_LOSSLESS_LEGACY_CROSSWALK
STATUS_CODE: COGNITIVE_OPERATOR_VOCABULARY_RATIFIED_IMPLEMENTATION_OPEN

PIN:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  HEAD: 7dbfb4317f2b07b0b82066d2f358ec6e6a5ce441
  VERIFIED: true

VERDICT: RATIFY_WITH_REPAIRS

CANONICAL_VOCABULARY:
  NAME: PROSHKA_M2
  FIELD: cognitive_operator_used
  COUNT: 8
  SOLE_CANONICAL_ENUM: true

LEGACY_VOCABULARY:
  NAME: LEGACY_CONTROL_ACTION
  FIELD: legacy_control_action
  COUNT: 9
  PRESERVE_DEFINITIONS_VERBATIM: true
  LIVE_WRITE_ALLOWED: false
  HISTORICAL_IMPORT_ALLOWED: true

CROSSWALK_CLASSES:
  - DIRECT_ALIAS
  - RELATED_NOT_EQUIVALENT
  - LEGACY_ONLY

DIRECT_ALIAS_COUNT: 2
RELATED_NOT_EQUIVALENT_COUNT: 2
LEGACY_ONLY_COUNT: 5

SILENT_REWRITE: FORBIDDEN
HISTORICAL_SOURCE_REWRITE: FORBIDDEN
OWNER_ACTION_REQUIRED: false
REPOSITORY_EDIT_PERFORMED: false
ARISTOTLE: NONE

ARSENAL_MANDATE: ACCEPTED
ARSENAL_USED:
  - C04_SAME_COORDINATES_TWO_LAWS

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PX_RH_CLAIM: NOT_MADE
```

## VERDICT

**Ratify Codex’s recommendation with one categorical repair:** the old CamelCase vocabulary is not a second strategy-operator enum. It is a frozen **control-action vocabulary**.

The current branch and pin are exact. The pin closes the physical Fourier receiver and leaves the route in `CHALLENGER / NOT_RH`, with Bus 010 void, Goal 055 held, and no PX/RH claim.   `[ABSTRACT][PAPER]`

The live Proshka protocol requires exactly one M2 operator from the eight-value SCREAMING_SNAKE enum after every nontrivial iteration.  `[ABSTRACT][PAPER]`

The legacy file defines nine different objects: some are strategy transformations, but others are loop controls, review calls, persistence actions, or executor-backend changes.  `[ABSTRACT][PAPER]`

The repository audit independently found zero literal overlap and exactly four semantically close pairs. It also found that the live verdict stream uses M2, while the legacy vocabulary has one historical writer and survives mainly through eight migrated failed-strategy records.  `[ABSTRACT][PAPER]`

## CANONICAL_ENUM

The sole canonical value of `cognitive_operator_used` must be one of:

```text
REPRESENTATION_SHIFT
COUNTEREXAMPLE_HUNT
DUALIZE
BOUNDARY_CASE
UNIT_AUDIT
MINIMAL_LEMMA
LITERATURE_BRIDGE
ABANDON_ROUTE
```

No CamelCase token is valid in this field.

These remain distinct from:

```text
PROGRESS_CLASS
TRY_/KILL_/RUN_ operative classes
exploration state
Proshka call class
legacy control action
```

## LEGACY_HANDLING

Preserve these nine values verbatim under the closed type `LEGACY_CONTROL_ACTION`:

```text
ContinueLocal
EscapeLoop
RepresentationShift
CertificateShift
CounterexampleSearch
RouteKill
ProshkaReview
MemoryConsolidation
ReceiverMinimize
```

Their definitions must remain available at the existing path:

```text
q3.lean.aristotle/COGNITIVE_OPERATORS.md
```

That path should become the versioned registry rather than being deleted or renamed. The audit explicitly warns that removing it would leave historical `knowledge.db` records uninterpretable.  `[ABSTRACT][PAPER]`

New live verdicts and M3 strategy-memory entries must not emit legacy values. Legacy values remain legal only as historical provenance under `legacy_control_action`.

## CROSSWALK

| Legacy value           | Class                    | Canonical relation     | Binding interpretation                                                                                                                                                   |
| ---------------------- | ------------------------ | ---------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `ContinueLocal`        | `LEGACY_ONLY`            | —                      | Executor continuation state, not a cognitive transformation.                                                                                                             |
| `EscapeLoop`           | `LEGACY_ONLY`            | —                      | Loop-control trigger. It requires a subsequent M2 choice; it is not itself that choice.                                                                                  |
| `RepresentationShift`  | `DIRECT_ALIAS`           | `REPRESENTATION_SHIFT` | Same strategy transformation; spelling and namespace differ.                                                                                                             |
| `CertificateShift`     | `LEGACY_ONLY`            | —                      | Specialized change of certificate backend. Mapping it to `REPRESENTATION_SHIFT` would erase whether the mathematical representation or only the proof transport changed. |
| `CounterexampleSearch` | `DIRECT_ALIAS`           | `COUNTEREXAMPLE_HUNT`  | Same falsification operation.                                                                                                                                            |
| `RouteKill`            | `RELATED_NOT_EQUIVALENT` | `ABANDON_ROUTE`        | Legacy action may kill one theorem shape or family and roll back; `ABANDON_ROUTE` terminates the active route at M2 scope.                                               |
| `ProshkaReview`        | `LEGACY_ONLY`            | —                      | Channel/call action, now governed by `DELEGATED_STRATEGIC_REVIEW` and `EXPLORATION_REVIEW`, not a reasoning operator.                                                    |
| `MemoryConsolidation`  | `LEGACY_ONLY`            | —                      | Persistence action after reasoning, not the reasoning operator itself.                                                                                                   |
| `ReceiverMinimize`     | `RELATED_NOT_EQUIVALENT` | `MINIMAL_LEMMA`        | Receiver minimization is one specialized application of minimal-lemma discipline, not its full meaning.                                                                  |

Thus only two mappings permit canonical query equivalence. The other two close pairs are navigational hints, never substitutions.

## MIGRATION_RULE

### Registry and control wiring

Keep `q3.lean.aristotle/COGNITIVE_OPERATORS.md` and upgrade it to:

```yaml
schema: q3_cognitive_operator_registry.v1
canonical_enum: PROSHKA_M2
legacy_enum: LEGACY_CONTROL_ACTION
crosswalk_classes:
  - DIRECT_ALIAS
  - RELATED_NOT_EQUIVALENT
  - LEGACY_ONLY
```

Add its path to the mandatory `docs/CODEX_CONTROL.md` reading path. `CODEX_CONTROL` is already the active semantic kernel for both executor bodies, but currently names none of the 17 tokens.  `[ABSTRACT][PAPER]`

Required fail-closed code:

```text
COGNITIVE_OPERATOR_REGISTRY_UNAVAILABLE_OR_INVALID
```

### Knowledge database

Add two dedicated tables rather than overloading the Arsenal `move` table:

```sql
cognitive_operator_registry (
  token,
  vocabulary,
  description,
  source_file,
  schema_version
)

cognitive_operator_crosswalk (
  legacy_token,
  relation,
  canonical_token,
  note
)
```

Expected row counts:

```text
registry: 17
crosswalk: 9
```

For the eight frozen failed-strategy records:

* preserve the original `escape_operator` token;
* add `kill_evidence(kind='legacy_control_action', ref=<raw token>)`;
* preserve any explicitly recorded `cognitive_operator_used` as a separate canonical fact;
* do not derive or overwrite a canonical operator from the crosswalk;
* do not rewrite `ACTIVE/FAILED_STRATEGIES.yaml`.

The existing migration currently embeds `escape_operator` in replacement prose while storing explicit `cognitive_operator_used` separately as evidence. That split should be made queryable, not collapsed.  `[ABSTRACT][PAPER]`

### Query semantics

```text
DIRECT_ALIAS:
  may be grouped with the canonical token only when a query explicitly requests
  direct aliases; always display the original token.

RELATED_NOT_EQUIVALENT:
  may be shown as “related to”; never counted or rewritten as canonical usage.

LEGACY_ONLY:
  exact-token retrieval only.
```

## FORBIDDEN_LOSSY_REWRITES

The following are control failures:

```text
CamelCase → SCREAMING_SNAKE by case conversion alone.

RouteKill → ABANDON_ROUTE as an automatic rewrite.

ReceiverMinimize → MINIMAL_LEMMA as an automatic rewrite.

CertificateShift → REPRESENTATION_SHIFT.

CertificateShift → MINIMAL_LEMMA.

ContinueLocal → MINIMAL_LEMMA.

EscapeLoop → ABANDON_ROUTE.

ProshkaReview → any M2 operator.

MemoryConsolidation → any M2 operator.

Merging escape_operator and cognitive_operator_used into one database field.

Deleting an original token after attaching a canonical alias.

Counting RELATED_NOT_EQUIVALENT rows as canonical operator usage.

Rewriting frozen source files to make historical data appear canonical.
```

## STRONGEST ATTACK

A single historical failed-strategy record can contain both:

```text
escape_operator: RepresentationShift
cognitive_operator_used: MINIMAL_LEMMA
```

and another can contain:

```text
escape_operator: ReceiverMinimize
cognitive_operator_used: MINIMAL_LEMMA
```

These are not duplicate spellings. They record two different layers: the executor’s escape/control action and Proshka’s selected M2 reasoning operator.  `[ABSTRACT][PAPER]`

Any one-column normalization would destroy this information. That is the decisive **C04** objection: the two vocabularies can look similar after forgetting their roles while remaining different in the control category.

## META CLOSEOUT

**What became smaller?**

```text
two competing operator enums
```

became:

```text
one canonical M2 enum
+ one frozen legacy control-action enum
+ one explicit lossless crosswalk.
```

**What was killed?**

Silent global normalization of all nine CamelCase tokens into M2.

**What must not be tried again?**

Do not infer the reasoning operator from an executor action. Preserve both when both are explicitly present.

**Current smallest named gap**

```text
COGNITIVE_OPERATOR_REGISTRY_NOT_MATERIALIZED
```

**Next cheapest decisive test**

Round-trip the two historical records containing both fields and verify that registry ingestion returns both original tokens unchanged.

**Memory entry**

```yaml
iteration:
  target: cognitive_operator_vocabulary
  status: PROGRESS
  failed_strategy: collapse_legacy_control_actions_into_m2
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: COGNITIVE_OPERATOR_REGISTRY_NOT_MATERIALIZED
  invariant_learned: reasoning_operator_and_executor_control_action_are_distinct_fields
  forbidden_future_move: silently_normalize_related_or_legacy_only_tokens
  next_decisive_test: dual_field_knowledge_db_round_trip
```

## CODEX DIRECTIVE

```yaml
EXECUTION_AUTHORIZED_NOW: false
REPOSITORY_EDIT_NOW: false
ARISTOTLE: NONE

NEXT_CONTROL_PLANE_MATERIALIZATION:
  NAME: COGNITIVE_OPERATOR_REGISTRY_V1
  OWNER_ACTION_REQUIRED: false

  REQUIRED_ARTIFACTS:
    - q3.lean.aristotle/COGNITIVE_OPERATORS.md
    - docs/CODEX_CONTROL.md
    - q3.lean.aristotle/aristotle_db/knowledge_schema.sql
    - orchestrator/kb.py
    - operator-registry validation tests

  REQUIRED_GATES:
    - exact canonical count 8
    - exact legacy count 9
    - exact crosswalk count 9
    - all new cognitive_operator_used values belong to M2
    - all historical legacy values remain byte-identifiable
    - dual-field failed-strategy records preserve both fields
    - RELATED_NOT_EQUIVALENT never auto-normalizes
    - knowledge.db integrity_check = ok
    - strict Spine rejects an unknown operator token

  SUCCESS:
    COGNITIVE_OPERATOR_REGISTRY_V1_MATERIALIZED_LOSSLESSLY

  STOP:
    COGNITIVE_OPERATOR_REGISTRY_LOSSY_MIGRATION
```
