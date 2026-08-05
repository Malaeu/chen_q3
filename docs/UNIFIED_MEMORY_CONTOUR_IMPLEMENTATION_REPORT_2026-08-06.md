# Unified memory + behavior contour — implementation closeout

Date: 2026-08-06 (Europe/Berlin)

```yaml
PRIMARY: UNIFIED_MEMORY_CONTOUR_P1A_P7_MATERIALIZED_AND_PLANTED
BEHAVIOR_CONTROL: UNIFIED_BEHAVIOR_CONTROL_PHASE_CHAT_PLANTS_PASS
P9_STATUS: ACTIVE
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
RH_CLAIM: false
ARISTOTLE_SUBMISSION: NONE
TRACKED_LEAN_DIFF: NONE
COMMIT_OR_PUSH: NONE
```

## Materialized contour

- P1a/P1b: Mac gaps are resolved; stale pointer census is materialized; parked
  and closed monitors no longer advertise themselves as live selectors.
- P9+P6+P8: `docs/CODEX_CONTROL.md` is active; `AGENTS.md` and both
  `CLAUDE.md` files are thin pointers; the former executor addendum is
  superseded; the three channel kernels are registered and strict-validated.
- Phase chat: the six-field comparator continues the same chat across goals,
  restarts, elapsed time and site batons; a changed key closes/opens; FATAL
  closes immediately; a missing handle fails closed. Ordinary goal close makes
  zero Proshka calls. The only owner mathematical boundary is `PX_RH_CLAIM`.
- P2a/P2/P3: the closed AUTOPSY schema, live wall derivation, namewatch
  discriminator, coverage suppression and no-auto-promotion rule are wired into
  packet close validation, the sensor bundle, `observability.db` and Spine.
- P4: `orchestrator/spine.py` is the sole full refresh entrypoint and emits
  deterministic `SPINE_STATE.json`, `SPINE_VIEW.md` and `META_CORPUS.json`.
- P5: `q3_docs` now includes current Route B and canonical active-request
  Markdown. Large generated Lean payloads stay in exact `rg` search; compact
  Lean remains in semantic recall. The full curated index has 2120 Q3 files and
  11566 vectors.
- P7: meta-corpus is a derived registry of existing corpora and databases, not
  a new truth store and not a database merge.

## Live sensor result

```text
observability schema: 6
sources: 8, stale: 0, degraded: 1
Lean roots: 2
active Lean files: 3316
axiom rows: 10
sorry sites: 0
AUTOPSY events: 3 legacy / 0 structured
walls: 1
namewatch candidates: 0
numeric coverage: EMPTY_CONFIG / ZERO_COVERAGE
```

The single degraded source is deliberate numeric zero coverage, not a hidden
PASS. The three historical AUTOPSY lines remain `LEGACY_UNCLASSIFIED` and are
ineligible for namewatch.

## Semantic-index plants

All required queries pass through exact BM25 plus local vector recall:

- `IdentificationAt`: vector recall reaches current Route B material;
- `edge-sliver`: exact and vector recall reach current Route B material;
- `ActiveCenteredCoeffEntryHboxCert`: exact and vector recall reach the
  pre-switch Step33 monitor and compact Lean sources.

## Artifact-identity audit

The attached K6 criticism was correct about the duplicate roof outputs and the
Müntz address, and incorrect about a missing owner relay.

- tracked `RequestProject/Main.lean` count at `d3e8ac14`: 18; current on-disk
  count under `q3.lean.aristotle`: 19;
- selected roof work skeleton:
  `q3.lean.aristotle/aristotle_output/output-final_aristotle/RequestProject/Main.lean`,
  SHA-256 `d7fe57b57ae0d08bd474de6f283565168bac9e33dd55d6719289466c7065e90f`,
  549 lines, 15 literal `sorry` tokens, `supply_S2` at line 498;
- displaced candidate:
  `q3.lean.aristotle/aristotle_output/16535289-f016-4f62-bfbd-be83d826b4da/RequestProject/Main.lean`,
  SHA-256 `ae88cd93a52c69f4e440a2d9c46f543007a1d9b7f5fbe04c85ab8db6c536e895`,
  394 lines, 18 literal `sorry` tokens, `supply_S2` at line 346;
- canonical Müntz v3 source and its mirror are byte-identical at SHA-256
  `f4ea12e1497b37a809c27db35f95035111d0d126942ea8c7557ec435b0e3ebfd`.

The roof selection is `SELECTED_FOR_ROOF_WORK_NOT_PROOF_NOT_PROMOTED`; it does
not lift Goal 055, promote Route B or claim RH.

## Validation

```text
python3 -m unittest discover -s orchestrator/tests  -> 61 tests, OK
python3 orchestrator/spine.py --refresh --strict    -> P9_STRICT_PASS
two consecutive strict session-start builds         -> byte-identical 3-file hashes
knowledge.db PRAGMA integrity_check                  -> ok
observability.db PRAGMA integrity_check              -> ok
litreview_check.py                                   -> 67 rows / 46 PDFs / PASS
routeb_status.py --check                             -> CHECK: OK
git diff --check                                     -> PASS
tracked Lean diff                                    -> NONE
```

The remaining G2 certificate-data stop is operational/source-data work, not a
mathematical owner-choice boundary. The physical route state remains untouched.
