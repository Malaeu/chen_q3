# SYSTEM_SPEC — full-repo census of cycles, banks, rules (2026-08-05)

Companion to `docs/MEMORY_ARCHITECTURE_AUDIT_2026-08-05.md`. Built from a 3-agent whole-repo sweep
(pipelines/cycles · databanks/sensors · rules/transitions). Answers the owner's question: **where does
everything live, is it alive, and do we still need it or have we outgrown it?**

## Executive finding

The project passed through **8 eras**; each line-switch silently orphaned the contour just built. The
result is NOT one broken thing but three strata: a **live core**, a large **outgrown graveyard** (do not
resurrect), a smaller **needed-but-orphaned** set (rewire), plus **real bugs** (contradictory constants,
zombie monitors, stale pointers). The good news: the reunification core (Knowledge Spine + COGNITIVE_
GOVERNOR staleness sensor) already exists — it just lost its trigger and never got wired to the atlases,
cards, sensors, or litreview.

## The 8 eras (transition timeline)

| Era | When | Line | Orphaned at the NEXT switch |
|---|---|---|---|
| 1 | Jan 22–29 | projekt_2 / MatrixBridge / Toeplitz / RKHS | Jan tooling fleet (aristotle_dag_loop, monitor_server, refresh_status); root CLAUDE.md "Current Work" block never removed |
| 2 | Mar 20–Apr 11 | **H-bridge mainline** `T0→H-bridge→H4→RH` (STILL the official mainline) | ERA-1 decision-hook + semantic search index (frozen Apr 12, blind ever since) |
| 3 | May 4 | Route A (stillborn, 1 commit) | — |
| 4 | May 26–Jun 24 | **Step32→Step33** (233 commits, dominant) | **Jun 12/13 BIG FREEZE**: Obstruction/Trick/S5 atlases last curated, never updated; PHASE_MONITOR parked |
| 5 | Jul 10+ | **Route B challenger** (bus, 162 commits) | Step33 fleet+monitor left reading ACTIVE (zombie); atlases not wired into bus/Spine |
| 6 | Jul 30–31 | Conductor retired, Codex absorbs transport | autonomous-conductor loop orphaned ~1 day after birth; Knowledge Spine's trigger (conductor) died |
| 7 | Aug 4+ | **Arsenal / card-file** (CURRENT) | era-layers bolted onto CLAUDE.md/AGENTS.md, none removed → fragmentation |
| 8 | Aug 3–5 | CCM / M1-051 / 054 sectorcell (live work) | D0.7e.5a subtree terminally closed |

## Classification — the actionable part

### 🟢 ALIVE & KEEP (fed late-Jul/Aug, wired)
Knowledge Spine stack (`spine.py`→`SPINE_VIEW.md`, `KNOWLEDGE_SPINE.md`, **`COGNITIVE_GOVERNOR.md`** =
staleness sensor) + its 4 live sources (`FAILURE_ATLAS.json`, `FAILED_STRATEGIES.yaml`, `INSIGHTS.md`,
Proshka bus M3 verdicts) · ARSENAL trio (kernel v3 + cards + addendum/mandate) · `aristotle_proofs.db` ·
Route B Lamport bus `docs/routeB_bus/` (goals 001→054) · RB-0..RB-10 control plane (`routeb_status.py`,
`ROUTE_B_EXECUTION_*`) · `packet.py` (clipboard transport + Spine-ingest trigger) · litreview corpus (new).

### ⚰️ OUTGROWN → ARCHIVE (do NOT resurrect; just tag SUPERSEDED so they stop misleading)
- ERA-1 Aristotle tooling: `aristotle_dag_loop.py`, `monitor_server.py`+html, `refresh_status.py`/
  `update_status.py`, `KB/orchestrator.md` (v5.3), `self_improvement_loop.md` — superseded by Spine.
- `SPRINT_MONITOR.md` (status DONE), `PROOF_COMPILER_SEVEN_GATES` (folded into RB-0..RB-10),
  twolevel-ladder loop (`node.md` stamped "SUPERSEDED — DO NOT EXECUTE").
- **Autonomous-conductor loop** (`orchestrator/CONDUCTOR.md`, `sense.py`, `relay.py`, harvest/detect .js,
  `*_app.sh`) — role RETIRED 2026-07-30. Keep only `packet.py` + `spine.py`.
- `EXTERNAL_PIPELINE`/`RESEARCH_ORACLE` two-loop design — its own status says "stores initialized but
  empty"; aspirational, never populated.
- Duplicate trees: `KB/` (Feb-08 copy of `docs/`), `full/q3.lean.aristotle` parallel mirror, `SKILL 2.md`
  copies. Archive/de-dup.

### 🔌 NEEDED-BUT-ORPHANED → REWIRE (these are the real losses)
- **Knowledge Spine trigger** — documented as "run by conductor after each closed goal", but conductor
  retired. Re-anchor the trigger to goal-close (fits the budget batch-per-goal law).
- **Semantic search — DEAD, not just blind.** `.qmd_cache` has no materialized `q3_docs` corpus;
  `research_oracle.py` ×2 + `refresh_q3_docs.py` frozen Apr. Rebuild the index over Route B/arsenal/
  verdicts (audit P5). Root `scripts/research_oracle.py` points at the dead `full/` tree — fix path.
- **Curated atlases** (Obstruction/Trick/S5) — frozen Jun 12/13 but cited LIVE; 0 post-June objects in
  them. Snapshot-tag + wire the AUTOPSY→wall-map loop so a live wall map replaces them (audit P1+P2).
- **Sensor-tier frozen since Jan/Feb** — `PROOF_GRAPH.json`, `TAINT_GRAPH/TAINT_SOURCES.json`,
  `SORRY_FRONTIER.json`, `DEPS_TREE_MAIN.json`, `NUMERIC_CHECKS.json`, `ARISTOTLE_QUEUE.json`. These are
  real "where are the holes / where is the taint / what depends on what" gauges — **we've flown blind on
  these axes since January.** Decide per-gauge: revive (proof-graph, sorry-frontier, taint are genuinely
  useful under standard-triple discipline) vs archive (ARISTOTLE_QUEUE = manual-submit now).
- **litreview** (audit P8) — built Aug 3, referenced in ZERO discipline files. Wire the cite→verify→PDF→
  auto-REFERENCES rule.

### 🐞 REAL BUGS → FIX
1. **Constant drift (dangerous):** `c_*` = **1.5** (`q3.lean.aristotle/CLAUDE.md`) vs **11/10** (root
   CLAUDE.md) vs **1.1** live A3-floor. Three contradictory values of the Archimedean floor across live
   rule files. Pin ONE, fix the others. (This can silently corrupt reasoning.)
2. **Zombie monitors:** `PSD_STEP33_MONITOR.md` self-reports ACTIVE (dead since June); `PHASE_MONITOR.md`
   PARKED indefinitely but still advertises. Tag both DEAD/PARKED-CLOSED.
3. **11 stale pointers (live rule → frozen artifact):** canonical = `AGENTS.md:9` "Root atlas:
   Q3_OBSTRUCTION_ATLAS.md"; also README_SETUP (whole file, May-26 Step32), codex_prompts, step32/33
   skills, root CLAUDE.md "Current Work: MatrixBridge/projekt_2" + "Last updated 2026-01-22" stamp,
   SPINE_VIEW dangling OBSTRUCTION_ATLAS mention, WORKFLOW_CHECKLIST `full/` path.
4. **Naming-collision hazard:** control-plane "Rule A/Rule B" (RULE_INVENTORY_FIRST / RULE_SEND_
   DISCIPLINE) vs proof "Route A/Route B" — `..._RATIFIED_RULEA_REJECTED` filename invites confusion.

## How this feeds the reunification plan (audit doc P1–P8)

The audit's P1–P8 stand, refined by this census:
- **P1** grows: snapshot-tag not just 3 atlases but ALL outgrown/zombie artifacts + fix the 11 stale
  pointers + fix constant drift (bug #1 is urgent — do first).
- **P2** (AUTOPSY→wall-map) + **P4** (one SPINE_VIEW) now must also decide the frozen sensor-tier
  (proof-graph/taint/sorry-frontier revive-or-archive).
- **P3** auto-detect can reuse the ALREADY-LIVE `COGNITIVE_GOVERNOR` staleness sensor — extend it from
  "warn stale" to "raise NEW-FLAG when autopsies converge."
- **P5** semantic-search rebuild is bigger than thought (corpus never existed) but higher value.
- **P6** decision-consult = the batch-per-goal budget law (Proshka once per goal-close, local scans free).
- Everything routes through the one Knowledge Spine, re-triggered at goal-close.

## Deliverable status & flow
This SPEC + the memory audit doc = the whole-system map the owner asked for. Flow (budget-aware):
Mythos verifies BOTH docs (plan + spec) in one pass → then Proshka architects the unified contour in ONE
batch verdict (never fan multiple Proshka calls). No mechanism is deleted here; classification only.
CHALLENGER / NOT_RH, Bus 010 VOID, no route promotion.
