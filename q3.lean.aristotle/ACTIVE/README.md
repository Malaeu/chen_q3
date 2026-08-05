# ACTIVE hub

**Purpose:** Single entry point for live docs/links.  
**Current status:** Start at `ACTIVE/KNOWLEDGE_BASE.md`.  
**Next action:** Use reader flow in `ACTIVE/tree.md`.  
**Links:** `ACTIVE/KNOWLEDGE_BASE.md` · `ACTIVE/tree.md` · `ACTIVE/MAIN_CHAIN_DEPS.md`

---

This folder is a single entry point for frequently updated docs, databases, and scripts.
It uses symlinks so existing paths keep working.

## Quick links (symlinks)

- docs/            -> ../docs
- scripts/         -> ../scripts
- db/              -> ../aristotle_db
- input/           -> ../aristotle_input
- output/          -> ../aristotle_output
- orchestrator.md  -> ../PROJECT_ORCHESTRATOR.md
- philosophy.md    -> ../PHILOSOPHY_OF_PROOF.md
- insights.md      -> ../docs/INSIGHTS.md
- insights_index.md -> ../docs/insights/INDEX.md
- workflow.md      -> ../PROJECT_WORKFLOW.md
- chain_status.md  -> ../docs/CHAIN_STATUS.md
- KNOWLEDGE_BASE.md (this folder) — lightweight index + live facts
- MAIN_CHAIN_DEPS.md (this folder) — actual RH deps vs repo legacy
- tree.md (this folder) — navigation tree (dependencies at a glance)
- requests/ (this folder) — active + infra only (archive in `q3.lean.aristotle/archive/requests_2026_01_29`)

## Core folders (new layout)

- `ACTIVE/aristotle/` — Aristotle workflow + queue + Proshka links
- `ACTIVE/refs/` — maps/specs/architecture/legacy refs
- `ACTIVE/graphs/` — auto‑generated proof/taint/deps graphs
- `ACTIVE/pipeline/` — external pipeline + oracles + meta

## Stats update

- Run `./scripts/update_formalization_stats.sh` to refresh `FORMALIZATION_STATS.md`.
- Run `python3 orchestrator/sensors.py refresh` from the repository root to
  refresh the checked sensor bundle, observability database, and Spine.

## Proof-graph tools

- `python3 orchestrator/sensors.py refresh --dry-run` → build and validate without publication
- `python3 orchestrator/sensors.py refresh` → publish the full checked bundle
- `python3 orchestrator/sensors.py status` → read the current database projection
