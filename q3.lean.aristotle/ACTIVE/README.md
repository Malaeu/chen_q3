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
- Run `./scripts/build_dependency_tree.py` to refresh `ACTIVE/graphs/DEPS_TREE_MAIN.md`.

## Proof-graph tools

- `./scripts/build_dependency_tree.py` → updates `ACTIVE/graphs/DEPS_TREE_MAIN.md`
- `./scripts/build_proof_graph.py` → updates `ACTIVE/graphs/PROOF_GRAPH.md`
- `./scripts/build_sorry_frontier.py` → updates `ACTIVE/graphs/SORRY_FRONTIER.md`
- `./scripts/build_taint_graph.py` → updates `ACTIVE/graphs/TAINT_GRAPH.md`
- `./scripts/numeric_sanity_check.py` → updates `ACTIVE/graphs/NUMERIC_CHECKS_REPORT.md`
