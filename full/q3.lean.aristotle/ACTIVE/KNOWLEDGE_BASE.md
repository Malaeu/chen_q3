# Knowledge Base (index + live facts)

**Purpose:** Router for ACTIVE docs. Read this first, then follow links only as needed.
**Current status:** Main chain deps are fixed in `ACTIVE/MAIN_CHAIN_DEPS.md` (authoritative).
**Next action:** Go to `ACTIVE/orchestrator.md` for tasks, or `ACTIVE/MAIN_CHAIN_DEPS.md` for blockers.
**Links:** `ACTIVE/orchestrator.md` · `ACTIVE/MAIN_CHAIN_DEPS.md` · `ACTIVE/chain_status.md` · `ACTIVE/requests/INDEX.md`

--- 

Goal: lightweight, link-first map so agents pull only what they need.
Keep this file short. Put details in linked docs.

## 0) Start here (order matters)

1) `ACTIVE/orchestrator.md` — current status + next steps
2) `ACTIVE/chain_status.md` — single-scale chain summary
2.1) `ACTIVE/MAIN_CHAIN_DEPS.md` — **actual** RH dependencies vs repo legacy
3) `ACTIVE/insights.md` — live insights index (links only)
4) `ACTIVE/workflow.md` — workflow rules
5) `ACTIVE/tree.md` — navigation tree (what depends on what)
6) `ACTIVE/SPECS_INDEX.md` — curated spec pointers + constants checklist
7) `ACTIVE/Q3_BLOCK_MAP.md` — Lean ↔ paper block map
8) `ACTIVE/ERS_SUMMARY.md` — consolidated ERS legacy summary

Note: spec sources are legacy/background. For mainline decisions, return to
`ACTIVE/chain_status.md` and `ACTIVE/orchestrator.md`.

## 1) Canonical chain (single-scale t_critical)

- Mainline parameters:
  - `t_critical = 3/20`
  - base-atom cone with `tau = 0`
- Canonical summary: `ACTIVE/chain_status.md`
- Paper alignment audit (single-scale vs legacy): `ACTIVE/single_scale_paper_audit.md`
- Legacy two-scale index: `ACTIVE/legacy_two_scale_index.md`

## 2) Main-chain dependencies (authoritative)

Source of truth:
- `ACTIVE/MAIN_CHAIN_DEPS.md` (actual RH deps vs repo legacy)
- `Q3/CheckAxioms.lean` (prints the live dependency list)
- `ACTIVE/SORRY_FRONTIER.md` (current `sorry` list in Q3)
- `ACTIVE/TAINT_GRAPH.md` (FRI-style taint propagation)

## 3) Canonical docs (maps/specs)

- Proof maps:
  - `ACTIVE/proof_map.md`
  - `ACTIVE/proof_map_new_kernel.md`
- Paper ↔ Lean mapping:
  - `ACTIVE/paper_lean_mapping.md`
  - `ACTIVE/q3_pdf_structure.md`
  - `ACTIVE/q3_structure_mapping.md`
- Architecture/status:
  - `ACTIVE/architecture.md`
  - `ACTIVE/project_status.md`
  - `ACTIVE/axiom_closure_analysis.md`

## 4) Aristotle + Proshka

- Aristotle docs (RU):
  - `ACTIVE/aristotle.md`
  - `ACTIVE/aristotle_sandbox_guide.md`
- Proshka:
  - `ACTIVE/proshka_entrypoint.md`
  - `ACTIVE/proshka_memory_pack.md`
  - `PROSHKA_REQUEST_4.md` (single‑scale closure pack)
  - `ACTIVE/proshka_context_single_scale.md` (one‑file packed brief)
  - `scripts/build_proshka_brief.py` (pack builder)
  - `docs/PROSHKA_POLICY.md` (canonical set policy)
  - `ACTIVE/requests/INDEX.md` (request tree: why -> evidence -> decision -> request)

## 5) Stats update

- Script: `scripts/update_formalization_stats.sh`
- Output: `FORMALIZATION_STATS.md`

## 6) Knowledge base (external)

- `ACTIVE/aristotle_models_knowledge` — Aristotle model/training knowledge dump
- `ACTIVE/codex_agent_loop_notes.md` — Codex CLI agent loop notes (OpenAI blog)
- `ACTIVE/EXTERNAL_PIPELINE.md` — two‑loop pipeline (formal DAG + external literature)
- `ACTIVE/EXTERNAL_GRAPH_SCHEMA.md` — schema for external graphs + alignment
- `ACTIVE/TAINT_ANALYSIS.md` — FRI-style taint propagation rules
- `ACTIVE/RISK_MODEL.json` — risk aggregation + kill switch
- `ACTIVE/RESEARCH_ORACLE.md` — qmd-based semantic search wrapper
- `ACTIVE/PIPELINE_GUIDE.md` — end-to-end agent checklist

## 7) Editing policy (keep this stable)

- Add only links + 1–2 lines of context.
- Avoid duplicating content from linked docs.
- When a doc becomes obsolete, mark it inside that doc (do not delete).
