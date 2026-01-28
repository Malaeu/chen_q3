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
- stats.md         -> ../FORMALIZATION_STATS.md
- chain_status.md  -> ../docs/CHAIN_STATUS.md
- KNOWLEDGE_BASE.md (this folder) — lightweight index + live facts
- MAIN_CHAIN_DEPS.md (this folder) — actual RH deps vs repo legacy
- tree.md (this folder) — navigation tree (dependencies at a glance)
- SPECS_INDEX.md (this folder) — curated spec pointers + constants checklist
- Q3_BLOCK_MAP.md (this folder) — Lean ↔ paper block mapping
- ERS_SUMMARY.md (this folder) — consolidated ERS legacy summary
- PROBLEM_SOLVER_PROMPT_RU.md (this folder) — prompt for chain reconstruction
- problem_solver_prompt.md -> ../ACTIVE/PROBLEM_SOLVER_PROMPT_RU.md

## Maps / Specs / Architecture

- proof_map.md            -> ../PROOF_MAP.md
- proof_map_new_kernel.md -> ../PROOF_MAP_NEW_KERNEL.md
- paper_lean_mapping.md   -> ../PAPER_LEAN_MAPPING.md
- q3_pdf_structure.md     -> ../docs/Q3_PDF_STRUCTURE.md
- q3_structure_mapping.md -> ../docs/struktura_q3_with_mapping_toLEAN.md
- architecture.md         -> ../ARCHITECTURE.md
- project_status.md       -> ../PROJECT_STATUS.md
- proof_dossier_v4.md     -> ../PROOF_DOSSIER_V4.md
- axiom_closure_analysis.md -> ../docs/AXIOM_CLOSURE_ANALYSIS.md

## Aristotle (RU)

- aristotle_workflow.md     -> ../ACTIVE/ARISTOTLE_WORKFLOW.md
- proshka_entrypoint.md     -> ../docs/PROSHKA_ENTRYPOINT.md
- proshka_memory_pack.md    -> ../docs/PROSHKA_MEMORY_PACK.md

## Knowledge base (external docs)

- aristotle_models_knowledge -> ../../../docs/Как работают модели типа Аристотель и их тренировка

## External proof-graph pipeline

- EXTERNAL_PIPELINE.md (this folder) — two-loop workflow
- EXTERNAL_GRAPH_SCHEMA.md (this folder) — schema + invariants
- EQUIVALENCE_GRAPH.json (this folder) — external equivalence edges (speculative by default)
- PAPER_INDEX.json (this folder) — external source index
- FAILURE_ATLAS.json (this folder) — where external routes fail
- ALIGNMENT_MAP.json (this folder) — external ↔ Lean mapping
- TAINT_ANALYSIS.md (this folder) — FRI-style taint propagation
- RISK_MODEL.json (this folder) — risk aggregation + kill switch
- RESEARCH_ORACLE.md (this folder) — qmd wrapper + usage
- PIPELINE_GUIDE.md (this folder) — end-to-end agent checklist

## Imported specs (from external knowledge dir)

- spec_critical_constants_rh_q3.md
- spec_rh_q3_decomposition.md
- spec_formalizing_rh_insights.md
- spec_high_ers_constants.md

## Stats update

- Run `./scripts/update_formalization_stats.sh` to refresh `FORMALIZATION_STATS.md`.
- Run `./scripts/build_dependency_tree.py` to refresh `ACTIVE/DEPS_TREE_MAIN.md`.

## Proof-graph tools

- `./scripts/build_dependency_tree.py` → updates `ACTIVE/DEPS_TREE_MAIN.md`
- `./scripts/build_proof_graph.py` → updates `ACTIVE/PROOF_GRAPH.md`
- `./scripts/build_sorry_frontier.py` → updates `ACTIVE/SORRY_FRONTIER.md`
- `./scripts/build_taint_graph.py` → updates `ACTIVE/TAINT_GRAPH.md`
- `./scripts/numeric_sanity_check.py` → updates `ACTIVE/NUMERIC_CHECKS_REPORT.md`
