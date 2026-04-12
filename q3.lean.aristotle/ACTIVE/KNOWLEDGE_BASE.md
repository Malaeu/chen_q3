# Knowledge Base (index + live facts)

**Purpose:** Router for ACTIVE docs. Read this first, then follow links only as needed.
**Current status:** Main chain deps are fixed in `ACTIVE/MAIN_CHAIN_DEPS.md` (authoritative).
**Next action:** Go to `ACTIVE/orchestrator.md` for tasks, or `ACTIVE/MAIN_CHAIN_DEPS.md` for blockers.
**Links:** `ACTIVE/orchestrator.md` · `ACTIVE/MAIN_CHAIN_DEPS.md` · `ACTIVE/chain_status.md` · `ACTIVE/requests/INDEX.md`

--- 

Goal: lightweight, link-first map so agents pull only what they need.
Keep this file short. Put details in linked docs.

## 0) Start here (order matters)

1) `ACTIVE/PHASE_MONITOR.md` — active post-sprint theorem/certificate phase if present
1.1) `ACTIVE/AGENT_PROTOCOL.md` — if a second agent is used in the active phase
2) `ACTIVE/SPRINT_MONITOR.md` — active sprint state if present
3) `ACTIVE/AGENT_PROTOCOL.md` — orchestrator/worker loop for parallel agent
4) `ACTIVE/orchestrator.md` — current status + next steps
5) `ACTIVE/chain_status.md` — single-scale chain summary
5.1) `ACTIVE/MAIN_CHAIN_DEPS.md` — **actual** RH dependencies vs repo legacy
6) `ACTIVE/insights.md` — live insights index (links only)
7) `ACTIVE/workflow.md` — workflow rules
8) `ACTIVE/tree.md` — navigation tree (what depends on what)
9) `ACTIVE/refs/SPECS_INDEX.md` — curated spec pointers + constants checklist
10) `ACTIVE/refs/Q3_BLOCK_MAP.md` — Lean ↔ paper block map
11) `ACTIVE/refs/ERS_SUMMARY.md` — consolidated ERS legacy summary

Note: spec sources are legacy/background. For mainline decisions, return to
`ACTIVE/chain_status.md` and `ACTIVE/orchestrator.md`.

## 1) Canonical chain (single-scale t_critical)

- Mainline parameters:
  - `t_critical = 3/20`
  - base-atom cone with `tau = 0`
- Canonical summary: `ACTIVE/chain_status.md`
- Paper alignment audit (single-scale vs legacy): `ACTIVE/refs/single_scale_paper_audit.md`
- Legacy two-scale index: `ACTIVE/refs/legacy_two_scale_index.md`

## 2) Main-chain dependencies (authoritative)

Source of truth:
- `ACTIVE/MAIN_CHAIN_DEPS.md` (actual RH deps vs repo legacy)
- `Q3/CheckAxioms.lean` (prints the live dependency list)
- `ACTIVE/graphs/SORRY_FRONTIER.md` (current `sorry` list in Q3)
- `ACTIVE/graphs/TAINT_GRAPH.md` (FRI-style taint propagation)

## 3) Canonical docs (maps/specs)

- Proof maps:
  - `ACTIVE/refs/proof_map.md`
  - `ACTIVE/refs/proof_map_new_kernel.md`
- Paper ↔ Lean mapping:
  - `ACTIVE/refs/paper_lean_mapping.md`
  - `ACTIVE/refs/q3_pdf_structure.md`
  - `ACTIVE/refs/q3_structure_mapping.md`
- Architecture/status:
  - `ACTIVE/refs/architecture.md`
  - `ACTIVE/refs/project_status.md`
  - `ACTIVE/refs/axiom_closure_analysis.md`

## 4) Aristotle + Proshka

- Aristotle docs (RU):
  - `ACTIVE/aristotle/aristotle.md`
  - `ACTIVE/aristotle/aristotle_sandbox_guide.md`
- Proshka:
  - `ACTIVE/aristotle/proshka_entrypoint.md`
  - `ACTIVE/aristotle/proshka_memory_pack.md`
  - `PROSHKA_REQUEST_4.md` (single‑scale closure pack)
  - `ACTIVE/aristotle/proshka_context_single_scale.md` (one‑file packed brief)
  - `scripts/build_proshka_brief.py` (pack builder)
  - `docs/PROSHKA_POLICY.md` (canonical set policy)
  - `ACTIVE/requests/INDEX.md` (request tree: why -> evidence -> decision -> request)

## 5) Stats update

- Script: `scripts/update_formalization_stats.sh`
- Output: `FORMALIZATION_STATS.md`

## 6) Knowledge base (external)

- `ACTIVE/aristotle/models_knowledge` — Aristotle model/training knowledge dump
- `ACTIVE/pipeline/codex_agent_loop_notes.md` — Codex CLI agent loop notes (OpenAI blog)
- `ACTIVE/pipeline/EXTERNAL_PIPELINE.md` — two‑loop pipeline (formal DAG + external literature)
- `ACTIVE/pipeline/EXTERNAL_GRAPH_SCHEMA.md` — schema for external graphs + alignment
- `ACTIVE/pipeline/TAINT_ANALYSIS.md` — FRI-style taint propagation rules
- `ACTIVE/pipeline/RISK_MODEL.json` — risk aggregation + kill switch
- `ACTIVE/pipeline/RESEARCH_ORACLE.md` — qmd-based semantic search wrapper
- `ACTIVE/pipeline/oracle_questions/INDEX.md` — журнал поисковых серий по адресам дерева
- `ACTIVE/pipeline/oracle_questions/BY_ADDRESS.md` — навигация вверх-вниз по адресам
- `ACTIVE/pipeline/oracle_questions/VOCAB_MAP.md` — адресный словарь сильных и пустых слов
- `ACTIVE/pipeline/PIPELINE_GUIDE.md` — end-to-end agent checklist
- `docs/EMBEDDING_INGEST_WORKFLOW.md` — raw markdown -> reviewed note -> embeddings workflow
- `docs/insights/erdos_minimum_overlap_repo_assessment_2026_03_07.md` — external
  Together AI repo assessment and collection wiring

## 7) Editing policy (keep this stable)

- Add only links + 1–2 lines of context.
- Avoid duplicating content from linked docs.
- When a doc becomes obsolete, mark it inside that doc (do not delete).

## 8) Embeddings + Knowledge Graphs (how we use)

- **Embeddings (fast recall):**
  - Raw markdown or zip goes first to `docs/incoming_notes/`.
  - Local skill for this loop:
    `/Users/emalam/.codex/skills/q3-note-ingest/SKILL.md`
  - Prepare it with `./scripts/ingest_incoming_notes.py prepare ...`.
  - Distilled reviewed extracts go to `docs/reviewed_notes/`.
  - Only reviewed notes marked `safe for embeddings: yes` enter `q3_docs`.
  - After review, archive the raw payload with `./scripts/ingest_incoming_notes.py archive ...`.
  - Refresh the live collection when the repo changed materially:
    `./scripts/refresh_q3_docs.py`
  - Перед новой серией oracle-search завести карточку:
    `python3 q3.lean.aristotle/scripts/oracle_questions.py new ...`
  - Run: `./scripts/research_oracle.py query "keyword" -c q3_docs`
  - For the external Together AI corpus:
    `./scripts/refresh_erdos_overlap_kb.py`
    then
    `./scripts/research_oracle.py query "keyword" -c erdos_minimum_overlap`
  - qmd operations are serialized through `.qmd_cache/qmd_ops.lock`; keep local
    semantic queries sequential.
  - Каждая серия запросов должна быть привязана к адресу дерева доказательства;
    killed address трактуется как killed subtree и в вопроснике тоже.
  - После серии обновить карточку вопроса, затем сделать синтез в `docs/INSIGHTS.md`.
  - Then write a 5–10 line synthesis into `docs/INSIGHTS.md` and add a short pointer
    in `ACTIVE/insights.md` (link only).
- **Knowledge graphs (dependency/taint):**
  - Use `ACTIVE/graphs/PROOF_GRAPH.md`, `ACTIVE/graphs/DEPS_TREE_MAIN.md`, `ACTIVE/graphs/TAINT_GRAPH.md`
    to see what actually blocks the main chain and what is safe to edit.
  - Before a new blocker: check the graph → confirm the exact lemma/axiom node →
    then use embeddings to avoid re‑doing solved work.

## 9) Where we park future work

- Long‑term: `docs/INSIGHTS.md` (full reasoning + decisions).
- Short‑term pointers: `ACTIVE/insights.md` (links only).
- Proshka requests: `ACTIVE/requests/INDEX.md` (why → evidence → decision → request).
