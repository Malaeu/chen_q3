---
tags: [subagent, pipeline]
priority: high
last_updated: 2026-02-08
---

# Subagent Delegation Playbook (5.3)

When to delegate:
- You need parallel exploration (proof search vs doc scan vs code integration).
- A blocker requires external recall (embeddings + web tool) while you keep mainline state.
- A task is long-running (>45 min) and can be split into independent sub-tasks.

Roles to delegate:
- `research_oracle`: embedding + web search, returns 5–10 line synthesis + sources.
- `proof_checker`: Lean compile checks, isolates failing lemmas, reports minimal repro.
- `latex_writer`: updates or audits LaTeX docs in `full/` and aligns with Lean blocks.
- `data_cert_builder`: runs certificate scripts, produces Lean data files.

Rules:
- Always give explicit inputs/outputs (file paths, lemma names, success check).
- Require subagent to return a concise summary + diff pointers.
- Keep one “decision owner” (main agent) to merge results.
