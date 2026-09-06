---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

Project workflow: `q3.lean.aristotle/PROJECT_WORKFLOW.md`
Aristotle skill (CLI-based): `~/.codex/skills/aristotle/`
Session entry (single): `SESSION_ENTRY.md`

Compat: `full/q3.lean.aristotle` is a symlink to `q3.lean.aristotle` for legacy docs.

Aristotle integration rules (project workflow):
- Activate venv before any Aristotle command: `source .venv/bin/activate`.
- Submit via `aristotle formalize <request.md>` for single-file requests, or `aristotle submit "..." --project-dir <dir>` when directory context is needed; check/download via the current Aristotle skill snippets.
- Always scan downloaded files for holes: `rg -n "sorry|exact\\?|admit" <file>`.
- Treat files with holes as drafts; extract only hole-free lemmas or use as structure guidance.
- Run `lake env lean <file>` after every integration to ensure the project still compiles.
- Keep new kernel (A3_FLOOR) and old RKHS results separated; do not mix proof strategies.
- When a lemma fails to integrate cleanly, revert its addition and request Aristotle iteration on that lemma only.
- Log proof status in the DB by re-importing with `aristotle_db/parse_lean.py` and update notes if a lemma is no longer conditional.
- Prefer small, targeted Aristotle requests with explicit lemma statements and no `exact?` or `sorry`.

Semantic search workflow (before tackling a new blocker):
- Define the exact target lemma/axiom and where it is wired in the chain.
- Run embedding search on our local index (3-5 queries, aim for ~75% confidence). Do not use mgrep/websearch.
- Embedding command (from `q3.lean.aristotle`): `./scripts/research_oracle.py query "keyword" -c q3_docs` (use `math_papers`/`zotero_lib` if indexed).
- Run external web search via the built-in web tool (not the `websearch` wrapper).
- Synthesize a 5-10 line plan with concrete file/lemma pointers.
- Record the synthesis in `q3.lean.aristotle/docs/INSIGHTS.md` and commit (label as in progress).
- Commit message format: check OS + branch first, then use `[Linux][<branch>] Message` or `[MacOS][<branch>] Message` (no sandbox tags).
  - OS check: `uname -s` → Linux/Darwin.
  - Branch check: `git rev-parse --abbrev-ref HEAD`.
  - Optional category suffix: `[Linux][<branch>][Docs] ...`
  - Windows is not supported in this repo.
- Implement; once resolved, update `docs/INSIGHTS.md` with the final result and any reusable lemma list.

Coordination (decision transparency):
- After asking me questions, always follow up with your own recommendation of the path
  you would take, aligned with our philosophy: fast, efficient, robust, step-by-step toward
  full formalization (Q3), or a credible alternative proof.

Tone (coordination note):
- Be a bit more эмоциональный and supportive in replies.
- Acknowledge good insights explicitly.
- Celebrate progress when we close steps.
- Keep precision, but add encouragement.

Documentation link map (entry points):

                      ┌─────────────────────────────────────┐
                      │           CLAUDE.md                 │
                      │      (auto-read entry point)        │
                      └──────────────┬──────────────────────┘
                                     │
            ┌────────────────────────┼────────────────────────┐
            │                        │                        │
            ▼                        ▼                        ▼

  ┌─────────────────┐    ┌─────────────────────┐    ┌──────────────────────┐
  │ PROJECT_        │    │ PHILOSOPHY_OF_      │    │ ARISTOTLE_PROMPT_     │
  │ ORCHESTRATOR.md │    │ PROOF.md            │    │ GUIDELINES.md         │
  │ (status/next)   │    │ (axiom rules)       │    │ (prompt policy)       │
  └────────┬────────┘    └─────────────────────┘    └──────────────────────┘
           │
           ├──► PROJECT_ASCII.md (diagram)
           ├──► PROJECT_WORKFLOW.md (checklist)
           ├──► docs/INSIGHTS.md (Proshka notes)
           └──► FORMALIZATION_STATS.md (metrics)

Closure: YES
- Start at CLAUDE.md -> navigate everywhere.
- Philosophy, Workflow, Aristotle guidance are all reachable.

Aristotle guidelines (links):

| Path | Content |
| --- | --- |
| ~/.codex/skills/aristotle/SKILL.md | Local Aristotle skill (CLI + workflow) |
| q3.lean.aristotle/aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md | Prompt policy for Q3 |
| q3.lean.aristotle/aristotle_input/project_ids.txt | All project UUIDs |
| ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md | Canonical workflow (single source) |

Project files (Q3):

| Path | Content |
| --- | --- |
| q3.lean.aristotle/PROJECT_ORCHESTRATOR.md | Current status, next step |
| q3.lean.aristotle/PHILOSOPHY_OF_PROOF.md | Axiom criteria |
| q3.lean.aristotle/TRICKS_LIBRARY.md | Tricks/notes |
| q3.lean.aristotle/docs/INSIGHTS.md | Accumulated insights |
