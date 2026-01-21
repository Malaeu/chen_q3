@CLAUDE.md
Project workflow: `full/q3.lean.aristotle/PROJECT_WORKFLOW.md`
Aristotle skill (CLI-based): `~/.codex/skills/aristotle/`

Aristotle integration rules (project workflow):
- Activate venv before any Aristotle command: `source .venv/bin/activate`.
- Submit via `aristotle prove-from-file` and check/download via the Python API snippets in the Aristotle skill.
- Always scan downloaded files for holes: `rg -n "sorry|exact\\?" <file>`.
- Treat files with holes as drafts; extract only hole-free lemmas or use as structure guidance.
- Run `lake env lean <file>` after every integration to ensure the project still compiles.
- Keep new kernel (A3_FLOOR) and old RKHS results separated; do not mix proof strategies.
- When a lemma fails to integrate cleanly, revert its addition and request Aristotle iteration on that lemma only.
- Log proof status in the DB by re-importing with `aristotle_db/parse_lean.py` and update notes if a lemma is no longer conditional.
- Prefer small, targeted Aristotle requests with explicit lemma statements and no `exact?` or `sorry`.

Semantic search workflow (before tackling a new blocker):
- Define the exact target lemma/axiom and where it is wired in the chain.
- Run `q3search "query" -c` first (3-5 queries, aim for ~75% confidence). Do not run `mgrep watch` or `mgrep --sync`.
- Run `websearch "question"` for external confirmation or alternative proof ideas.
- Synthesize a 5-10 line plan with concrete file/lemma pointers.
- Record the synthesis in `full/q3.lean.aristotle/docs/INSIGHTS.md` and commit (label as in progress).
- Implement; once resolved, update `docs/INSIGHTS.md` with the final result and any reusable lemma list.

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
| /Users/emalam/.claude/skills/aristotle/skill.md | Full API documentation (~830 lines) |
| /Users/emalam/Documents/GitHub/chen_q3/full/q3.lean.aristotle/aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md | Prompt policy for Q3 |
| /Users/emalam/Documents/GitHub/chen_q3/full/q3.lean.aristotle/aristotle_input/project_ids.txt | All project UUIDs |
| /Users/emalam/Documents/GitHub/chen_q3/full/q3.lean.aristotle/ARISTOTLE_SANDBOX_GUIDE.md | Sandbox workflow |

Project files (Q3):

| Path | Content |
| --- | --- |
| /Users/emalam/Documents/GitHub/chen_q3/full/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md | Current status, next step |
| /Users/emalam/Documents/GitHub/chen_q3/full/q3.lean.aristotle/PHILOSOPHY_OF_PROOF.md | Axiom criteria |
| /Users/emalam/Documents/GitHub/chen_q3/full/q3.lean.aristotle/TRICKS_LIBRARY.md | Tricks/notes |
| /Users/emalam/Documents/GitHub/chen_q3/full/q3.lean.aristotle/docs/INSIGHTS.md | Accumulated insights |
