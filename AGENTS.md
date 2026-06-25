Project workflow: `q3.lean.aristotle/PROJECT_WORKFLOW.md`
Aristotle skill (CLI-based): `~/.codex/skills/aristotle/`
Oracle skill (advisory external reviewer): `~/.codex/skills/oracle/`
Session entry (single): `SESSION_ENTRY.md`

Compat: `full/q3.lean.aristotle` is a symlink to `q3.lean.aristotle` for legacy docs.

Codex self-config bootstrap:
- Root atlas: `Q3_OBSTRUCTION_ATLAS.md`.
- Repo skill: `.agents/skills/q3-psdpd-step33-bootstrap/SKILL.md`.
- Compatibility skill: `.agents/skills/q3-step32-lean/SKILL.md`.
- Active PSD Step33 monitor: `q3.lean.aristotle/ACTIVE/PSD_STEP33_MONITOR.md`.
- Active PSD Step33 request:
  `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/node.md`.
- Legacy Step32 request:
  `q3.lean.aristotle/ACTIVE/requests/step32_next_gate/node.md`.
- Validation helper: `scripts/q3_check.sh`.
- Current PSD Step33 live gate: entry hbox certificates around
  `ActiveCenteredCoeffEntryHboxCert`; do not route new work to the already
  closed Arch-integrability target or to the parked H1/PO3 monitor unless the
  user explicitly asks for H1 / PO3 / H-bridge / route-kill work.
- Step33 anti-swamp rule: the `(0,0)` direct-profile cert is a pilot only.
  Do not continue manual row-by-row or entry-by-entry scalar replay.  For
  PSD Step33A.1, prefer delta compression, compact-support live prime-shift
  filtering, and segment/live hbox receivers before generating scalar payloads.
- Git `untracked` means only "not tracked by Git"; these files may still be
  project files. Do not delete, stage, or describe them as foreign unless the
  current task explicitly requires it.

Aristotle integration rules (project workflow):
- Activate venv before any Aristotle command: `source .venv/bin/activate`.
- Submit via `aristotle prove-from-file` and check/download via the Python API snippets in the Aristotle skill.
- Always scan downloaded files for holes: `rg -n "sorry|exact\\?|admit" <file>`.
- Treat files with holes as drafts; extract only hole-free lemmas or use as structure guidance.
- Run `lake env lean <file>` after every integration to ensure the project still compiles.
- Keep new kernel (A3_FLOOR) and old RKHS results separated; do not mix proof strategies.
- When a lemma fails to integrate cleanly, revert its addition and request Aristotle iteration on that lemma only.
- Log proof status in the DB by re-importing with `aristotle_db/parse_lean.py` and update notes if a lemma is no longer conditional.
- Prefer small, targeted Aristotle requests with explicit lemma statements and no `exact?` or `sorry`.

Oracle advisory workflow:
- Use Oracle only as an external reviewer on hard blockers, not as a source of proof truth.
- Prefer `npx -y @steipete/oracle --dry-run summary --files-report ...` before any live run.
- Prefer `--render --copy` or browser mode for advisory review; API runs require explicit user consent because they can incur costs.
- Never attach secrets, `.env`, credentials, or unrelated large folders.
- Treat Oracle output like Proshka output: record useful theorem-shapes in `docs/INSIGHTS.md`, but accept only Lean-checked code, hole-free Aristotle output, or verified mathematics into the mainline.

Pro / Louise escalation protocol:
- Current project roles:
  - Codex is the local repo worker: edits Lean/docs/scripts, runs builds/checks,
    and writes exact blocker reports.
  - ChatGPT Pro / Louise is the route architect/reviewer: chooses theorem
    shape or next proof gate when there is a real fork.
- Codex must not assume automatic access to the Pro chat.  If the user
  attaches, pastes, or appshots the Pro chat, Codex may use it as context.
  Otherwise Codex must write a compact escalation block in the active report:
  If the current Codex Desktop session confirms that the in-app browser is open
  to the Pro/Louise chat, Codex should use Computer Use for route-review before
  changing strategy on a loop trap or real theorem-shape fork; if that browser
  context is absent, fall back to the report block below.

```md
## PRO_REVIEW_REQUEST

Route:
Current step:
Current theorem:
File:
Lean error / blocker:
Options:
A.
B.
C.
Codex recommendation:
Question for Louise:
```

- Use `PRO_REVIEW_REQUEST` when two routes are plausible, a theorem statement
  may be wrong, a monitor conflict appears, H1/PO3 and PSD Step33 routes
  conflict, or a generated payload shape is unclear.

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
- Communication hard rules:
  - Никогда не отвечать транслитом; только нормальный русский (кириллица).
  - Никогда не обращаться на "Вы"; всегда обращаться на "ты".

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
