---
tags: [pipeline, steering, subagent]
priority: medium
last_updated: 2026-02-08
---

# Self Improvement Loop (Semi-Automatic)

Use this loop to keep KB useful without forcing full automation.
Trigger by command (`update kb`, `summarize learnings`) or when signal thresholds are reached.

## Trigger Conditions
- Long task finished (`>30 min`) with at least one non-trivial decision.
- The same error pattern appears `>=3` times in one session.
- Mainline status changed (`Q3/CheckAxioms.lean` output changed).
- User asks for post-mortem, synthesis, or context pack.

## Loop Steps
1. Capture result in 5-15 lines (`what changed`, `why`, `evidence`, `next`).
2. Write one insight file: `KB/insights/YYYY-MM-DD_short_title.md`.
3. Run refresh: `python3 q3.lean.aristotle/scripts/kb_refresh.py`.
4. Verify status files reflect current reality:
   - `KB/SESSION_STATE.md`
   - `KB/axioms/AXIOM_REGISTRY.md`
   - `KB/maps/open_lemmas.md`
5. If drift/noise is detected, propose `run self-diagnosis`.

## Error Promotion Rule
If one mistake repeats `>=3` times:
- Add one concise rule to `KB/ERRORS_DESTROYER.md`, or
- Add one focused how-to under `KB/skills/` if the fix is procedural.

## Output Contract (after each loop run)
- `Delta`: 2-5 bullets on what changed.
- `Evidence`: commands/files used for verification.
- `Risk`: one remaining risk or unknown.
- `Next`: one concrete next step with success check.
