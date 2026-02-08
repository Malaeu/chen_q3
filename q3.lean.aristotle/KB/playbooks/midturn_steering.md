---
tags: [steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# Mid‑Turn Steering Playbook

Use when the task drifts, assumptions are wrong, or new constraints appear.

Signals:
- New blocker discovered or compilation fails.
- The scope is larger than expected.
- A path is likely false‑for‑now.

Steering actions:
- Restate the target lemma or file in 1 line.
- Switch to a smaller subtask with a concrete success check.
- Ask for confirmation before destructive or wide changes.

Sample phrases (user-facing):
- "I see a blocker in <file>:<lemma>. I suggest we pivot to <narrow fix>. OK?"
- "Scope is larger than planned. I’ll split into A/B; want me to proceed with A now?"
- "This path looks false‑for‑now; I can log it and switch to the fallback. Confirm?"
