---
tags: [pipeline, subagent]
priority: medium
last_updated: 2026-02-08
---

# Long‑Task Template (>1h)

Structure:
1) Objective (1–2 lines, include success check)
2) Breakdown (3–7 bullets, each with file/lemma/script)
3) Checkpoints (what to verify after each step)
4) Risks (top 2 failure modes)
5) State save (what to write to `KB/SESSION_STATE.md` + new insight file)

Checkpoint examples:
- `lake env lean <file>` succeeds
- `./scripts/check_axioms.sh` clean
- `rg -n "sorry|admit|exact\?" <file>` empty
