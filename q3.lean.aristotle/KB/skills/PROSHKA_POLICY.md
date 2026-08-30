---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# Proshka policy pointer

Status: compatibility copy of `q3.lean.aristotle/docs/PROSHKA_POLICY.md`.
Canonical behavior lives in `docs/CODEX_CONTROL.md`.

Current judge/dependency sources are
`docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md`,
`docs/Codex/RESEARCH_DEPENDENCY_PROTOCOL.md`, and
`docs/routeB_bus/RECHECKABLE_RESEARCH_DEBTS.json`. Exact request selection and
transport use `workflow_runtime.py review-plan` plus one source-locked UTF-8
`.txt` in the existing living phase chat.

`scripts/build_proshka_brief.py` creates evidence only, never a request or front
door. January requests/packs and `refresh_proshka_pack.sh` are historical only.
