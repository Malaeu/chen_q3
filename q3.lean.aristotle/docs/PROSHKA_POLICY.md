# Proshka policy pointer

Status: current pointer only. Canonical behavior lives in
`docs/CODEX_CONTROL.md`; this file cannot weaken or duplicate it.

## Current contract

- Judge prompt: `docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md`.
- Consumer-first dependency rules:
  `docs/Codex/RESEARCH_DEPENDENCY_PROTOCOL.md`.
- Recheckable debt registry:
  `docs/routeB_bus/RECHECKABLE_RESEARCH_DEBTS.json`.
- Request selection and byte binding:
  `orchestrator/workflow_runtime.py review-plan`.
- Transport: one source-locked UTF-8 `.txt` in the existing living phase chat.

The request must start from the downstream consumer and weakest sufficient
interface. A named theorem is a candidate until necessity is pinned. Missing
source, derivation, bridge, formalization budget, or local progress creates
`RESEARCH_DEBT`; it does not prove mathematical death.

## Evidence packs

`scripts/build_proshka_brief.py` may assemble a read-only evidence pack. Its
output is not the authoritative request, not a dispatch payload, not a route
selector, and must not replace the `review-plan` attachment lifecycle.

## Historical surfaces

`PROSHKA_REQUEST_3.md`, `PROSHKA_REQUEST_4.md`, the January single-scale pack,
the old memory-pack symlinks, and `scripts/refresh_proshka_pack.sh` are archive
evidence only. No post-commit hook or refresh script makes them current.
