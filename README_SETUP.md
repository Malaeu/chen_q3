# Q3 Codex Bootstrap

This repo contains a Codex Step32 workflow bootstrap:

- `AGENTS.md` for durable repo guidance.
- `Q3_OBSTRUCTION_ATLAS.md` for the current Step32 threat model.
- `.agents/skills/q3-step32-lean/SKILL.md` for reusable Step32 execution.
- `q3.lean.aristotle/ACTIVE/requests/step32_next_gate/node.md` for the active
  request.
- `scripts/q3_check.sh` for direct Lean and hole-marker validation.
- `codex_prompts/q3_step32_goal.md` for a reusable goal prompt.

The active request lives under `q3.lean.aristotle/ACTIVE/requests`, matching the
current project layout. Root-level `ACTIVE/requests` is not used for this
bootstrap.

## Run The Current Gate

Use the skill explicitly:

```text
$q3-step32-lean Execute q3.lean.aristotle/ACTIVE/requests/step32_next_gate/node.md
```

Or use the prompt in `codex_prompts/q3_step32_goal.md`.

## Validate

From the repo root:

```bash
scripts/q3_check.sh Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean
```

The current live gate is `ActiveCenteredCoeffEntryHboxCert`, not the older
`centeredBSplineArchIntegrand_translatedPacketSum_integrable` target.
