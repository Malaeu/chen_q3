# Codex App native subagent playbook on Mac (2026-03-16)

## Status

Supporting playbook only.

This file standardizes how to run the project's native custom agents on macOS
without pretending that undocumented `codex exec --agent ...` forcing is
stable.

It does not replace `ACTIVE/AGENT_PROTOCOL.md`.
It is an operational helper for the existing file-based loop.

## Current truth

The project is already wired for native custom agents:

- `.codex/config.toml`
- `.codex/agents/q3-worker.toml`
- `.codex/agents/q3-researcher.toml`
- `.codex/agents/q3-lean-worker.toml`

Local smoke-test result:

- native custom-agent usage should be treated as an app / interactive CLI
  feature first;
- non-interactive `codex exec` is healthy, but explicit custom-agent forcing is
  not reliable enough to be our primary orchestration layer;
- the canonical contract still remains
  `request node -> report file -> orchestrator ingest`.

## Mac setup checklist

1. Open the repo root in Codex App:
   `/Users/emalam/Documents/GitHub/rh_lean_01_2026`
2. Confirm these files exist:
   - `.codex/config.toml`
   - `.codex/agents/q3-worker.toml`
   - `.codex/agents/q3-researcher.toml`
   - `.codex/agents/q3-lean-worker.toml`
3. Keep the main thread anchored to:
   - `q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md`
   - `q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md` if active
4. Prefer native subagent work from the app or interactive CLI thread.
5. In interactive CLI, use `/agent` when you need to inspect or switch between
   active agent threads.
6. Do not rely on non-interactive `codex exec` as the primary native
   subagent launch surface.

## Supported native roles

### `q3_worker`

Use for:

- one theorem/block request node;
- one exact artifact receiver;
- no frontier remapping.

### `q3_researcher`

Use for:

- one blocker;
- local oracle / semantic recall;
- one external sanity-check;
- short synthesis only.

### `q3_lean_worker`

Use for:

- one narrow Aristotle/Lean integration task;
- compile check;
- hole-free extraction only.

## Ready prompts

### Prompt A — `q3_worker` on active `P3`

```text
Use parallel subagents for the active phase.

Spawn one q3_worker for
q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/node.md.

Have it:
- read SESSION_ENTRY.md, PHASE_MONITOR.md, AGENT_PROTOCOL.md, the request node,
  and only the supporting files listed there;
- avoid remapping the whole project;
- write only to
  q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/report.md.

Wait for the worker and then summarize what changed in the report.
```

### Prompt B — `q3_researcher` for Door 2 groundwork

```text
Use parallel subagents for the active phase.

Spawn one q3_researcher for Door 2 groundwork on the current H-bridge route.

Have it:
- read q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md;
- read q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md;
- read q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md;
- read q3.lean.aristotle/docs/insights/h_bridge_three_doors_macro_map_2026_03_16.md;
- read q3.lean.aristotle/docs/insights/plus_plus_boundary_inventory_2026_03_15.md;
- read q3.lean.aristotle/docs/insights/suzuki_form_pair_bridge_2026_03_08.md;
- run only local oracle recall plus one external sanity-check on same-sign
  Toeplitz/Hankel or commutator support;
- return a short summary to the parent thread without remapping the whole
  project.

Wait for the worker and summarize the best literature-backed theorem shape for
Door 2.
```

## Monitoring flow

The intended flow remains:

1. parent/orchestrator keeps the active monitor current;
2. child reads the active monitor and, when present, the active request node;
3. child returns a narrow result;
4. orchestrator ingests the result into the canonical `report.md` and the
   relevant phase artifact.

Native subagents do not replace the file contract.
They only reduce prompt boilerplate.

## Fallback rule

If native app / interactive CLI spawn is unavailable or flaky, use a second
narrow `codex exec` process.

Critical rule:

- the child should return its final payload through stdout or
  `--output-last-message`;
- the orchestrator then writes the canonical `report.md`.

Do not treat child-direct-write as the primary non-interactive pattern.

## Why this playbook exists

The project already proved that the math loop and the file loop are worth
protecting.

So the correct operational stance is:

- native subagents where the platform supports them well;
- one narrow worker per blocker;
- file-based ingest remains canonical;
- no undocumented launch trick should become load-bearing.

## Minimal external docs

- Codex subagents:
  <https://developers.openai.com/codex/concepts/subagents>
- Codex CLI slash commands:
  <https://developers.openai.com/codex/cli/slash-commands>
- Codex app features:
  <https://developers.openai.com/codex/app/features>
- Codex config basics:
  <https://developers.openai.com/codex/config-basic>
