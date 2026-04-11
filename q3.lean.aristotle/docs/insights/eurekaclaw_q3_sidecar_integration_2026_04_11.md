# EurekaClaw Q3 sidecar integration (2026-04-11)

## Verdict

EurekaClaw is worth integrating into Q3, but only as a **local-first sidecar**
around the existing control-plane.

It should **not** replace:

- Codex as the active orchestrator;
- the file-based monitors in `ACTIVE/`;
- Aristotle as the external theorem-prover loop;
- Lean + `lake env lean` as the formal verification gate.

The right model is:

```text
Q3 control-plane (canonical)
  = Codex orchestrator + ACTIVE monitors + Aristotle + Lean

EurekaClaw (auxiliary sidecar)
  = survey / memory / theorem-mining / skill-draft / paper-draft layer
```

## Why it is actually useful here

Official docs make three capabilities especially relevant to Q3:

1. **Multi-agent pipeline + central artifact bus.**
   EurekaClaw is coordinated by a `MetaOrchestrator`, with artifacts shared via
   a `KnowledgeBus`. That is useful for long blocker attacks where literature,
   candidate lemmas, and failed routes need to stay synchronized.

2. **Persistent memory + theorem graph.**
   Its memory system includes persistent cross-run storage plus a theorem
   dependency graph and markdown insight memories. That fits our proof-tree
   style well: Q3 already thinks in addressed theorem packets and route
   branches, so a sidecar memory can help cluster old attempts instead of
   re-deriving them from scratch.

3. **Domain plugin + skill system.**
   EurekaClaw exposes a `DomainPlugin` layer for domain-specific tools, skills,
   and workflow hints. This is exactly where Q3-specific rules should live if
   we integrate it seriously.

## What it should do for Q3

The high-value uses are:

### 1. Blocker-focused literature lane

Use EurekaClaw to run narrow literature sessions for one explicit blocker, for
example:

- `D2g29` arithmetic endpoint;
- one exact Suzuki/Ford–Zaharescu/Landau–Gonek comparison;
- one Aristotle prompt design problem;
- one route-kill sanity check.

Expected output:

- short survey note;
- 3-10 candidate lemmas or reductions;
- one “keep / kill / backup” recommendation with citations.

### 2. Proof-tree memory lane

Q3 is already organized by addressed nodes like `D2g29b1`, `D2g29c4`,
`D2g29d1a`. EurekaClaw can store:

- node summaries;
- failed theorem shapes;
- reusable reductions;
- dependency links between theorem packets.

That is a natural fit for its knowledge-graph and memory layers.

### 3. Candidate-lemma mining lane

For a fixed theorem packet, the sidecar can propose:

- alternate decompositions;
- comparison lemmas from papers;
- likely sublemmas to send to Aristotle;
- minimal formalization targets.

This is useful precisely because Q3 needs many small, exact theorem-shaped
substeps.

### 4. Post-closure writing lane

Once a packet is closed, EurekaClaw is good for turning the result into:

- a polished explanatory note;
- a paper-style subsection draft;
- a literature-positioning summary.

That is genuinely valuable and does not threaten the canonical proof state.

## What it must never do in Q3

These are hard boundaries.

### 1. No canonical write-back

EurekaClaw must not directly edit:

- `ACTIVE/PHASE_MONITOR.md`;
- `ACTIVE/SPRINT_MONITOR.md`;
- `ACTIVE/graphs/ROUTE_KILL_REGISTRY.md`;
- Lean theorem files;
- `docs/INSIGHTS.md`.

It can emit drafts only. The local orchestrator ingests reviewed material.

### 2. No autonomous route decisions

Route-kill and route-reopen decisions stay in the main Q3 control-plane.
External sidecars can propose, but not decide.

### 3. No direct Lean trust

Even though EurekaClaw exposes a Lean4 verification tool in its docs, Q3
already has a stricter Aristotle + `lake env lean` loop. Any Lean artifact from
EurekaClaw should be treated as draft input and re-verified locally.

### 4. No uncontrolled self-learning into protocol

Its skill evolver is interesting, but for Q3 every distilled skill must be
reviewed before it becomes part of the real workflow.

## Recommended concrete integration shape

The right target is a Q3-specific domain plugin:

```text
q3_rh
```

### Plugin responsibilities

#### Workflow hint

Inject Q3-specific rules, including:

- addressed proof-tree discipline;
- killed parent => killed subtree by default;
- one blocker at a time;
- no mixing old RKHS and new A3_FLOOR kernels;
- Aristotle requests must be narrow and hole-checked;
- Lean integration is local and mandatory.

#### Tool wrappers

The plugin should expose wrappers around our existing local tools:

- `q3_oracle_query`
  calls `./scripts/research_oracle.py query ... -c q3_docs`
- `q3_branch_lookup`
  reads `ACTIVE/PHASE_MONITOR.md`, `PROJECT_ORCHESTRATOR.md`,
  and route registries in read-only mode
- `q3_aristotle_submit`
  prepares a narrow Aristotle request file but does not auto-send without
  explicit permission
- `q3_aristotle_poll`
  polls/downloads results and hole-checks them
- `q3_lean_check`
  runs `lake env lean <file>`
- `q3_note_emit`
  writes raw output to a staging area, not to canonical docs

#### Skills

Initial Q3 skill pack should include:

- proof-tree addressing;
- route-kill discipline;
- Aristotle narrow-prompt protocol;
- Lean hole scan protocol;
- insight synthesis format;
- exceptional/nonexceptional arithmetic split templates.

## Operational boundary

Use a strict staging boundary:

```text
EurekaClaw raw session output
    -> staging dir / incoming notes
    -> human/orchestrator review
    -> canonical ingest into Q3 docs
```

Recommended staging locations:

- `q3.lean.aristotle/docs/incoming_notes/`
- or an external directory under `~/.eurekaclaw/` with later manual import.

## Suggested rollout plan

### Phase 1 — zero-risk attachment

Do not install any repo hooks yet.

Just use EurekaClaw for:

- blocker-specific literature sweeps;
- candidate theorem packet generation;
- polished note drafting.

### Phase 2 — domain plugin

Create `q3_rh` with:

- workflow hint;
- read-only branch tools;
- local oracle wrapper;
- draft-only note emitter.

Still no canonical write-back.

### Phase 3 — Aristotle/Lean adapters

Add optional wrappers for:

- Aristotle prompt staging;
- result download;
- hole scan;
- `lake env lean`.

But keep final execution and acceptance under the existing Q3 workflow.

## Bottom line

EurekaClaw is **not** a replacement for Oracle, Aristotle, or Lean.

It is valuable because it can become a persistent local research exoskeleton
around Q3:

- better long-memory for branches and failed routes;
- cleaner literature-to-lemma pipeline;
- reusable domain skills;
- lower scaffolding cost on hard blockers.

So yes: it is worth connecting.

But the winning integration is **sidecar mode with hard ingestion boundaries**,
not “let it run the project by itself.”
