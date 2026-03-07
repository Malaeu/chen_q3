# Embedding Ingest Workflow

## Purpose

The embeddings database is a **fast recall layer**, not the source of truth.

Source of truth stays in:

- Lean files
- paper TeX
- control docs

The embeddings collection `q3_docs` should index only material that is
useful and sufficiently reviewed.

## Three-layer model

### 1. Raw inbox

Location:

- `docs/incoming_notes/`

Use this for:

- raw Proshka markdown
- chat exports
- unchecked long notes
- speculative idea dumps

These files are **not** embedded into `q3_docs`.

### 2. Reviewed notes

Location:

- `docs/reviewed_notes/`

Use this for:

- distilled, cross-checked extracts from the raw inbox
- file/lemma maps
- verified mathematical synthesis

These files **are** embedded into `q3_docs`.

### 3. Canonical project memory

Locations:

- `docs/INSIGHTS.md`
- `PROJECT_ORCHESTRATOR.md`
- `docs/PAPER_MAINLINE_TRACKER.md`
- `IMPLEMENTATION_PLAN.md`

These remain the main project memory and control plane.

## Workflow

1. Drop the raw markdown into `docs/incoming_notes/`.
2. Review it against live Lean / TeX / control docs.
3. Distill the reusable part into `docs/reviewed_notes/`.
4. If the result affects the active project state, also write a short synthesis into `docs/INSIGHTS.md`.
5. Rebuild embeddings:

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle
./scripts/refresh_q3_docs.py
```

6. Query the refreshed collection:

```bash
./scripts/research_oracle.py query "your blocker query" -c q3_docs -n 5
```

## Practical rule

Do **not** dump raw chats directly into the embeddings base.

Reason:

- they mix good insights with false claims,
- they often use stale notation,
- they pollute semantic recall,
- they make search noisier exactly where we need precision.

Instead:

- inbox for raw,
- reviewed notes for searchable memory,
- canonical docs for project state.
