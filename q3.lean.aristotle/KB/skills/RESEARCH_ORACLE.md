---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# Research Oracle (qmd)

**Purpose:** Local fast-recall search over the curated Q3 KB and external markdown literature.
**Current status (1–3 lines):**
- Wrapper script available from `q3.lean.aristotle/`: `scripts/research_oracle.py`
**Next action (1–2 lines):**
- Refresh `q3_docs`, then run the blocker query on the current live KB.
**Links (3–6):**
- `ACTIVE/pipeline/RESEARCH_ORACLE.json`
- `ACTIVE/pipeline/EQUIVALENCE_GRAPH.json`
- `ACTIVE/pipeline/PAPER_INDEX.json`
- `ACTIVE/pipeline/EXTERNAL_GRAPH_SCHEMA.md`

---

## Install (qmd)

```bash
bun install -g https://github.com/tobi/qmd
```

If qmd is installed via bun, ensure `~/.bun/bin` is on PATH
or set `"qmd_command": "/home/<user>/.bun/bin/qmd"` in `RESEARCH_ORACLE.json`.

## Refresh `q3_docs`

```bash
./scripts/refresh_q3_docs.py
```

This rebuilds `q3_docs` from the current control docs, active TeX, and live Lean
files while excluding archives and heavy `PrimeCert` shards.

## Ingest literature

```bash
/Users/emalam/Documents/GitHub/rh_lean_01_2026/scripts/research_oracle.py ingest --embed
```

Ensure literature lives under `full/q3.lean.aristotle/literature/`.

### Zotero full‑text cache → markdown

```bash
./scripts/zotero_ingest.py --collection-name Riemann --include-children --limit 50 --write-index
./scripts/research_oracle.py ingest --path full/q3.lean.aristotle/literature/zotero \
  --collection zotero_lib --embed
```

For docs/mainline search, use the refreshed `q3_docs` collection:
```bash
./scripts/research_oracle.py query "keyword" -c q3_docs
```

This `query` path is the stable default:

- it runs `qmd search` (BM25) and `qmd vsearch` (vector search) sequentially;
- it merges them by reciprocal-rank fusion;
- it avoids the heavier direct `qmd query` expansion/rerank path.

If you really want the legacy heavy backend, call:
```bash
./scripts/research_oracle.py query "keyword" --mode qmd-query -c q3_docs
```

## Query

```bash
./scripts/research_oracle.py query "bounds for Szego-Bottcher constant"
```

## Add speculative edge

```bash
./scripts/research_oracle.py add-speculative "Szego-Bottcher constant < 4" \
  --target Q3.Proofs.A3_bridge_integrated \
  --top-k 3
```

## Notes

- Output is JSON with `docid`, `file`, `score`, `snippet`, etc.
- In wrapper mode `query`, results also include `rrf_score` and `sources`.
- Speculative edges are **not** used by the planner until a Lean stub exists.
- If `q3_docs` is older than the current refactor wave, refresh it before running a
  new blocker search.
