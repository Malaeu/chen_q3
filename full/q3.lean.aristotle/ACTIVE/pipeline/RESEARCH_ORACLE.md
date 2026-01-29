# Research Oracle (qmd)

**Purpose:** Local semantic search over markdown literature for speculative edges.
**Current status (1–3 lines):**
- Wrapper script available: `scripts/research_oracle.py`
**Next action (1–2 lines):**
- Add markdown literature and run first query → `add-speculative`.
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

## Ingest

```bash
./scripts/research_oracle.py ingest --embed
```

Ensure literature lives under `full/q3.lean.aristotle/literature/`.

### Zotero full‑text cache → markdown

```bash
./scripts/zotero_ingest.py --collection-name Riemann --include-children --limit 50 --write-index
./scripts/research_oracle.py ingest --path full/q3.lean.aristotle/literature/zotero \
  --collection zotero_lib --embed
```

For docs-only search, use the `q3_docs` collection:
```bash
./scripts/research_oracle.py query "keyword" -c q3_docs
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
- Speculative edges are **not** used by the planner until a Lean stub exists.
