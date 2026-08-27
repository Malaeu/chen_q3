# Pipeline Guide (Agents)

**Purpose:** One-page, no-surprises workflow for discovery → taint/risk → proof.
**Current status (1–3 lines):**
- qmd installed globally (bun), `q3_docs` collection indexed.
**Next action (1–2 lines):**
- Use this checklist at session start; update if tooling changes.
**Links (3–6):**
- `ACTIVE/pipeline/EXTERNAL_PIPELINE.md`
- `ACTIVE/pipeline/RESEARCH_ORACLE.md`
- `ACTIVE/pipeline/TAINT_ANALYSIS.md`
- `ACTIVE/graphs/PROOF_GRAPH.md`
- `ACTIVE/graphs/SORRY_FRONTIER.md`

---

## 0) Always start here (from repo root)

```bash
# Ensure qmd on PATH (bun global bin)
export PATH="$HOME/.bun/bin:$PATH"

# Sanity check
qmd status
```

If `qmd` is missing:
```bash
bun install -g https://github.com/tobi/qmd
```

If bun warns about blocked postinstall:
```bash
bun pm -g untrusted
```

---

## 1) Collections (qmd)

### Docs (project knowledge base)
```bash
./scripts/refresh_q3_docs.py
```

This rebuilds `q3_docs` as a curated live KB:
- control/workflow docs,
- active manuscript TeX,
- live Q3 Lean files,
- reviewed notes from `docs/reviewed_notes/`,
- excluding archives, transcript dumps, and heavy `PrimeCert` shards.

Incoming markdown workflow:
- raw chats / Proshka dumps / unchecked notes go to `docs/incoming_notes/`
- only reviewed distilled notes go to `docs/reviewed_notes/`
- raw inbox notes are not embedded directly

### Zotero export (.bib)
```bash
qmd collection add ./docs/Riemann --name riemann_lib --mask "*.bib"
qmd embed
```

### Literature (markdown papers)
```bash
qmd collection add full/q3.lean.aristotle/literature --name math_papers
qmd embed
```

### Zotero (full‑text cache → markdown)
```bash
./scripts/zotero_ingest.py --collection-name Riemann --include-children --limit 50 --write-index
./scripts/research_oracle.py ingest --path full/q3.lean.aristotle/literature/zotero \
  --collection zotero_lib --embed
```

### Zotero API mode (no sqlite locks)
```bash
./scripts/zotero_ingest.py --api-auto --collection-name Riemann --include-children --report-missing
```

Note: Zotero **local API is read‑only** for writes. Creating collections/notes
requires the **Zotero Web API** (api.zotero.org) with an API key.

Notes:
- `qmd embed` downloads models on first run.
- Embeddings are stored in `~/.cache/qmd`.
- If `q3_docs` feels stale after a large refactor, rerun
  `./scripts/refresh_q3_docs.py` before trusting semantic-search hits.

---

## 2) Research Oracle (qmd wrapper)

### Query docs (fast retrieval)
```bash
./scripts/research_oracle.py query "Szego-Bottcher bound" -c q3_docs
```
Default `query` is now a stable hybrid wrapper:

- `qmd search` for lexical/BM25 hits
- `qmd vsearch` for semantic hits
- sequential execution + fused ranking

Use `--mode qmd-query` only when you explicitly want the old heavy rerank path.

### Query literature (speculative edges)
```bash
./scripts/research_oracle.py query "Weil positivity criterion" -c math_papers
```

### Query Zotero library
```bash
./scripts/research_oracle.py query "Szego-Bottcher bound" -c zotero_lib
```

### Add speculative edge into graph
```bash
./scripts/research_oracle.py add-speculative "Szego-Bottcher constant < 4" \
  -c q3_docs \
  --target Q3.Proofs.A3_bridge_integrated \
  --top-k 3
```

This writes to:
- `ACTIVE/pipeline/EQUIVALENCE_GRAPH.json` (speculative by default)
- `ACTIVE/pipeline/PAPER_INDEX.json` (sources)

---

## 3) Taint + Risk (FRI-style)

```bash
./scripts/numeric_sanity_check.py --write-back
./scripts/build_taint_graph.py
./scripts/build_proof_graph.py
./scripts/build_sorry_frontier.py
```

Key outputs:
- `ACTIVE/graphs/TAINT_GRAPH.md` (bubble‑up status)
- `ACTIVE/graphs/PROOF_GRAPH.md` (main chain with taint/risk)
- `ACTIVE/graphs/SORRY_FRONTIER.md` (all sorries)

---

## 4) Agent decision rule (must follow)

1. **Never** work on VERIFIED/TAINTED/DOOMED nodes.
2. Work only on **lowest SORRY** nodes (no SORRY deps).
3. If numeric check fails → mark BROKEN and re‑route.
4. Speculative edges **do not** count until Lean stub exists.

---

## 5) Troubleshooting

- `qmd not found`: check PATH and bun global install.
- `embed` slow: first download ~300MB model; reruns are faster.
- If hybrid `query` still feels stale, refresh `q3_docs`; if you need direct lexical
  debugging, run raw `qmd search` manually.
