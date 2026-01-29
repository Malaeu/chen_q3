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
export PATH="/home/chirurgie/.bun/bin:$PATH"

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
qmd collection add ./docs --name q3_docs
qmd embed
```

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

---

## 2) Research Oracle (qmd wrapper)

### Query docs (fast retrieval)
```bash
./scripts/research_oracle.py query "Szego-Bottcher bound" -c q3_docs
```

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
- Bad search: try `qmd search` (keyword) instead of `qmd query`.
