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
- `ACTIVE/pipeline/oracle_questions/INDEX.md`

---

## Install (qmd)

```bash
bun install -g https://github.com/tobi/qmd
```

If qmd is installed via bun, put `~/.bun/bin` on `PATH` and keep
`"qmd_command": "qmd"` in `RESEARCH_ORACLE.json`. The resolver does not expand
`~` inside a configured command path.

## Refresh `q3_docs`

```bash
./scripts/refresh_q3_docs.py
```

This rebuilds `q3_docs` from the current control docs, active TeX, and live Lean
files while excluding archives, raw inbox markdown, and heavy `PrimeCert` shards.
The refresh path is now serialized through
`q3.lean.aristotle/.qmd_cache/qmd_ops.lock` and retries transient
`SQLITE_BUSY_RECOVERY` failures.

Incoming markdown workflow:

- raw notes / Proshka dumps / unchecked chats or zip drops:
  `docs/incoming_notes/`
- prepare zip/raw inputs:
  `./scripts/ingest_incoming_notes.py prepare docs/incoming_notes/<file-or-zip>`
- reviewed searchable extracts:
  `docs/reviewed_notes/`
- archive processed raw inputs:
  `./scripts/ingest_incoming_notes.py archive ...`

Only `docs/reviewed_notes/` is promoted into `q3_docs`.
Within that folder, only notes marked `safe for embeddings: yes` are embedded.
See:
`docs/EMBEDDING_INGEST_WORKFLOW.md`

## Ingest literature

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

For docs/mainline search, use the refreshed `q3_docs` collection:
```bash
./scripts/research_oracle.py query "keyword" -c q3_docs
```

Before a new blocker search, open a question card:

```bash
python3 q3.lean.aristotle/scripts/oracle_questions.py new \
  --main-address "PO3a.3" \
  --ancestor-address "PO3a, H-bridge.11" \
  --child-address "PO3a.4" \
  --blocker "Знаковая структура одного вектора граничной поправки"
```

Operational rule:

- question cards live in `ACTIVE/pipeline/oracle_questions/`;
- each query series must be tied to one proof-tree address;
- `raw_address_notation` keeps the literal project shorthand;
- `normalized_addresses` must expand shorthand like `D2Q3B5, 7` into the full
  explicit list;
- in card titles, blocker descriptions, and vocabulary fields, write terms in
  Russian first; if needed, add the English label in parentheses on first use;
- after updating cards, run
  `python3 q3.lean.aristotle/scripts/oracle_questions.py reindex`.

This `query` path is now the stable default:

- it runs `qmd search` (BM25) and `qmd vsearch` (vector search) sequentially;
- it merges results by reciprocal-rank fusion;
- it avoids the heavier `qmd query` expansion/rerank path, which is less stable on this host.

Use the legacy heavy backend only if you explicitly want it:
```bash
./scripts/research_oracle.py query "keyword" --mode qmd-query -c q3_docs
```

The wrapper still uses the same lock and retry layer as refresh.
Run local qmd queries sequentially; do not fan out parallel qmd queries on this host.

For the external Together AI minimum-overlap corpus, use the separate collection:
```bash
./scripts/refresh_erdos_overlap_kb.py
./scripts/research_oracle.py query "sequential linear programming" -c erdos_minimum_overlap -n 5
```
This corpus is retrieval-only. It is not a Lean prover and should not be treated
as a replacement for Aristotle.

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
- In wrapper mode `query`, results also include `rrf_score` and `sources`
  (`search`, `vsearch`) so it is obvious which backend surfaced a hit.
- Speculative edges are **not** used by the planner until a Lean stub exists.
- If `q3_docs` is older than the current refactor wave, refresh it before running a
  new blocker search.
- If you still hit `SQLITE_BUSY_RECOVERY`, treat it as a backend contention issue.
  Wait for the current qmd operation to finish instead of starting more local queries.
- `ACTIVE/pipeline/oracle_questions/**` is intentionally excluded from `q3_docs`;
  this journal is search memory, not retrieval corpus.
