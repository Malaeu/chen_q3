# External Literature Loop (Q3)

Purpose: automated scouting of published work that might map to our DAG.
This is **not** part of the main proof until a formal Lean bridge exists.

## Workflow

1) Search
- `python3 scripts/proof_compiler/search_external.py --query "toeplitz a3 bridge" --query "rkhs prime cap"`

2) Ingest (optional: add PDFs / metadata)
- `python3 scripts/proof_compiler/ingest_paper.py --id arXiv:xxxx --url <pdf_url> --title "..." --authors "..." --year 2023`

3) Map to DAG
- `python3 scripts/proof_compiler/map_paper_nodes.py --paper-id arXiv:xxxx --node-list <path/to/dependency_graph.json>`

4) Breakpoint report
- `python3 scripts/proof_compiler/breakpoint_report.py --paper-id arXiv:xxxx`

## Data layout

- `external/index.json` — search results + metadata
- `external/papers/` — PDFs
- `external/maps/<paper_id>.json` — candidate node mappings
- `external/breakpoints/<paper_id>.md` — where the external path breaks

## Gate rule

External results are **speculative** unless a formal Lean bridge (lemma stub) exists.
Only after a bridge is added does an edge become **active**.
