# External Proof-Graph Pipeline

**Purpose:** Run the two‑loop workflow (formal Lean DAG + external literature DAG) with a strict formal gate.
**Current status (1–3 lines):**
- Formal DAG tooling exists (`build_dependency_tree.py`, `build_proof_graph.py`).
- External graph stores are initialized but empty.
**Next action (1–2 lines):**
- Populate `PAPER_INDEX.json` with the first external source and add one alignment entry.
**Links (3–6):**
- `ACTIVE/EXTERNAL_GRAPH_SCHEMA.md`
- `ACTIVE/EQUIVALENCE_GRAPH.json`
- `ACTIVE/PAPER_INDEX.json`
- `ACTIVE/FAILURE_ATLAS.json`
- `ACTIVE/ALIGNMENT_MAP.json`
- `ACTIVE/PROOF_GRAPH.json`

---

## Minimal loop (authoritative)

1. **Extract Lean DAG**  
   `python scripts/build_dependency_tree.py`  
   `python scripts/build_proof_graph.py`

2. **List sorries (frontier)**  
   `./scripts/build_sorry_frontier.py`
   *(or quick view: `./scripts/tdd.sh sorries`)*

3. **Run taint analysis (FRI-style)**  
   `./scripts/build_taint_graph.py`  
   *(optional numeric gate: `./scripts/numeric_sanity_check.py --write-back`)*
   *(risk config: `ACTIVE/RISK_MODEL.json`)*

4. **External ingestion (speculative)**  
   Add one source to `ACTIVE/PAPER_INDEX.json` and record its claims in
   `ACTIVE/EQUIVALENCE_GRAPH.json` with status `speculative`.

5. **Formal gate**  
   Create a Lean stub for any external claim you want to use.
   Only then promote the edge to `active_sorry` / `active_formal`.

## Rule of use

The planner may **only** use `active_*` edges.  
Everything else is metadata until a Lean stub exists.
