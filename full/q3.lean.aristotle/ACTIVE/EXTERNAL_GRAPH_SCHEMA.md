# External Graph Schema (ACTIVE)

**Purpose:** Define the canonical data model for *external* literature graphs and their alignment to the Lean DAG.
**Current status (1–3 lines):**
- Schema v1 created; JSON stores are empty placeholders.
**Next action (1–2 lines):**
- Populate `PAPER_INDEX.json` with the first source and create one alignment entry.
**Links (3–6):**
- `ACTIVE/EQUIVALENCE_GRAPH.json`
- `ACTIVE/PAPER_INDEX.json`
- `ACTIVE/FAILURE_ATLAS.json`
- `ACTIVE/ALIGNMENT_MAP.json`

---

## Scope

Two layers are tracked separately:

1) **Formal Lean DAG** (authoritative)
   - Files: `ACTIVE/DEPS_TREE_MAIN.json`, `ACTIVE/PROOF_GRAPH.json`
   - Status is derived from Lean + project tooling.

2) **External / Literature Graph** (speculative)
   - Files: `ACTIVE/PAPER_INDEX.json`, `ACTIVE/EQUIVALENCE_GRAPH.json`,
     `ACTIVE/FAILURE_ATLAS.json`, `ACTIVE/ALIGNMENT_MAP.json`
   - Ideas are *speculative by default* and become active only when a Lean stub exists.

## Node Types (external graph)

- `external_claim` — theorem/lemma claim from a paper.
- `external_def` — definition or construction.
- `external_assumption` — explicit assumption (unproven in source).
- `gap` — implicit or missing step (e.g., “it is clear”).
- `numeric` — relies on computation or numerical bound.
- `equivalence` — stated equivalence between two formulations.
- `counterexample` — explicit disproof or obstruction.

## Edge Types

- `depends_on` — proof dependency inside a paper.
- `reduces_to` — reduction from one claim to another.
- `equivalent_to` — logical equivalence (must be symmetric or paired).
- `contradicts` — disproof or incompatibility.
- `cites` — bibliographic reference only (weak edge).

## Status Values

- `speculative` — extracted/guessed from paper; not connected to Lean.
- `active_sorry` — Lean stub exists but proof missing.
- `active_formal` — Lean proof exists (bridge is complete).
- `rejected` — found false or inconsistent.

## Alignment Map (external ↔ Lean)

`ALIGNMENT_MAP.json` records attempted links between external nodes and Lean declarations.
Each entry must include:

- `external_id`, `lean_decl`, `status`
- `norm_convention` (e.g., 2π scaling, t_critical)
- `confidence` (low/med/high)
- `notes` (reasoning)

## Invariants (hard rules)

1) **No speculative edge can be used by the planner.**
2) **`active_formal` edges require a Lean stub or proof reference.**
3) **Every external node must cite a source ID from `PAPER_INDEX.json`.**
4) **Normalization conflicts must be explicit in alignment notes.**

