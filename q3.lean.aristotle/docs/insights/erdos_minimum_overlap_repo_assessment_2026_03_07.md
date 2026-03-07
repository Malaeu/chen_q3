# Together AI `erdos-minimum-overlap` repo assessment

Date: 2026-03-07

## Verdict

This repo is useful as an **external AI-math artifact corpus**, but not as a
drop-in replacement for Aristotle.

## What is actually in the repo

- `README.md` with the problem statement and claimed SOTA upper bound.
- `solutions/*.py` containing static step-function arrays.
- `analysis.ipynb` that verifies and visualizes those arrays.

## What is not in the repo

- no Lean code,
- no theorem prover,
- no prompt traces,
- no reusable proof-search framework,
- no published optimizer implementation beyond high-level mentions of
  sequential linear programming.

## Practical use for Q3

Use it as:

- a separate semantic-search collection,
- methodological context for AI-assisted mathematical search,
- an example of how a small external artifact can package results cleanly.

Do **not** use it as:

- a substitute for Aristotle,
- a direct source of Lean proofs,
- evidence that the underlying search procedure is available here.

## Operational decision

Local vendor clone:

- `archive/subprojects/erdos-minimum-overlap/`

Separate qmd collection:

- `erdos_minimum_overlap`

Refresh command:

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle
./scripts/refresh_erdos_overlap_kb.py
```

Query command:

```bash
./scripts/research_oracle.py query "sequential linear programming" -c erdos_minimum_overlap -n 5
```

This keeps the corpus usable without polluting `q3_docs`.
