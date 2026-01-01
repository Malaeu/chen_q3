# Project Structure and Archive Policy

This document captures the current root layout, where new work should live,
and the rules for archiving legacy or out-of-scope material.

## Root Layout (Active)

- `AGENTS.md` / `CLAUDE.md` / `README.md`: active workflow and entrypoints.
- `full/`: Lean proofs and the Aristotle integration workflow.
  - `full/q3.lean.aristotle/`: A3_FLOOR kernel proofs, DB, Aristotle input/output.
- `paper/`: main LaTeX paper for the current proof path.
- `src/`: Python experiments and analysis scripts.
- `output/`: generated plots and tables from scripts (default target).
- `data/`: input data files used by scripts.
- `docs/`: living documentation for structure, decisions, and policies.
- `archive/`: legacy materials moved out of the active root.

## Output Policy (Keep Root Clean)

- All plots, tables, and generated artifacts go to `output/` (default).
- Scripts should create `output/` automatically if missing.
- Avoid absolute paths and writing into the repo root.

## Archive Policy

Move anything not part of the current A3_FLOOR proof path or active tooling
into `archive/`, using these buckets:

- `archive/aristotle_root/`: raw Aristotle outputs and draft .lean files.
- `archive/old_docs/`: superseded plans, TODOs, and legacy notes.
- `archive/latex_aux/`: LaTeX build artifacts and aux files.
- `archive/legacy_tools/`: old scripts that are not in active use.
- `archive/subprojects/`: side projects and old branches of work.

### What Gets Archived

- Old proof strategies (e.g., RKHS or deprecated constants).
- Side projects not in the current Q3/A3_FLOOR track.
- Duplicated or obsolete Aristotle outputs.
- Large build artifacts (Lean `.lake/`, LaTeX aux logs).

### What Stays Active

- The A3_FLOOR Lean chain and its DB in `full/q3.lean.aristotle/`.
- Current paper sources in `paper/`.
- Active Python analysis in `src/`, with outputs in `output/`.

## Decision Rule (Quick Check)

If a file does not support the current A3_FLOOR kernel proof path or the
current paper, it belongs in `archive/`.
