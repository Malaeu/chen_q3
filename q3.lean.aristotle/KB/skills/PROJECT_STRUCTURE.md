---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# Project Structure and Archive Policy

This document captures the current root layout, where new work should live,
and the rules for archiving legacy or out-of-scope material.

## Root Layout (Active)

- `AGENTS.md` / `CLAUDE.md` / `README.md`: active workflow and entrypoints.
- `q3.lean.aristotle/`: Lean proofs, DB, Aristotle input/output.
- `ACTIVE/`: symlink to `q3.lean.aristotle/ACTIVE` (current session hub).
- `full/`: LaTeX sources + PDFs (RH_Q3.tex / RH_Q3.pdf).
- `docs/`: living documentation for structure, decisions, and policies.
- `archive/`: legacy materials moved out of the active root.
- `bellman_bmo.py`: BMO check-mode script (lightweight verification).

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

- The A3_FLOOR Lean chain and its DB in `q3.lean.aristotle/`.
- Current paper sources in `full/`.
- Small analysis scripts live at repo root or in `archive/` as needed; outputs go to `output/` when used.

## Decision Rule (Quick Check)

If a file does not support the current A3_FLOOR kernel proof path or the
current paper, it belongs in `archive/`.
