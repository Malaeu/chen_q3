---
tags: [pipeline, steering]
priority: high
last_updated: 2026-02-08
---

# KB Refactor: LaTeX→Lean Map + Open-Lemmas Scan

Synthesis:
- Added lemma-level routing from LaTeX labels/sections to Lean entry theorems in `KB/maps/latex_to_lean.md`.
- Made `KB/maps/open_lemmas.md` the authoritative short list of remaining mainline axioms (PrimeCert grid + heat).
- Implemented semi-auto refresh via `q3.lean.aristotle/scripts/kb_refresh.py`:
  - regenerates `KB/insights/INDEX.md`
  - fills the `open_lemmas.md` auto-scan block with per-file axiom/hole counts.
- Updated `KB/SESSION_STATE.md` with a concrete closure checklist: close 3 remaining PrimeCert axioms, then verify `Q3/CheckAxioms.lean` only shows standard+Weil.

Next:
- Start closure work following `KB/axioms/closure_plan.md` (priority: heat bucket → heat arch → grid).
