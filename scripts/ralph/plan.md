# Ralph Loop - PLAN mode

You are in PLAN mode.
Goal: compare specs vs code and produce a prioritized task list in
`IMPLEMENTATION_PLAN.md`.

Constraints:
- Do not modify code.
- Do not run heavy tests.
- Output is ONLY the updated `IMPLEMENTATION_PLAN.md`.

Project specs to read (in order):
1) full/q3.lean.aristotle/ACTIVE/KNOWLEDGE_BASE.md
2) full/q3.lean.aristotle/ACTIVE/chain_status.md
3) full/q3.lean.aristotle/ACTIVE/Q3_BLOCK_MAP.md
4) full/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md
5) full/q3.lean.aristotle/PHILOSOPHY_OF_PROOF.md

Plan requirements:
- Break the work into small, testable steps.
- Each task must have a clear acceptance check (e.g., `lake env lean <file>`).
- Prioritize the two SingleScale axioms:
  - SingleScale.continuous_P_A_shift
  - SingleScale.rayleigh_basis0_shift_ge_cstar_quarter
- Keep tasks atomic: one logical lemma or wiring step per task.

Output format:
- Use checkboxes: [ ] / [x]
- Include a short "Verification" line under each task.
