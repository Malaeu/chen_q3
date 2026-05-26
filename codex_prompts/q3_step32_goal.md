# Q3 Step32 Goal

/goal Execute q3.lean.aristotle/ACTIVE/requests/step32_next_gate/node.md.

Stop only when one Step32 theorem compiles or
q3.lean.aristotle/ACTIVE/requests/step32_next_gate/report.md contains the exact
missing lemma/blocker.

Required reads:

- AGENTS.md
- Q3_OBSTRUCTION_ATLAS.md
- .agents/skills/q3-step32-lean/SKILL.md
- SESSION_ENTRY.md
- q3.lean.aristotle/PROJECT_WORKFLOW.md
- q3.lean.aristotle/ACTIVE/requests/step32_next_gate/node.md
- latest Step32 entries in q3.lean.aristotle/docs/INSIGHTS.md

Validation:

```bash
scripts/q3_check.sh Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean
```

Do not edit Q3.Main. Do not use numerical PSD as proof. Do not add fake axioms,
`sorry`, `admit`, or `exact?`.
