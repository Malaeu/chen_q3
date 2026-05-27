---
name: q3-step32-lean
description: "Compatibility shim for older Q3 PSD-pd Step32 prompts. Step32 is closed; route active PSD/Step33 bootstrap work to q3-psdpd-step33-bootstrap and its PSD_STEP33_MONITOR/step33_bootstrap request."
metadata:
  short-description: Q3 Step32 compatibility shim
---

# Q3 Step32 Compatibility Shim

Step32 is closed in the current repo.  Do not reopen stale targets such as
`centeredBSplineArchIntegrand_translatedPacketSum_integrable` unless current
Lean files show a regression.

For active PSD work, use the Step33 bootstrap workflow:

1. `AGENTS.md`
2. `Q3_OBSTRUCTION_ATLAS.md`
3. `SESSION_ENTRY.md`
4. `q3.lean.aristotle/ACTIVE/PSD_STEP33_MONITOR.md`
5. `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/node.md`
6. latest Step33 entries in `q3.lean.aristotle/docs/INSIGHTS.md`

The active proof surface is Step33A.1:

- primary/control analytic `A/P/P0` entry hbox lemmas;
- `matrixEntrywiseAbsLe` consumes `hA/hP/hP0`;
- certified blocks and finite analytic Weil nonnegativity consume those
  hboxes downstream.

Use `.agents/skills/q3-psdpd-step33-bootstrap/SKILL.md` for the full current
workflow.
