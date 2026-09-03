# Task — Goal 058: real-zero quasi-eigenvector selector, source preflight (paper + source, READ-ONLY)

Date: 2026-09-04 · Status: `AUTHORIZED_BY_JUDGE_AND_OWNER` (verdict `9b822624` CHEAPEST_NEXT_ACTION; owner: Opus agent, do not wait for Codex)

```yaml
TASK_ID: GOAL058_P59_REALZERO_QUASIEIGEN_SELECTOR_SOURCE_PREFLIGHT
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
JUDGE_PREDICTION: [P_SOURCE_SPECIFIC_REALZERO_COMPONENT_IS_SELECTIVE, 0.30]
SUCCESS_CODE: P59_SOURCE_SPECIFIC_REALZERO_SELECTOR_SURVIVES_PLANTS
FAILURE_CODE: P59_REALZERO_CONE_NOT_SELECTIVE
```

Required outputs (judge, verbatim): (1) the exact source predicate stronger than bare `ZerosRealOn`, if CCM Theorem 5.10
supplies one (characteristic determinant / strict interlacing / positive norming data); (2) the exact P59/Lagrange polynomial
attached to the Xi-sample row; (3) the Robin-cosine Nyquist plant written in the project's objects; (4) a noncircular selector
modulus `ω_m`; (5) an interval-test design for the R-diameter of the admissible near-null set.
Falsifier: a center-normalized even source row v at Xi-residual scale, with the same real-zero/characteristic property as the
ground row, but with `‖R(v − y_m)‖` bounded below independently of m.
Forbidden: `‖R(v−y)‖` small as an assumption; any complement floor; the desired convergence; bounded curvature as a selector;
Lean edits; numerical runs (paper task; the observer's Probe 12 numerics may be cited: the Xi-row transform is NOT real-rooted).
Report: `docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_REALZERO_QUASIEIGEN_SELECTOR_SOURCE_PREFLIGHT.md`.
