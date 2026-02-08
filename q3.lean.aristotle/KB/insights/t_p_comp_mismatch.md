---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# T_P_comp Mismatch: Defined but Not Wired

Date: 2026-01-14

## Symptom
- A3_bridge_axiom and related proof sketches use direct-indexed T_P (matrix over Fin M).
- Q3 defines the compression operator T_P_comp over Nodes K with prime_vec normalization.

## Ground Truth
- T_P_comp is defined in `Q3/Basic/Defs.lean` (look for `def T_P_comp`).
- It sums over `Nodes K` and uses `prime_vec` with `1/sqrt(2*M+1)` normalization.

## Risk
- Using direct-indexed T_P breaks the intended compression form.
- Uniform t arguments fail when the operator grows with M.
- It diverges from the Rayleigh-first bridge and RKHS cap setup.

## Fix Direction
- Switch A3_bridge_* to use `T_P_comp` (or `T_P_comp_real`) consistently.
- State Rayleigh bounds for `ToeplitzMatrix ... - T_P_comp`.

## Related Files
- `Q3/Basic/Defs.lean`
- `Q3/Axioms.lean`
- `Q3/Proofs/RKHS_cap_rayleigh.lean`
- `Q3/Proofs/A3_bridge_rayleigh_first.lean`
