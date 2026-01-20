# check_axioms prebuild for A3_FLOOR

### Insight: check_axioms fails when A3_FLOOR is not built

Problem:
- `./scripts/check_axioms.sh` can fail at `Q3/Proofs/P_A_Toeplitz_bridge.lean` with
  `unknown module prefix 'A3_Floor_Main'`.

How to detect:
- The check_axioms log shows the missing module error above.

Fix:
- Prebuild the module before running checks:
  `lake build A3_Floor_Main`
- This step is included in `scripts/check_axioms.sh`.
