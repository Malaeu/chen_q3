# Exact-result assignment selection repair, current isolated plan

Baseline: canonical HEAD d6d548d2. team_records.py SHA256
2dfae6880df1e83b7722a9542cae4a6ff51c02d3f28f047255159c386f362a3a;
test_workflow_runtime.py SHA256
53850233a1a3907a242f1af84e601e66bd716f2d822edb8a0df446a737e0f685.
Scope: only assignment choice in implementer and independent branches; keep
all existing assignment owner, native identity/state/source/evidence and
FIX_VERIFIED artifact checks. No policy, role grants, publication unhold or
schema changes. Tests in existing test_workflow_runtime.py.

Reproduction: /tmp/q3_selector_reproduce.py. A valid current result succeeds;
adding an unrelated lexically earlier old assignment with only LAUNCH raises
NATIVE_OBSERVATION_MISSING for that old assignment.

Algorithm: among rows for requested actor and branch-compatible role, identify
assignments having a RESULT whose exact output_locator/output_sha256 pair is
in the transition's evidence. Treat this as a selection hint, never validation.
Independent branch requires exact assignment/event role equality. Implementer
branch preserves either existing implementation/implementer assignment alias
regardless of the event alias. Require exactly one selected assignment ID;
multiple distinct matching IDs reject explicitly. Count IDs, not RESULT records.
Then run the unchanged _validate_assignment_owner,
_validated_assignment_observation, _require_result_evidence and, if needed,
_require_repair_review_artifact checks on that assignment. Never catch validator
errors and try another candidate. Missing result evidence rejects. A selected
assignment with duplicate/malformed RESULT records must still fail the existing
native validation. Preserve owner-transition branch unchanged.

Tests: current exact match with older LAUNCH-only and unrelated completed
result, invariant under assignment ordering, in both implementer/independent
branches; both implementation/implementer alias pairings must remain accepted. No-match, wrong locator/right hash, right locator/wrong hash,
duplicate matching assignments, selected wrong owner/source/native id,
RUNNING result, duplicated RESULT and FIX_VERIFIED wrong artifact all reject.
Run existing provenance and repair tests plus focused new tests. No canonical
source changes before independent plan review; two clean plan passes are the
recorded repair prerequisite. Prior remote plan output is not available here;
no claim that its review completed. Reconcile/review current full plan instead.
