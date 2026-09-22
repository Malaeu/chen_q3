# Owner-directed relocation recovery — 2026-09-22

The human owner explicitly directed continuation on this Mac and repair of the
home/work relocation deadlock. This scoped repair implements that instruction;
it is not mathematical admission and does not authorize PX_RH_CLAIM.

Control revision 12 adds a source/epoch/checkpoint-bound option to the existing
resume-checkpoint transaction. It preserves immutable history, source pins and
review stages. An optional retirement applies only to unresolved ASSIGN/agent-launch:
the complete operation is retained with outcome UNKNOWN, the active slot is cleared,
and reservation rejects its ID from append-only history on future installations.
The current actor may continue synchronous owner-directed work; native watch
activation and old-host quiescence are not asserted. Other uncertain external
effects cannot be retired by this path. No old installation identity is forged.

Independent read-only review: /root/recovery_review, APPROVED after corrections.
Seven recovery tests independently passed; all eight targeted tests passed locally,
including malformed retirement metadata. Reviewed files and SHA-256:

- orchestrator/workflow_runtime.py: 1a2912dcf0a10c6d6def0d9b1b9f993c416b77e6c54f72386a2fa404a762827d
- orchestrator/startup_runtime.py: fa79aadd4739f503527ed974ef68f2dc24f1434c41775af7b0395038c856e13e
- orchestrator/tests/test_workflow_runtime.py: 53850233a1a3907a242f1af84e601e66bd716f2d822edb8a0df446a737e0f685
- docs/CODEX_CONTROL.md: b77a0f8a78e96873e3139baebe8e86454f42a8628a69e52bb9712f22cbac1715
- docs/cartographer/TOOLS.yaml: ff406e102a0b401fb1d64b000e3382939532123d050c6358dc6f862e4f07e8b9

Validation: 83 startup/checkpoint tests passed in a targeted run. Final combined
workflow/startup run with TMPDIR=/private/tmp: 297 run, 296 passed, one failed.
The failing existing fresh-process SIGKILL test observed the second file already
copied before its 1 ms polling loop killed the child. Its migration variant failed
separately and was excluded from the final run. The Linux strace test was excluded
because strace is unavailable on this Mac. These failures were not called passes;
the timed crash fixture and production integration implementation were not weakened.
Full final output follows.

```text
NOT RUN: orchestrator.tests.test_workflow_runtime.ControlV10BenchmarkPlants.test_strace_runs_the_exact_production_workflow_cli
NOT RUN: orchestrator.tests.test_workflow_runtime.TeamRuntimeTests.test_pinned_engine_recovers_control_10_to_11_migration
...............................................................................................................F.........................................................................usage: workflow_runtime.py [-h] [--root ROOT]
                           {team-local-init,team-bootstrap-publish,team-integrate-candidate,team-watch-intent,team-record,team-observe-remote,team-reserve-effect,team-observe-native,team-confirm-effect,plan,run,close-session,close-phase,resume-checkpoint,review-plan} ...
workflow_runtime.py: error: unrecognized arguments: --legacy-v9-maintenance
................................................................................................................
======================================================================
FAIL: test_fresh_process_recovers_persisted_manifest_after_runtime_write_crash (orchestrator.tests.test_workflow_runtime.TeamRuntimeTests.test_fresh_process_recovers_persisted_manifest_after_runtime_write_crash)
----------------------------------------------------------------------
Traceback (most recent call last):
  File "/Users/emalam/GitHub/rh_lean_01_2026/orchestrator/tests/test_workflow_runtime.py", line 7203, in test_fresh_process_recovers_persisted_manifest_after_runtime_write_crash
    self._assert_fresh_process_integration_recovery(self._fresh_process_integration_fixture())
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/Users/emalam/GitHub/rh_lean_01_2026/orchestrator/tests/test_workflow_runtime.py", line 7336, in _assert_fresh_process_integration_recovery
    self.assertEqual(
    ~~~~~~~~~~~~~~~~^
        (destination / "zz-integration-target.txt").read_bytes(),
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        fixture["before_target"],
        ^^^^^^^^^^^^^^^^^^^^^^^^^
    )
    ^
AssertionError: b'candidate target\nxxxxxxxxxxxxxxxxxxxxxxx[1449973 chars]xxxx' != b'old target\n'

----------------------------------------------------------------------
Ran 297 tests in 113.703s

FAILED (failures=1)
{"schema": "q3_search_evidence.v1", "status": "PASS", "observed_at": "2026-09-02T12:00:00+00:00"}

```
