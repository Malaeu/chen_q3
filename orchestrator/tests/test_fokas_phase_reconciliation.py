"""Real Git evidence and negative controls for the isolated one-shot repair."""
from contextlib import ExitStack, redirect_stdout, redirect_stderr
import io
from unittest.mock import Mock, patch
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from orchestrator import spine
from orchestrator import fokas_phase_reconciliation as repair


class FokasPhaseTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name)
        self.raw = (spine.REPO / "orchestrator/state/CHANNEL_RUNTIME.json").read_bytes()
        self.evidence = (spine.REPO / repair.RECEIPT_PATH).read_bytes()
        p = self.repo / repair.RECEIPT_PATH
        p.parent.mkdir(parents=True)
        p.write_bytes(self.evidence)
        self.git("init", "-q")
        self.git("add", repair.RECEIPT_PATH)
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                 "commit", "-qm", "Fixture evidence")
        self.event = {"transition_id": repair.TRANSITION,
                      "expected_runtime_sha256": repair.PREIMAGE,
                      "receipt_pin": {"path": repair.RECEIPT_PATH,
                                      "commit": self.git("rev-parse", "HEAD"),
                                      "blob": self.git("rev-parse", "HEAD:" + repair.RECEIPT_PATH),
                                      "sha256": repair.RECEIPT_SHA}}

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.repo, stderr=subprocess.DEVNULL).decode().strip()

    def run_repair(self, raw=None, event=None):
        return repair.reconcile(self.raw if raw is None else raw,
                                self.event if event is None else event,
                                repo=self.repo, recorded_at="2026-09-23T12:00:00+00:00")

    def assert_rejected(self, raw=None, event=None, code=None):
        with self.assertRaises(spine.ControlViolation) as ctx:
            self.run_repair(raw, event)
        if code:
            self.assertEqual(ctx.exception.code, code)

    def test_real_git_receipt_preserves_all_history_and_no_effect_counters(self):
        old = json.loads(self.raw)
        new, changed = self.run_repair()
        self.assertTrue(changed)
        history = new["observed_phase_transitions"]
        self.assertEqual(history[:-1], old.get("observed_phase_transitions", []))
        self.assertEqual(history[-1]["predecessor_phase"], old["active_proshka_phase"])
        self.assertEqual(history[-1]["predecessor_meter"], old["meter"])
        for k in old:
            if k not in {"active_proshka_phase", "observed_phase_transitions", "meter"}:
                self.assertEqual(new[k], old[k], k)
        for k, v in old["meter"].items():
            self.assertEqual(new["meter"][k], v + (k == "phases_opened"), k)
        self.assertEqual(new["active_proshka_phase"]["proshka_calls"], 0)
        self.assertIsNone(new["active_proshka_phase"]["last_adjudicated_pin"])
        self.assertEqual(new["active_proshka_phase"]["conversation_id"],
                         "6aafb38a-a7a4-83eb-9940-84a574eae168")

    def test_exact_replay_is_noop(self):
        new, _ = self.run_repair()
        replay, changed = self.run_repair(json.dumps(new).encode())
        self.assertFalse(changed)
        self.assertEqual(replay, new)

    def test_changed_successor_is_not_overwritten(self):
        new, _ = self.run_repair()
        new["active_proshka_phase"]["last_boundary_id"] = "LATER_REAL_EVENT"
        self.assert_rejected(json.dumps(new).encode(), code="FOKAS_PHASE_REPLAY_CONFLICT")

    def test_changed_preimage_rejected(self):
        self.assert_rejected(self.raw + b"\n", code="FOKAS_PHASE_STALE_PREIMAGE")

    def test_wrong_transition_rejected(self):
        self.event["transition_id"] = "DIFFERENT_TASK"
        self.assert_rejected(code="FOKAS_PHASE_EVENT_INVALID")

    def test_false_receipt_blob_rejected(self):
        self.event["receipt_pin"]["blob"] = "0" * 40
        self.assert_rejected(code="PHASE_RECORD_INVALID")

    def test_worktree_evidence_is_not_authority(self):
        (self.repo / repair.RECEIPT_PATH).write_text("uncommitted tampering")
        new, changed = self.run_repair()
        self.assertTrue(changed)
        self.assertEqual(new["observed_phase_transitions"][-1]["receipt"], json.loads(self.evidence))

    def test_wrong_evidence_hash_rejected(self):
        self.event["receipt_pin"]["sha256"] = hashlib.sha256(b"replacement").hexdigest()
        self.assert_rejected(code="FOKAS_PHASE_RECEIPT_INVALID")

    def test_naive_timestamp_rejected(self):
        with self.assertRaises(spine.ControlViolation) as ctx:
            repair.reconcile(self.raw, self.event, repo=self.repo,
                             recorded_at="2026-09-23T12:00:00")
        self.assertEqual(ctx.exception.code, "FOKAS_PHASE_TIME_INVALID")


class FokasPhaseCliTests(unittest.TestCase):
    """Actual CLI/atomic writer on temp state; host authorization is a fixture."""
    setUp = FokasPhaseTests.setUp
    git = FokasPhaseTests.git

    def invoke(self, execute=False, recheck=None, guard=None):
        from orchestrator import workflow_runtime as workflow
        runtime = self.repo / "runtime.json"
        if not runtime.exists():
            runtime.write_bytes(self.raw)
        event = self.repo / "event.json"
        event.write_text(json.dumps(self.event))
        epoch = Mock()
        epoch.recheck.side_effect = recheck
        argv = ["spine", "--record-fokas-transition", str(event)]
        if execute:
            argv.append("--execute-fokas-transition")
        writer = spine.write_runtime_atomic
        with ExitStack() as stack:
            stack.enter_context(patch.object(spine, "REPO", self.repo))
            stack.enter_context(patch.object(spine, "CHANNEL_RUNTIME", runtime))
            stack.enter_context(patch.object(spine, "_validate_active_control"))
            stack.enter_context(patch.object(spine, "write_runtime_atomic",
                side_effect=lambda value: writer(value, path=runtime)))
            epoch_context = stack.enter_context(patch.object(workflow, "_execution_writer_epoch"))
            epoch_context.return_value.__enter__.return_value = epoch
            stack.enter_context(patch.object(workflow, "team_guard", side_effect=guard))
            stack.enter_context(patch("sys.argv", argv))
            stack.enter_context(redirect_stdout(io.StringIO()))
            stack.enter_context(redirect_stderr(io.StringIO()))
            code = spine.main()
        return code, runtime.read_bytes(), epoch

    def test_cli_dry_run_preserves_bytes(self):
        code, raw, epoch = self.invoke()
        self.assertEqual(code, 0)
        self.assertEqual(raw, self.raw)
        epoch.recheck.assert_not_called()

    def test_cli_execute_and_replay(self):
        code, raw, epoch = self.invoke(execute=True)
        self.assertEqual(code, 0)
        self.assertNotEqual(raw, self.raw)
        epoch.recheck.assert_called_once()
        code, replay, epoch = self.invoke(execute=True)
        self.assertEqual(code, 0)
        self.assertEqual(replay, raw)
        epoch.recheck.assert_not_called()

    def test_cli_guard_failure_preserves_bytes(self):
        def reject(*args, **kwargs):
            spine._fail("TEST_GUARD_REJECTION")
        code, raw, _ = self.invoke(execute=True, guard=reject)
        self.assertEqual(code, 2)
        self.assertEqual(raw, self.raw)

    def test_cli_epoch_failure_preserves_bytes(self):
        def reject():
            spine._fail("TEST_EPOCH_REJECTION")
        code, raw, _ = self.invoke(execute=True, recheck=reject)
        self.assertEqual(code, 2)
        self.assertEqual(raw, self.raw)

    def test_cli_concurrent_change_is_not_overwritten(self):
        concurrent = self.raw + b"\n"
        def change():
            (self.repo / "runtime.json").write_bytes(concurrent)
        code, raw, _ = self.invoke(execute=True, recheck=change)
        self.assertEqual(code, 2)
        self.assertEqual(raw, concurrent)


class FokasWriterRegistrationTests(unittest.TestCase):
    def test_actual_writer_inventory_includes_reconciliation(self):
        from orchestrator import workflow_runtime
        inventory = workflow_runtime._team_writer_inventory(spine.REPO)
        self.assertIn("fokas-observed-phase-repair", inventory["fenced"])


if __name__ == "__main__":
    unittest.main()
