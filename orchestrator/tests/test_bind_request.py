import contextlib
import importlib.util
import io
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from orchestrator import workflow_runtime

SOURCE = pathlib.Path(__file__).resolve().parents[1] / "bind_request.py"


class Binding(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = pathlib.Path(self.temp.name)
        env = patch.dict(os.environ, {"GIT_AUTHOR_NAME": "Test", "GIT_AUTHOR_EMAIL": "test@example.invalid",
                                     "GIT_COMMITTER_NAME": "Test", "GIT_COMMITTER_EMAIL": "test@example.invalid"})
        env.start()
        self.addCleanup(env.stop)
        self.git("init", "-q")
        (self.root / ".git/q3-three-body.writer.lock").touch()
        (self.root / "queue.md").write_text("# Queue\n")
        (self.root / "other").write_text("original")
        control = self.root / "docs/CODEX_CONTROL.md"
        control.parent.mkdir()
        control.write_text("```yaml\nCONTROL_ID: Q3_EXECUTOR_CONTROL\nCONTROL_VERSION: 10\nSTATUS: ACTIVE\n"
                           "HONESTY_STATE: CHALLENGER_NOT_RH\nOWNER_ONLY_BOUNDARY: PX_RH_CLAIM\n```\n")
        self.git("add", ".")
        self.git("commit", "-qm", "fixture baseline")
        spec = importlib.util.spec_from_file_location("binder", SOURCE)
        self.module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.module)
        self.module.ROOT = self.root
        self.module.QUEUE = self.root / "queue.md"
        (self.root / "request.txt").write_text("REQUEST_ID: REQ-new\nBOUNDARY_ID: B\nCALL_CLASS: C\n")

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, text=True, stderr=subprocess.PIPE).strip()

    def remote(self):
        remote = self.root / "remote.git"
        self.git("init", "--bare", "-q", str(remote))
        self.git("remote", "add", "origin", str(remote))
        self.git("push", "-q", "origin", "HEAD:refs/heads/rh_clean")
        return remote

    def run_binding(self, *, no_push=False, intercept=None):
        real = self.module.sh
        def sh(*args, **kwargs):
            if "review-plan" in args:
                return '{"status":"REVIEW_DISPATCH_READY"}'
            if intercept:
                return intercept(real, *args, **kwargs)
            return real(*args, **kwargs)
        argv = ["bind", "request.txt", "--title", "test"] + (["--no-push"] if no_push else [])
        with patch.object(self.module, "sh", side_effect=sh), patch.object(sys, "argv", argv):
            return self.module.main()

    def intent(self):
        paths = list((self.root / ".git/q3-bind-intents").glob("*.json"))
        self.assertEqual(len(paths), 1)
        return paths[0], json.loads(paths[0].read_bytes())

    def test_lock_collision_prevents_binding(self):
        with workflow_runtime._execution_writer_epoch(self.root), patch.object(self.module, "bind") as binding:
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "LOCK_COLLISION"):
                self.run_binding(no_push=True)
            binding.assert_not_called()

    def test_binding_preserves_foreign_index_and_no_push_has_no_delivery_line(self):
        (self.root / "other").write_text("staged unrelated")
        self.git("add", "other")
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            self.assertEqual(self.run_binding(no_push=True), 0)
        self.assertEqual(self.git("diff", "--cached", "--name-only"), "other")
        self.assertEqual(self.git("show", "HEAD:other"), "original")
        self.assertIn("UNPUBLISHED", output.getvalue())
        self.assertNotIn("LINE:", output.getvalue())
        self.assertEqual(self.intent()[1]["state"], "PREPARED")

    def test_review_hold_error_and_foreign_queue_drift(self):
        original = self.module.QUEUE.read_bytes()
        for mode in ("hold", "error", "foreign"):
            with self.subTest(mode=mode):
                real = self.module.sh
                def sh(*args, **kwargs):
                    if "review-plan" in args:
                        if mode == "error":
                            raise OSError("fixture review failure")
                        if mode == "foreign":
                            self.module.QUEUE.write_bytes(b"foreign queue\n")
                        return '{"status":"HOLD"}'
                    return real(*args, **kwargs)
                # New attempts differ by base HEAD after the known aborted transaction.
                with patch.object(self.module, "sh", side_effect=sh), patch.object(sys, "argv", ["bind", "request.txt", "--title", "test", "--no-push"]):
                    if mode == "hold":
                        self.assertEqual(self.module.main(), 2)
                    elif mode == "error":
                        with self.assertRaises(OSError):
                            self.module.main()
                    else:
                        with self.assertRaises(self.module.QueueDriftError):
                            self.module.main()
                self.assertEqual(self.module.QUEUE.read_bytes(), b"foreign queue\n" if mode == "foreign" else original)
                if mode != "foreign":
                    (self.root / "other").write_text(mode)
                    self.git("add", "other")
                    self.git("commit", "-qm", "fixture between aborted attempts")

    def test_push_is_unlocked_pinned_and_later_remote_queue_is_valid(self):
        self.remote()
        observed = []
        def intercept(real, *args, **kwargs):
            if args[1] == "push":
                with workflow_runtime._execution_writer_epoch(self.root):
                    observed.append("unlocked")
                (self.root / "intervening").write_text("must remain local")
                self.git("add", "intervening")
                self.git("commit", "-qm", "intervening local commit")
            return real(*args, **kwargs)
        self.assertEqual(self.run_binding(intercept=intercept), 0)
        _, record = self.intent()
        self.assertEqual(observed, ["unlocked"])
        self.assertEqual(self.git("ls-remote", "origin", "refs/heads/rh_clean").split()[0], record["queue_commit"])
        self.assertNotEqual(self.git("rev-parse", "HEAD"), record["queue_commit"])
        self.module.QUEUE.write_text(self.module.QUEUE.read_text() + "\nA later request\n")
        self.git("add", "queue.md")
        self.git("commit", "-qm", "next independent queue entry")
        self.git("push", "origin", "HEAD:refs/heads/rh_clean")
        before = self.git("rev-parse", "HEAD")
        self.assertEqual(self.run_binding(), 0)
        self.assertEqual(self.git("rev-parse", "HEAD"), before)

    def test_lost_push_receipt_reconciles_without_second_push_or_commit(self):
        self.remote()
        pushes = []
        def intercepted(real, *args, **kwargs):
            if args[1] == "push":
                pushes.append(args)
                real(*args, **kwargs)
                raise OSError("receipt lost after remote accepted")
            return real(*args, **kwargs)
        self.assertEqual(self.run_binding(intercept=intercepted), 0)
        before = self.git("rev-parse", "HEAD")
        self.assertEqual(self.run_binding(intercept=intercepted), 0)
        self.assertEqual(len(pushes), 1)
        self.assertEqual(self.git("rev-parse", "HEAD"), before)

    def test_unknown_outcome_never_replays_and_transport_secret_is_not_printed(self):
        self.remote()
        pushes = []
        def interrupted(real, *args, **kwargs):
            if args[1] == "push" or (args[1] == "ls-remote" and pushes):
                if args[1] == "push":
                    pushes.append(args)
                raise OSError("https://secret:credential@fixture.invalid")
            return real(*args, **kwargs)
        output = io.StringIO()
        with contextlib.redirect_stderr(output):
            self.assertEqual(self.run_binding(intercept=interrupted), 3)
            self.assertEqual(self.run_binding(intercept=interrupted), 3)
        self.assertEqual(len(pushes), 1)
        self.assertEqual(self.intent()[1]["state"], "PUSH_UNKNOWN")
        self.assertNotIn("credential", output.getvalue())
        self.assertIn("UNKNOWN_PUSH_OUTCOME", output.getvalue())

    def test_unpublished_foreign_ancestor_never_reaches_remote(self):
        self.remote()
        baseline = self.git("rev-parse", "HEAD")
        (self.root / "foreign").write_text("must remain local")
        self.git("add", "foreign")
        self.git("commit", "-qm", "foreign pre-existing commit")
        local_head = self.git("rev-parse", "HEAD")
        with self.assertRaisesRegex(self.module.BindingError, "BINDING_UNPUBLISHED_BASE"):
            self.run_binding()
        self.assertEqual(self.git("ls-remote", "origin", "refs/heads/rh_clean").split()[0], baseline)
        self.assertEqual(self.git("rev-parse", "HEAD"), local_head)
        self.assertFalse((self.root / ".git/q3-bind-intents").exists())

    def test_stale_owner_guard_fails_before_any_intent_or_commit(self):
        before = self.git("rev-parse", "HEAD")
        with patch.object(workflow_runtime, "team_guard", side_effect=workflow_runtime.WorkflowRuntimeError("TEAM_OBSERVER_ONLY")):
            with self.assertRaisesRegex(workflow_runtime.WorkflowRuntimeError, "OBSERVER_ONLY"):
                self.run_binding()
        self.assertFalse((self.root / ".git/q3-bind-intents").exists())
        self.assertEqual(self.git("rev-parse", "HEAD"), before)

    def test_verified_push_completes_same_team_reservation_even_after_receipt_crash(self):
        from orchestrator.tests.test_workflow_runtime import TeamRuntimeTests
        fixture = TeamRuntimeTests()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        self.root = fixture.repo
        self.module.ROOT = self.root
        self.module.QUEUE = self.root / "queue.md"
        self.module.QUEUE.write_text("# Queue\n")
        request = self.root / "request.txt"
        request.write_text("REQUEST_ID: REQ-new\nBOUNDARY_ID: B\nCALL_CLASS: C\n")
        data = fixture.data()
        data["operation"].update(command="bind-request", inputs={
            "request.txt": workflow_runtime._resume_digest(request.read_bytes()),
            "queue.md": workflow_runtime._resume_digest(self.module.QUEUE.read_bytes())})
        fixture.install(data)
        self.git("add", "docs", "queue.md")
        self.git("commit", "-qm", "fixture active owner")
        self.remote()
        workflow_runtime.team_observe_remote(self.root, operation_id=data["operation"]["id"])
        workflow_runtime.team_reserve_effect(self.root, operation_id=data["operation"]["id"])
        original_save = self.module._save_intent
        def fail_after_team_confirmation(record, before, epoch):
            if record["state"] == "PUBLISHED":
                raise RuntimeError("fixture publication receipt crash")
            original_save(record, before, epoch)
        with patch.object(workflow_runtime, "_team_enabled", return_value=True):
            with patch.object(self.module, "_save_intent", side_effect=fail_after_team_confirmation):
                with self.assertRaisesRegex(RuntimeError, "publication receipt crash"):
                    self.run_binding()
            self.assertEqual(workflow_runtime._team_local_operation(self.root, data["operation"]["id"])["state"], "CONFIRMED")
            self.assertEqual(self.intent()[1]["state"], "PUSH_UNKNOWN")
            def no_new_effect(real, *args, **kwargs):
                if args[1] in {"push", "commit"}:
                    raise AssertionError("publication replayed")
                return real(*args, **kwargs)
            self.assertEqual(self.run_binding(intercept=no_new_effect), 0)
            self.assertEqual(self.intent()[1]["state"], "PUBLISHED")
            self.assertFalse(any(item["state"] in {"RESERVED", "UNKNOWN"}
                for item in workflow_runtime._team_local(self.root)["operations"].values()))


if __name__ == "__main__":
    unittest.main()
