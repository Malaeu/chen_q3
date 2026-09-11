from __future__ import annotations

import subprocess
import io
import sys
import tempfile
import unittest
from contextlib import contextmanager, redirect_stdout
from pathlib import Path
from unittest import mock

import yaml

from specs_docs import session_close
from orchestrator import spine, workflow_runtime


def run(root: Path, *args: str) -> None:
    subprocess.run(list(args), cwd=root, check=True, capture_output=True, text=True)


class SessionClosePlants(unittest.TestCase):
    @contextmanager
    def close_call(self, *arguments: str):
        """Exercise the real close CLI without touching the local search index."""
        output = io.StringIO()
        with (
            mock.patch.object(sys, "argv", ["session-close", "--root", str(session_close.REPO), *arguments]),
            mock.patch.object(session_close, "repair_derived", return_value=([], [])) as repair,
            mock.patch.object(session_close, "dirty_split", return_value=([], ["foreign.md"])),
            mock.patch.object(session_close, "verify_owned_lean", return_value=[]),
            mock.patch.object(session_close.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, stdout="a" * 40)),
            mock.patch.object(session_close.session_briefing, "write_checkpoint", return_value=Path("checkpoint.json")) as checkpoint,
            mock.patch.object(session_close, "atomic_write") as protocol,
            mock.patch.object(spine, "validate_p9a") as base,
            mock.patch.object(spine, "semantic_index_stale", return_value=True) as stale,
            mock.patch.object(spine, "_run_checked") as stage,
            mock.patch.object(spine, "validate_semantic_index") as validate,
            redirect_stdout(output),
        ):
            yield output, repair, checkpoint, protocol, base, stale, stage, validate

    def test_semantic_refresh_runs_complete_pipeline_then_fresh_replay_skips_it(self) -> None:
        with self.close_call("--semantic-refresh") as (output, _, checkpoint, _, base, stale, stage, validate):
            events = []
            stage.side_effect = lambda action, command: events.append(command[0])
            validate.side_effect = lambda **kwargs: events.append("validate")
            checkpoint.side_effect = lambda repo: events.append("checkpoint") or Path("checkpoint.json")
            self.assertEqual(session_close.main(), 0)
            self.assertEqual(events, [
                "q3.lean.aristotle/scripts/refresh_q3_docs.py",
                "scripts/deep_preflight.py",
                "scripts/semantic_index_plants.py",
                "validate", "checkpoint",
            ])
            self.assertEqual(base.call_count, 2)
            self.assertIn("`REFRESHED` (validated)", output.getvalue())
            stage.reset_mock()
            base.reset_mock()
            stale.return_value = False
            events.clear()
            self.assertEqual(session_close.main(), 0)
            stage.assert_not_called()
            base.assert_called_once()
            self.assertEqual(events, ["validate", "checkpoint"])
            self.assertIn("`FRESH` (validated)", output.getvalue())

    def test_semantic_failures_never_write_a_success_checkpoint(self) -> None:
        for failure in ("base", "builder", "preflight", "plants", "post-base", "receipt", "io"):
            with self.subTest(failure=failure), self.close_call("--semantic-refresh") as (output, _, checkpoint, protocol, base, _, stage, validate):
                error = spine.ControlViolation("SEMANTIC_TEST_FAILURE")
                if failure == "base":
                    base.side_effect = error
                elif failure == "post-base":
                    base.side_effect = [None, error]
                elif failure in {"builder", "preflight", "plants"}:
                    stage.side_effect = [None] * ("builder", "preflight", "plants").index(failure) + [error]
                elif failure == "receipt":
                    validate.side_effect = error
                else:
                    stage.side_effect = OSError("SEMANTIC_TEST_FAILURE")
                self.assertEqual(session_close.main(), 2)
                checkpoint.assert_not_called()
                protocol.assert_not_called()
                self.assertIn("SEMANTIC_TEST_FAILURE", output.getvalue())
                self.assertNotIn("(validated)", output.getvalue())
                self.assertNotIn("SESSION_CHECKPOINT_WRITTEN", output.getvalue())

    def test_semantic_wrong_root_is_refused_before_derived_repair(self) -> None:
        for mismatch in ("argument", "module"):
            arguments = ["--semantic-refresh", "--repair"]
            if mismatch == "argument":
                arguments += ["--root", "/different-q3-copy"]
            with self.subTest(mismatch=mismatch), self.close_call(*arguments) as (output, repair, checkpoint, protocol, base, _, stage, _):
                with mock.patch.object(spine, "REPO", Path("/different-q3-module") if mismatch == "module" else spine.REPO):
                    self.assertEqual(session_close.main(), 2)
                self.assertIn("SESSION_CLOSE_SEMANTIC_ROOT_MISMATCH", output.getvalue())
                for writer in (repair, checkpoint, protocol, base, stage):
                    writer.assert_not_called()

    def test_semantic_protocol_output_is_refused_before_any_write(self) -> None:
        with self.close_call("--semantic-refresh", "--repair", "--protocol-out", "docs/routeB_bus/close.md") as (output, repair, checkpoint, protocol, base, _, stage, _):
            self.assertEqual(session_close.main(), 2)
            self.assertIn("SESSION_CLOSE_SEMANTIC_PROTOCOL_OUT_FORBIDDEN", output.getvalue())
            for writer in (repair, checkpoint, protocol, base, stage):
                writer.assert_not_called()

    def test_default_close_keeps_protocol_output_and_does_not_run_semantic_work(self) -> None:
        with self.close_call("--protocol-out", "close.md") as (_, _, checkpoint, protocol, base, stale, stage, validate):
            self.assertEqual(session_close.main(), 0)
            checkpoint.assert_called_once()
            protocol.assert_called_once()
            for semantic in (base, stale, stage, validate):
                semantic.assert_not_called()

    def test_close_wrapper_forwards_semantic_flag_under_real_writer_lock(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            run(root, "git", "init", "-q", "-b", "rh_clean")
            (root / ".git/q3-three-body.writer.lock").touch()
            (root / "specs_docs").mkdir()
            (root / "specs_docs/session_close.py").write_text(
                "import fcntl, sys\n"
                "assert '--semantic-refresh' in sys.argv\n"
                "with open('.git/q3-three-body.writer.lock', 'rb') as lock:\n"
                "    try:\n"
                "        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)\n"
                "    except BlockingIOError:\n"
                "        sys.exit(0)\n"
                "    sys.exit('parent writer lock was not retained')\n"
            )
            with (
                mock.patch.object(workflow_runtime, "_team_enabled", return_value=True),
                mock.patch.object(workflow_runtime, "_team_pending_guard"),
                mock.patch.object(workflow_runtime, "team_guard") as guard,
            ):
                self.assertEqual(workflow_runtime._run_close_script(root, "specs_docs/session_close.py", ["--semantic-refresh"]), 0)
                guard.assert_called_once_with(root, command="workflow-session-close", paths=[])

    def test_incremental_repair_second_run_noop_and_foreign_preserved(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            run(root, "git", "init", "-q", "-b", "rh_clean")
            (root / "input").write_text("v1\n")
            (root / "output").write_text("v1\n")
            run(root, "git", "add", "-A")
            run(root, "git", "-c", "user.name=Plant", "-c", "user.email=p@example.invalid", "commit", "-qm", "baseline")
            (root / "input").write_text("v2\n")
            (root / "foreign").write_text("keep\n")
            registry = root / "registry.yaml"
            registry.write_text(yaml.safe_dump({"schema": "q3_derived_artifact_registry.v1", "artifacts": [{"id": "copy", "detector": "GIT_DERIVATION", "inputs": ["input"], "outputs": ["output"], "generator_tool": "copy", "repair_command": ["cp", "input", "output"], "authority": "DERIVED", "cost_tier": "CHEAP"}]}))
            executed, statuses = session_close.repair_derived(root, registry, repair=True)
            self.assertEqual(executed, ["copy"])
            self.assertEqual((root / "foreign").read_text(), "keep\n")
            # The byte-bound local receipt proves the current worktree projection
            # and makes an immediate second close a true no-op.
            self.assertEqual(statuses[0].status, "CURRENT_WORKTREE")
            self.assertEqual(
                session_close.dependency_registry.statuses(root, registry)[0].status,
                "CURRENT_WORKTREE",
            )
            payload = yaml.safe_load(registry.read_text())
            payload["artifacts"][0]["repair_command"] = ["cp", "--", "input", "output"]
            registry.write_text(yaml.safe_dump(payload))
            self.assertEqual(
                session_close.dependency_registry.statuses(root, registry)[0].status,
                "STALE",
            )
            payload["artifacts"][0]["repair_command"] = ["cp", "input", "output"]
            registry.write_text(yaml.safe_dump(payload))
            executed2, statuses2 = session_close.repair_derived(root, registry, repair=True)
            self.assertEqual(executed2, [])
            self.assertEqual(statuses2[0].status, "CURRENT_WORKTREE")
            run(root, "git", "add", "input", "output")
            run(root, "git", "-c", "user.name=Plant", "-c", "user.email=p@example.invalid", "commit", "-qm", "refresh")
            executed3, statuses3 = session_close.repair_derived(root, registry, repair=True)
            self.assertEqual(executed3, [])
            self.assertEqual(statuses3[0].status, "FRESH")
            owned, foreign = session_close.dirty_split(root, ["input", "output"])
            self.assertEqual(owned, [])
            self.assertEqual(foreign, ["foreign", "registry.yaml"])

    def test_owned_lean_requires_kernel_gate(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with self.assertRaisesRegex(RuntimeError, "KERNEL_GATE_REQUIRED"):
                session_close.verify_owned_lean(root, ["q3.lean.aristotle/Q3/X.lean"], run_kernel=False)


if __name__ == "__main__":
    unittest.main()
