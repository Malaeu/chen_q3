import contextlib
import importlib.util
import io
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SOURCE = pathlib.Path(__file__).resolve().parents[1] / "bind_request.py"


class Binding(unittest.TestCase):
    def test_lock_collision_prevents_binding(self):
        from orchestrator import bind_request
        from orchestrator.workflow_runtime import WorkflowRuntimeError, _execution_writer_epoch

        with tempfile.TemporaryDirectory() as td:
            root = pathlib.Path(td)
            subprocess.run(["git", "init", "-q", td], check=True)
            (root / ".git/q3-three-body.writer.lock").touch()
            with (
                _execution_writer_epoch(root),
                patch.object(bind_request, "ROOT", root),
                patch.object(bind_request, "bind") as binding,
                patch.object(sys, "argv", ["bind", "request.txt", "--title", "test"]),
            ):
                with self.assertRaisesRegex(WorkflowRuntimeError, "LOCK_COLLISION"):
                    bind_request.main()
                binding.assert_not_called()

    def test_binding(self):
        for mode in ["ready", "hold", "duplicate", "error"]:
            with (
                self.subTest(mode=mode),
                tempfile.TemporaryDirectory() as td,
                patch.dict(
                    os.environ,
                    {
                        "GIT_AUTHOR_NAME": "Test",
                        "GIT_AUTHOR_EMAIL": "test@example.invalid",
                        "GIT_COMMITTER_NAME": "Test",
                        "GIT_COMMITTER_EMAIL": "test@example.invalid",
                    },
                ),
            ):
                root = pathlib.Path(td)

                def git(*args):
                    return subprocess.check_output(["git", *args], cwd=root, text=True).strip()

                git("init", "-q")
                (root / ".git/q3-three-body.writer.lock").touch()
                (root / "queue.md").write_text(
                    "# Queue\n" + ("## REQ-new · old\n" if mode == "duplicate" else "")
                )
                (root / "other").write_text("original")
                git("add", ".")
                git("commit", "-qm", "baseline")
                (root / "other").write_text("staged unrelated")
                git("add", "other")
                (root / "request.txt").write_text(
                    "REQUEST_ID: REQ-new\nBOUNDARY_ID: B\nCALL_CLASS: C\n"
                )
                spec = importlib.util.spec_from_file_location("binder", SOURCE)
                m = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(m)
                m.ROOT = root
                m.QUEUE = root / "queue.md"
                original = m.QUEUE.read_bytes()
                head = git("rev-parse", "HEAD")
                real = m.sh

                def sh(*args, **kwargs):
                    if "review-plan" in args:
                        if mode == "error":
                            raise OSError("review failed")
                        return (
                            '{"status":"'
                            + ("REVIEW_DISPATCH_READY" if mode == "ready" else "HOLD")
                            + '"}'
                        )
                    return real(*args, **kwargs)

                output = io.StringIO()
                with (
                    contextlib.redirect_stdout(output),
                    patch.object(m, "sh", sh),
                    patch.object(
                        sys, "argv", ["bind", "request.txt", "--title", "test", "--no-push"]
                    ),
                ):
                    if mode == "duplicate":
                        with self.assertRaises(SystemExit):
                            m.main()
                        self.assertEqual(head, git("rev-parse", "HEAD"))
                    elif mode == "error":
                        with self.assertRaises(OSError):
                            m.main()
                    else:
                        self.assertEqual(m.main(), 0 if mode == "ready" else 2)
                self.assertEqual(git("diff", "--cached", "--name-only"), "other")
                self.assertEqual(git("show", "HEAD:other"), "original")
                if mode == "ready":
                    self.assertIn("UNPUBLISHED", output.getvalue())
                    self.assertNotIn("LINE:", output.getvalue())
                if mode != "ready":
                    self.assertEqual(m.QUEUE.read_bytes(), original)


if __name__ == "__main__":
    unittest.main()
