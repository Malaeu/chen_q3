from __future__ import annotations

import subprocess
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from datetime import date
from io import StringIO
from pathlib import Path
from unittest.mock import patch

from scripts import phase_end


def git(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=root, check=True, text=True, capture_output=True
    )
    return result.stdout.strip()


def dirty_repo(root: Path) -> None:
    git(root, "init", "-q")
    git(root, "branch", "-M", phase_end.BRANCH)
    git(root, "config", "user.email", "phase-end-test@example.invalid")
    git(root, "config", "user.name", "Phase End Test")
    for name in ("owned.txt", "foreign-staged.txt", "foreign-unstaged.txt"):
        (root / name).write_text("base\n", encoding="utf-8")
    git(root, "add", "--", "owned.txt", "foreign-staged.txt", "foreign-unstaged.txt")
    git(root, "commit", "-qm", "base")

    (root / "owned.txt").write_text("scoped change\n", encoding="utf-8")
    (root / "owned-new.txt").write_text("scoped new file\n", encoding="utf-8")
    (root / "foreign-staged.txt").write_text("staged foreign change\n", encoding="utf-8")
    git(root, "add", "--", "foreign-staged.txt")
    (root / "foreign-unstaged.txt").write_text("unstaged foreign change\n", encoding="utf-8")
    (root / "foreign-untracked.txt").write_text("untracked foreign file\n", encoding="utf-8")


class PhaseEndScopedTests(unittest.TestCase):
    def test_changed_lean_is_limited_to_scoped_paths(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lean_dir = root / "q3.lean.aristotle/Q3/Proofs/RouteB"
            lean_dir.mkdir(parents=True)
            scoped = "q3.lean.aristotle/Q3/Proofs/RouteB/Scoped.lean"
            foreign = "q3.lean.aristotle/Q3/Proofs/RouteB/Foreign.lean"
            (root / scoped).write_text("-- base scoped\n", encoding="utf-8")
            (root / foreign).write_text("-- base foreign\n", encoding="utf-8")
            git(root, "init", "-q")
            git(root, "branch", "-M", phase_end.BRANCH)
            git(root, "config", "user.email", "phase-end-test@example.invalid")
            git(root, "config", "user.name", "Phase End Test")
            git(root, "add", "--", scoped, foreign)
            git(root, "commit", "-qm", "base")
            git(root, "update-ref", "refs/remotes/origin/rh_clean", "HEAD")
            (root / scoped).write_text("-- scoped edit\n", encoding="utf-8")
            (root / foreign).write_text("-- foreign edit\n", encoding="utf-8")

            with patch.object(phase_end, "ROOT", root):
                self.assertEqual(phase_end.changed_lean([scoped]), [scoped])

    def test_scoped_closeout_leaves_foreign_outputs_unchanged(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "docs/Codex").mkdir(parents=True)
            lit_dir = root / "docs/literature"
            lit_dir.mkdir(parents=True)
            next_path = root / "docs/Codex/NEXT.md"
            next_path.write_text("- lit: foreign query\n", encoding="utf-8")
            for name in ("owned.txt", "foreign.txt", "staged.txt"):
                (root / name).write_text("base\n", encoding="utf-8")
            git(root, "init", "-q")
            git(root, "branch", "-M", phase_end.BRANCH)
            git(root, "config", "user.email", "phase-end-test@example.invalid")
            git(root, "config", "user.name", "Phase End Test")
            git(root, "add", "--", "docs/Codex/NEXT.md", "owned.txt", "foreign.txt", "staged.txt")
            git(root, "commit", "-qm", "base")

            next_path.write_text("- lit: foreign dirty query\n", encoding="utf-8")
            (root / "owned.txt").write_text("scoped edit\n", encoding="utf-8")
            (root / "foreign.txt").write_text("foreign edit\n", encoding="utf-8")
            (root / "staged.txt").write_text("staged foreign edit\n", encoding="utf-8")
            git(root, "add", "--", "staged.txt")
            outputs = {
                f"scan_{date.today().isoformat()}.json": b"foreign scan bytes\n",
                f"x_{date.today().isoformat()}.json": b"foreign X bytes\n",
            }
            for name, contents in outputs.items():
                (lit_dir / name).write_bytes(contents)
            next_before = next_path.read_bytes()
            foreign_before = (root / "foreign.txt").read_bytes()
            staged_before = git(root, "diff", "--cached", "--", "staged.txt")
            unstaged_before = git(root, "diff", "--", "foreign.txt")

            with (
                patch.object(phase_end, "ROOT", root),
                patch.object(phase_end, "NEXT", next_path),
                patch.object(phase_end, "LIT_DIR", lit_dir),
                patch.object(phase_end, "changed_lean", return_value=[]),
                patch.object(phase_end.shutil, "which", return_value=None),
                patch.object(phase_end, "literature", side_effect=AssertionError("out-of-scope literature call")),
                patch.object(phase_end, "stats", side_effect=AssertionError("out-of-scope stats call")),
                redirect_stdout(StringIO()),
                redirect_stderr(StringIO()),
            ):
                result = phase_end.main(
                    ["scoped closeout", "--scope", "owned.txt", "--no-log"]
                )

            self.assertEqual(result, 1)
            self.assertEqual(next_path.read_bytes(), next_before)
            self.assertEqual((root / "foreign.txt").read_bytes(), foreign_before)
            self.assertEqual(git(root, "diff", "--cached", "--", "staged.txt"), staged_before)
            self.assertEqual(git(root, "diff", "--", "foreign.txt"), unstaged_before)
            for name, contents in outputs.items():
                self.assertEqual((lit_dir / name).read_bytes(), contents)

    def test_scoped_commit_preserves_foreign_staged_unstaged_and_untracked_paths(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            dirty_repo(root)
            staged_before = git(root, "diff", "--cached", "--", "foreign-staged.txt")
            unstaged_before = git(root, "diff", "--", "foreign-unstaged.txt")

            with patch.object(phase_end, "ROOT", root):
                committed = phase_end.commit_scoped(
                    "scoped change", phase_end.normalize_scope(["owned.txt", "owned-new.txt"])
                )

            self.assertTrue(committed)
            committed_paths = set(git(root, "show", "--pretty=format:", "--name-only", "HEAD").splitlines())
            self.assertEqual(committed_paths, {"owned.txt", "owned-new.txt"})
            self.assertEqual(git(root, "diff", "--cached", "--", "foreign-staged.txt"), staged_before)
            self.assertEqual(git(root, "diff", "--", "foreign-unstaged.txt"), unstaged_before)
            self.assertEqual(
                set(git(root, "status", "--porcelain", "--untracked-files=all").splitlines()),
                {"M  foreign-staged.txt", " M foreign-unstaged.txt", "?? foreign-untracked.txt"},
            )

    def test_dirty_no_scope_refuses_before_checks_or_writes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            dirty_repo(root)
            index_before = (root / ".git/index").read_bytes()
            status_before = git(root, "status", "--porcelain", "--untracked-files=all")
            calls: list[list[str]] = []
            original_run = phase_end.run

            def recording_run(cmd: list[str], **kwargs):
                calls.append(cmd)
                return original_run(cmd, **kwargs)

            with patch.object(phase_end, "ROOT", root), patch.object(phase_end, "run", recording_run):
                with redirect_stdout(StringIO()), redirect_stderr(StringIO()):
                    result = phase_end.main(["phase close"])

            self.assertEqual(result, 64)
            self.assertEqual(
                calls,
                [
                    ["git", "branch", "--show-current"],
                    ["git", "status", "--porcelain", "--untracked-files=all"],
                ],
            )
            self.assertEqual((root / ".git/index").read_bytes(), index_before)
            self.assertEqual(git(root, "status", "--porcelain", "--untracked-files=all"), status_before)

    def test_wrong_branch_refuses_before_modifications(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in ("owned.txt", "foreign-staged.txt", "foreign-unstaged.txt"):
                (root / name).write_text("base\n", encoding="utf-8")
            git(root, "init", "-q")
            git(root, "config", "user.email", "phase-end-test@example.invalid")
            git(root, "config", "user.name", "Phase End Test")
            git(root, "add", "--", "owned.txt", "foreign-staged.txt", "foreign-unstaged.txt")
            git(root, "commit", "-qm", "base")
            git(root, "branch", "-M", "other")

            (root / "owned.txt").write_text("scoped edit\n", encoding="utf-8")
            (root / "foreign-staged.txt").write_text("staged foreign edit\n", encoding="utf-8")
            git(root, "add", "--", "foreign-staged.txt")
            (root / "foreign-unstaged.txt").write_text("unstaged foreign edit\n", encoding="utf-8")
            (root / "foreign-untracked.txt").write_text("foreign untracked\n", encoding="utf-8")

            head_before = git(root, "rev-parse", "HEAD")
            index_before = (root / ".git/index").read_bytes()
            status_before = git(root, "status", "--porcelain", "--untracked-files=all")
            contents_before = {
                name: (root / name).read_bytes()
                for name in (
                    "owned.txt",
                    "foreign-staged.txt",
                    "foreign-unstaged.txt",
                    "foreign-untracked.txt",
                )
            }
            calls: list[list[str]] = []
            original_run = phase_end.run

            def recording_run(cmd: list[str], **kwargs):
                calls.append(cmd)
                return original_run(cmd, **kwargs)

            with patch.object(phase_end, "ROOT", root), patch.object(
                phase_end, "run", recording_run
            ):
                with redirect_stdout(StringIO()), redirect_stderr(StringIO()):
                    result = phase_end.main(
                        ["scoped closeout", "--scope", "owned.txt", "--no-log"]
                    )

            self.assertEqual(result, 64)
            self.assertEqual(calls, [["git", "branch", "--show-current"]])
            self.assertEqual(git(root, "rev-parse", "HEAD"), head_before)
            self.assertEqual((root / ".git/index").read_bytes(), index_before)
            self.assertEqual(
                git(root, "status", "--porcelain", "--untracked-files=all"), status_before
            )
            self.assertEqual(
                {name: (root / name).read_bytes() for name in contents_before}, contents_before
            )

    def test_dry_run_is_read_only_and_calls_no_checks_or_network(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            dirty_repo(root)
            index_before = (root / ".git/index").read_bytes()
            status_before = git(root, "status", "--porcelain", "--untracked-files=all")
            contents_before = {
                path.name: path.read_bytes()
                for path in root.iterdir()
                if path.is_file() and path.name != "index"
            }

            with patch.object(phase_end, "ROOT", root), patch.object(
                phase_end, "run", side_effect=AssertionError("dry-run must not execute commands")
            ):
                with redirect_stdout(StringIO()), redirect_stderr(StringIO()):
                    result = phase_end.main(["--dry-run", "--scope", "owned.txt"])

            self.assertEqual(result, 0)
            self.assertEqual((root / ".git/index").read_bytes(), index_before)
            self.assertEqual(git(root, "status", "--porcelain", "--untracked-files=all"), status_before)
            self.assertEqual(
                {
                    path.name: path.read_bytes()
                    for path in root.iterdir()
                    if path.is_file() and path.name != "index"
                },
                contents_before,
            )


if __name__ == "__main__":
    unittest.main()
