"""Plants for the repository-visible Codex task pointer."""

from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path

from orchestrator import spine


REPO = Path(__file__).resolve().parents[2]


def pointer(status: str, task_file: str | None, source_commit: str | None) -> str:
    task = "null" if task_file is None else task_file
    source = "null" if source_commit is None else source_commit
    return (
        "# Codex current task pointer\n\n"
        "```yaml\n"
        "schema: q3_codex_current_task.v1\n"
        f"status: {status}\n"
        f"task_file: {task}\n"
        f"source_commit: {source}\n"
        "updated_at: 2026-08-10T00:00:00+02:00\n"
        "updated_by: TEST\n"
        "```\n"
    )


class CodexCurrentTaskPlants(unittest.TestCase):
    def test_committed_empty_pointer_is_valid(self) -> None:
        data = spine.validate_current_codex_task()
        self.assertEqual(data["status"], "EMPTY")
        self.assertIsNone(data["task_file"])

    def test_active_pointer_requires_tracked_task_and_ancestor_commit(self) -> None:
        task_file = "docs/Codex/TASK_2026-08-06_07.md"
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True,
        ).strip()
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "CURRENT.md"
            path.write_text(pointer("ACTIVE", task_file, head), encoding="utf-8")
            data = spine.validate_current_codex_task(path)
        self.assertEqual(data["task_file"], task_file)
        self.assertEqual(data["source_commit"], head)

    def test_active_pointer_rejects_unpinned_task(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "CURRENT.md"
            path.write_text(
                pointer("ACTIVE", "docs/Codex/TASK_2026-08-06_07.md", None),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(spine.ControlViolation, "source_commit"):
                spine.validate_current_codex_task(path)


if __name__ == "__main__":
    unittest.main()
