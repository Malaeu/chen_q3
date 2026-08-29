from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path

import yaml

from specs_docs import session_close


def run(root: Path, *args: str) -> None:
    subprocess.run(list(args), cwd=root, check=True, capture_output=True, text=True)


class SessionClosePlants(unittest.TestCase):
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
