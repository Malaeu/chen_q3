from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path

from orchestrator import dependency_registry


def run(root: Path, *args: str) -> str:
    return subprocess.run(list(args), cwd=root, check=True, capture_output=True, text=True).stdout.strip()


def commit(root: Path, message: str) -> str:
    run(root, "git", "add", "-A")
    run(root, "git", "-c", "user.name=Registry Plant", "-c", "user.email=plant@example.invalid", "commit", "-qm", message)
    return run(root, "git", "rev-parse", "HEAD")


class DependencyRegistryPlants(unittest.TestCase):
    def test_git_derivation_fresh_then_stale_and_dirty_output(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            run(root, "git", "init", "-q", "-b", "rh_clean")
            (root / "src").mkdir()
            (root / "src/a.lean").write_text("def a := 1\n")
            (root / "gen.py").write_text("# generator\n")
            commit(root, "inputs")
            (root / "out.json").write_text("{}\n")
            commit(root, "derived output")
            row = {"id": "plant", "detector": "GIT_DERIVATION", "inputs": ["src/**/*.lean", "gen.py"], "outputs": ["out.json"], "repair_command": ["true"]}
            self.assertEqual(dependency_registry.evaluate(root, row).status, "FRESH")
            (root / "src/a.lean").write_text("def a := 2\n")
            self.assertEqual(dependency_registry.evaluate(root, row).status, "STALE")
            run(root, "git", "checkout", "--", "src/a.lean")
            (root / "out.json").write_text('{"dirty":true}\n')
            self.assertEqual(dependency_registry.evaluate(root, row).status, "DIRTY_OUTPUT")

    def test_needs_cards_detects_exact_existing_card_and_manual_debt(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lit = root / "docs/routeB_bus/litreview"
            lit.mkdir(parents=True)
            row = {"id": "cards", "detector": "NEEDS_CARDS_CONSISTENCY"}
            refs = lit / "REFERENCES.md"
            refs.write_text("| X | NEEDS_CARDS | `X_USAGE_CARDS.md` |\n")
            (lit / "X_USAGE_CARDS.md").write_text("# card\n")
            self.assertEqual(dependency_registry.evaluate(root, row).status, "STALE")
            (lit / "X_USAGE_CARDS.md").unlink()
            self.assertEqual(dependency_registry.evaluate(root, row).status, "MANUAL_DEBT")
            refs.write_text("| X | HAVE | `X_USAGE_CARDS.md` |\n")
            self.assertEqual(dependency_registry.evaluate(root, row).status, "FRESH")


if __name__ == "__main__":
    unittest.main()
