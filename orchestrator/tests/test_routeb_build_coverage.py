from __future__ import annotations

import tomllib
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
LAKEFILE = ROOT / "q3.lean.aristotle" / "lakefile.toml"


def q3_globs(path: Path = LAKEFILE) -> list[str]:
    data = tomllib.loads(path.read_text(encoding="utf-8"))
    libraries = data.get("lean_lib", [])
    for library in libraries:
        if library.get("name") == "Q3":
            return list(library.get("globs", []))
    raise AssertionError("Q3 lean_lib is missing")


def glob_covers_routeb_module(glob: str, module: str) -> bool:
    if glob.endswith(".+"):
        prefix = glob[:-2]
        return module.startswith(prefix + ".")
    return module == glob


class RouteBBuildCoveragePlants(unittest.TestCase):
    def test_q3_default_target_covers_existing_and_future_routeb_modules(self) -> None:
        globs = q3_globs()
        for module in (
            "Q3.Proofs.RouteB.AbstractCoboundaryLedger",
            "Q3.Proofs.RouteB.FutureNested.NewModule",
        ):
            self.assertTrue(
                any(glob_covers_routeb_module(glob, module) for glob in globs),
                f"{module} is outside the Q3 default build target: {globs}",
            )

    def test_bare_q3_is_not_mistaken_for_subtree_coverage(self) -> None:
        self.assertFalse(glob_covers_routeb_module("Q3", "Q3.Proofs.RouteB.NewModule"))


if __name__ == "__main__":
    unittest.main()
