from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
SCRIPT = REPO / "scripts" / "build_proshka_brief.py"


def load_module():
    spec = importlib.util.spec_from_file_location("q3_build_proshka_brief", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class BuildProshkaBriefPlants(unittest.TestCase):
    def test_default_evidence_pack_carries_consumer_first_sources(self) -> None:
        module = load_module()
        includes = {
            path.relative_to(REPO).as_posix()
            for path in module._default_includes(REPO)
        }
        self.assertIn("docs/Codex/RESEARCH_DEPENDENCY_PROTOCOL.md", includes)
        self.assertIn("docs/routeB_bus/RECHECKABLE_RESEARCH_DEBTS.json", includes)
        self.assertIn("docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md", includes)

    def test_pack_disclaims_request_and_transport_authority(self) -> None:
        module = load_module()
        self.assertIn("EVIDENCE PACK ONLY", module.PACK_DISCLAIMER)
        self.assertIn("not the authoritative Proshka request", module.PACK_DISCLAIMER)
        self.assertIn("not a transport/front door", module.PACK_DISCLAIMER)
        self.assertIn("workflow_runtime.py review-plan", module.PACK_DISCLAIMER)


if __name__ == "__main__":
    unittest.main()
