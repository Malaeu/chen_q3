from __future__ import annotations

import unittest
from unittest import mock

from orchestrator import spine


class ResearchDependencyP9Wiring(unittest.TestCase):
    def _patches(self):
        return (
            mock.patch.object(spine, "_validate_active_control"),
            mock.patch.object(spine, "validate_behavior_registry", return_value=[]),
            mock.patch.object(
                spine,
                "_read_runtime",
                return_value={"mathematical_authority_mode": "TEST"},
            ),
            mock.patch.object(spine, "validate_cognitive_operator_registry", return_value={}),
            mock.patch.object(spine, "validate_tool_manifest", return_value={}),
            mock.patch.object(
                spine,
                "validate_current_codex_task",
                return_value={"status": "CLOSED", "task_file": None},
            ),
            mock.patch.object(
                spine._three_body_loop,
                "validate_repository_gate",
                return_value={
                    "schema": "test",
                    "control_version": 9,
                    "entries": [],
                    "active_lease": None,
                },
            ),
        )

    def test_normal_p9_invokes_dependency_gate(self) -> None:
        patches = self._patches()
        with (
            patches[0], patches[1], patches[2], patches[3], patches[4], patches[5], patches[6],
            mock.patch.object(spine._research_dependency_gate, "check") as gate,
        ):
            result = spine.validate_p9a()
        gate.assert_called_once_with(spine.REPO)
        self.assertEqual(result["research_dependency"], "PASS")

    def test_dependency_violation_fails_normal_p9_closed(self) -> None:
        patches = self._patches()
        with (
            patches[0], patches[1], patches[2], patches[3], patches[4], patches[5], patches[6],
            mock.patch.object(
                spine._research_dependency_gate,
                "check",
                side_effect=RuntimeError("planted rigid X"),
            ),
        ):
            with self.assertRaisesRegex(
                spine.ControlViolation, "RIGID_DEPENDENCY_UNJUSTIFIED"
            ):
                spine.validate_p9a()


if __name__ == "__main__":
    unittest.main()
