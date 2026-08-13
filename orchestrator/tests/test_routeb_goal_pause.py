"""Plants for restorable Route B goal pauses."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from orchestrator import packet
from orchestrator.routeb_goal_state import (
    goal_machine_header_text,
    goal_status_text,
    is_paused_goal,
)


class RouteBGoalPausePlants(unittest.TestCase):
    def test_first_machine_status_controls_pause(self) -> None:
        text = """# GOAL 057
```yaml
GOAL: 057
STATUS: PAUSED_RESTORABLE
```
STATUS: OPEN
"""
        self.assertEqual(goal_status_text(text), "PAUSED_RESTORABLE")

    def test_paused_goal_remains_a_file_but_is_not_executable(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            goal = Path(tmp) / "057_example.goal.md"
            goal.write_text(
                "```yaml\nGOAL: 057\nSTATUS: PAUSED_RESTORABLE\n```\n",
                encoding="utf-8",
            )
            self.assertTrue(goal.is_file())
            self.assertTrue(is_paused_goal(goal))

    def test_open_goal_is_not_paused(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            goal = Path(tmp) / "058_example.goal.md"
            goal.write_text("```yaml\nGOAL: 058\nSTATUS: OPEN\n```\n", encoding="utf-8")
            self.assertFalse(is_paused_goal(goal))

    def test_status_outside_machine_header_is_ignored(self) -> None:
        text = """# malformed goal
STATUS: PAUSED_RESTORABLE
"""
        self.assertIsNone(goal_status_text(text))

    def test_lexical_goal_id_is_not_yaml_11_octal(self) -> None:
        header = goal_machine_header_text("```yaml\nGOAL: 057\nSTATUS: OPEN\n```\n")
        self.assertIsNotNone(header)
        self.assertEqual(header["GOAL"], "057")

    def test_duplicate_machine_key_is_rejected(self) -> None:
        text = "```yaml\nGOAL: 057\nSTATUS: OPEN\nSTATUS: PAUSED_RESTORABLE\n```\n"
        self.assertIsNone(goal_machine_header_text(text))
        self.assertIsNone(goal_status_text(text))

    def test_duplicate_nested_machine_key_is_rejected(self) -> None:
        text = """```yaml
GOAL: 057
STATUS: OPEN
phase_key:
  route_id: RouteA
  route_id: RouteB
```
"""
        self.assertIsNone(goal_machine_header_text(text))

    def test_live_packet_selector_sees_paused_057_and_open_058(self) -> None:
        goals = packet._collect_goals()
        by_root = {
            goal.label.split("_", 1)[0]: goal
            for goal in goals
            if goal.label.startswith(("057_", "058_"))
        }
        self.assertTrue(by_root["057"].paused)
        self.assertFalse(by_root["057"].answered)
        self.assertFalse(by_root["058"].paused)
        self.assertFalse(by_root["058"].answered)


if __name__ == "__main__":
    unittest.main()
