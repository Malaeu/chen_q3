"""K1 plants for the closed AUTOPSY schema, wall map and namewatch."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts import build_autopsy_map as autopsy
from orchestrator import packet


def event(goal: str, front: str, tag: str, shape: str | None) -> dict[str, object]:
    return {
        "id": f"{goal}_{front}_{tag}_{shape}", "source_file": f"{goal}.md",
        "source_line": 1, "goal_id": goal, "front": front, "tag": tag,
        "note": "fixture", "shape": shape, "structured": True,
        "namewatch_eligible": bool(shape), "raw_sha256": "a" * 64,
    }


class AutopsyPlants(unittest.TestCase):
    def test_structured_line_is_parsed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "101_alpha.answer.md"
            path.write_text(
                "front: FRONT_A\nAUTOPSY: dropped=DOMAIN; note=shape=TYPE_MISMATCH | domains differ\n",
                encoding="utf-8",
            )
            rows = autopsy.parse_file(path, repo=Path(tmp))
        self.assertEqual(rows[0]["tag"], "DOMAIN")
        self.assertEqual(rows[0]["shape"], "TYPE_MISMATCH")
        self.assertTrue(rows[0]["namewatch_eligible"])

    def test_unknown_tag_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "101_alpha.answer.md"
            path.write_text("AUTOPSY: dropped=MADE_UP; note=x\n", encoding="utf-8")
            with self.assertRaisesRegex(autopsy.AutopsyError, "unknown tag"):
                autopsy.parse_file(path, repo=Path(tmp))

    def test_legacy_is_visible_but_ineligible(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "101_alpha.answer.md"
            path.write_text("AUTOPSY: old prose\n", encoding="utf-8")
            row = autopsy.parse_file(path, repo=Path(tmp))[0]
        self.assertEqual(row["tag"], "LEGACY_UNCLASSIFIED")
        self.assertFalse(row["namewatch_eligible"])

    def test_same_shape_two_goals_two_fronts_flags(self) -> None:
        rows = [event("101", "A", "DOMAIN", "TYPE_MISMATCH"),
                event("102", "B", "DOMAIN", "TYPE_MISMATCH")]
        result = autopsy.derive(rows, [], {})
        self.assertEqual(len(result["namewatch_candidates"]), 1)
        self.assertFalse(result["namewatch_candidates"][0]["auto_promoted"])

    def test_different_shapes_do_not_flag(self) -> None:
        rows = [event("101", "A", "DOMAIN", "TYPE_A"),
                event("102", "B", "DOMAIN", "TYPE_B")]
        self.assertEqual(autopsy.derive(rows, [], {})["namewatch_candidates"], [])

    def test_same_goal_or_same_front_does_not_flag(self) -> None:
        same_goal = [event("101", "A", "DOMAIN", "TYPE_A"),
                     event("101", "B", "DOMAIN", "TYPE_A")]
        same_front = [event("101", "A", "DOMAIN", "TYPE_A"),
                      event("102", "A", "DOMAIN", "TYPE_A")]
        self.assertFalse(autopsy.derive(same_goal, [], {})["namewatch_candidates"])
        self.assertFalse(autopsy.derive(same_front, [], {})["namewatch_candidates"])

    def test_registered_wall_coverage_suppresses_flag(self) -> None:
        rows = [event("101", "A", "DOMAIN", "TYPE_A"),
                event("102", "B", "DOMAIN", "TYPE_A")]
        walls = [{"id": "W_DOMAIN", "coverage_tags": ["DOMAIN"],
                  "dropped_structure": "domain", "status": "REGISTERED"}]
        self.assertFalse(autopsy.derive(rows, walls, {})["namewatch_candidates"])

    def test_card_coverage_suppresses_flag(self) -> None:
        rows = [event("101", "A", "PARITY", "EVEN_ODD"),
                event("102", "B", "PARITY", "EVEN_ODD")]
        self.assertFalse(autopsy.derive(rows, [], {"PARITY": "C08"})["namewatch_candidates"])

    def test_negative_close_requires_structured_autopsy(self) -> None:
        with self.assertRaisesRegex(packet.PacketError, "AUTOPSY_REQUIRED_MISSING"):
            packet.validate_autopsy_close_gate("# STATUS: KILLED\n", "KILLED")

    def test_malformed_new_autopsy_fails(self) -> None:
        with self.assertRaisesRegex(packet.PacketError, "AUTOPSY_SCHEMA_INVALID"):
            packet.validate_autopsy_close_gate(
                "AUTOPSY: old free text\n", "WALL",
            )

    def test_valid_negative_close_passes(self) -> None:
        self.assertEqual(
            packet.validate_autopsy_close_gate(
                "AUTOPSY: dropped=DOMAIN; note=shape=TYPE_MISMATCH | domains differ\n",
                "INCONCLUSIVE",
            ),
            "AUTOPSY_CLOSE_GATE_PASS",
        )


if __name__ == "__main__":
    unittest.main()
