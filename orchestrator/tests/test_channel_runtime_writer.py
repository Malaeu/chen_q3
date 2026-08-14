"""Plants for the atomic CHANNEL_RUNTIME delegated-review writer."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from orchestrator import spine


def fixture_runtime() -> dict[str, object]:
    runtime = json.loads(spine.CHANNEL_RUNTIME.read_text(encoding="utf-8"))
    runtime.pop("recorded_review_events", None)
    runtime["active_proshka_phase"]["proshka_calls"] = 9
    runtime["meter"]["delegated_strategic_review_calls"] = 11
    return runtime


def event(**updates: object) -> dict[str, object]:
    runtime = json.loads(spine.CHANNEL_RUNTIME.read_text(encoding="utf-8"))
    payload: dict[str, object] = {
        "request_message_id": "request-10",
        "conversation_id": runtime["active_proshka_phase"]["conversation_id"],
        "boundary_id": "GOAL_056_PHASE4J_GENERIC_HILBERT_BASIS_WEIGHTED_TAIL",
        "adjudicated_pin": "0dea3fc20e0b0af45ed8aad50eed578a1a485b54",
        "phase_call_index": 10,
        "meter_call_index": 12,
    }
    payload.update(updates)
    return payload


class ChannelRuntimeWriterTests(unittest.TestCase):
    def test_records_review_and_updates_both_meters(self) -> None:
        updated, changed = spine.record_delegated_review(fixture_runtime(), event())
        self.assertTrue(changed)
        self.assertEqual(updated["active_proshka_phase"]["proshka_calls"], 10)
        self.assertEqual(updated["meter"]["delegated_strategic_review_calls"], 12)
        self.assertEqual(updated["active_proshka_phase"]["last_adjudicated_pin"],
                         "0dea3fc20e0b0af45ed8aad50eed578a1a485b54")

    def test_identical_replay_is_idempotent(self) -> None:
        updated, _ = spine.record_delegated_review(fixture_runtime(), event())
        replayed, changed = spine.record_delegated_review(updated, event())
        self.assertFalse(changed)
        self.assertEqual(replayed, updated)

    def test_missing_sequence_number_fails_closed(self) -> None:
        with self.assertRaises(spine.ControlViolation) as caught:
            spine.record_delegated_review(
                fixture_runtime(), event(phase_call_index=11, meter_call_index=13),
            )
        self.assertEqual(caught.exception.code, "EXPLORATION_RUNTIME_MISSING")

    def test_other_chat_fails_closed(self) -> None:
        with self.assertRaises(spine.ControlViolation) as caught:
            spine.record_delegated_review(
                fixture_runtime(), event(conversation_id="fresh-chat"),
            )
        self.assertEqual(caught.exception.code, "EXPLORATION_CHAT_FANOUT")

    def test_atomic_writer_round_trip_is_canonical(self) -> None:
        updated, _ = spine.record_delegated_review(fixture_runtime(), event())
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "CHANNEL_RUNTIME.json"
            spine.write_runtime_atomic(updated, path)
            raw = path.read_text(encoding="utf-8")
            self.assertEqual(raw, json.dumps(updated, ensure_ascii=False,
                                             indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    unittest.main()
