"""Plants for the atomic CHANNEL_RUNTIME delegated-review writer."""

from __future__ import annotations

import hashlib
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


class ObservedBridgeTransitionTests(unittest.TestCase):
    """Regression checks for the single already observed BRIDGE transition."""

    def setUp(self) -> None:
        import subprocess

        self.raw = subprocess.check_output(
            [
                "git",
                "show",
                "57df552a4a12c7e557d0be2938e05c09060aa2e2:orchestrator/state/CHANNEL_RUNTIME.json",
            ],
            cwd=spine.REPO,
        )
        self.receipt = {
            "schema": "q3_observed_phase_transition.v1",
            "transition_id": "REQ-2026-09-09-BRIDGE",
            "observed_at": "2026-09-10T08:33:00+02:00",
            "conversation_id": "6aa24f25-0934-83eb-9151-3565fc4b3379",
            "request_message_id": "42601c8e-ad3b-47de-b2aa-706c74cd9184",
            "response_message_id": "b9b96355-7515-4611-ab05-4fe88c76d963",
        }

        def pin(commit, path):
            raw = subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=spine.REPO)
            return {
                "commit": commit,
                "path": path,
                "blob": subprocess.check_output(
                    ["git", "rev-parse", f"{commit}:{path}"], cwd=spine.REPO, text=True
                ).strip(),
                "sha256": hashlib.sha256(raw).hexdigest(),
            }

        self.receipt["opening_request"] = pin(
            "b968f9443d5491778ab5e65c75c4ad7d64ba0b14",
            "docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_BRIDGE_2026-09-09.txt",
        )
        self.receipt["verdict"] = pin(
            "4ae462655affe4e3511a765a54a04a6510338f72",
            "docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_BRIDGE_2026-09-09.md",
        )
        grant = pin("57df552a4a12c7e557d0be2938e05c09060aa2e2", "docs/Codex/GOAL.md")
        text = spine._phase_record_pin(grant, repo=spine.REPO)
        self.receipt["owner_authorization"] = {
            "source": grant,
            "locator": (
                "section 5, opening paragraph; owner new-chat instruction in current Codex task "
                "01a084f4-7498-7021-bac2-91d184d58dc7"
            ),
            "quote": next(
                line for line in text.splitlines() if line.startswith("SCHUR независимо проверен")
            ),
        }
        self.event = {
            "expected_runtime_sha256": hashlib.sha256(self.raw).hexdigest(),
            "receipt_pin": {"test": "queue-receipt", "path": "docs/routeB_bus/PROSHKA_QUEUE.md"},
            "transition_id": self.receipt["transition_id"],
        }

    def run_record(self, raw=None, event=None, receipt=None):
        from unittest import mock

        read_pin = spine._phase_record_pin
        selected = self.receipt if receipt is None else receipt
        text = (
            "<!-- observed-phase-transition:REQ-2026-09-09-BRIDGE -->\n```json\n"
            + json.dumps(selected)
            + "\n```\n"
        )

        def read(pin, *, repo):
            return text if pin == self.event["receipt_pin"] else read_pin(pin, repo=repo)

        with mock.patch.object(spine, "_phase_record_pin", side_effect=read):
            return spine.record_observed_bridge_transition(
                self.raw if raw is None else raw,
                self.event if event is None else event,
                recorded_at="2026-09-10T11:00:00+02:00",
            )

    def test_preserves_history_and_production_state_and_reuses_literal_phase_id(self):
        original = json.loads(self.raw)
        updated, changed = self.run_record()
        self.assertTrue(changed)
        archived = updated["observed_phase_transitions"][0]
        self.assertEqual(archived["predecessor_phase"], original["active_proshka_phase"])
        self.assertEqual(archived["predecessor_meter"], original["meter"])
        self.assertEqual(archived["preimage_sha256"], hashlib.sha256(self.raw).hexdigest())
        self.assertTrue(archived["late_recording"])
        self.assertNotEqual(archived["observed_at"], archived["recorded_at"])
        self.assertEqual(updated["recorded_review_events"][:-1], original["recorded_review_events"])
        for key in original.keys() - {"active_proshka_phase", "meter", "recorded_review_events"}:
            self.assertEqual(updated[key], original[key])
        self.assertEqual(
            updated["active_proshka_phase"]["phase_id"],
            original["active_proshka_phase"]["phase_id"],
        )
        self.assertEqual(updated["active_proshka_phase"]["proshka_calls"], 1)
        self.assertEqual(updated["meter"]["delegated_strategic_review_calls"], 46)
        self.assertEqual(updated["meter"]["phases_opened"], original["meter"]["phases_opened"] + 1)
        self.assertEqual(
            updated["meter"]["fresh_chats_opened"], original["meter"]["fresh_chats_opened"] + 1
        )

    def test_replay_idempotent_but_divergent_event_or_successor_rejected(self):
        updated, _ = self.run_record()
        raw = json.dumps(updated).encode()
        replay, changed = self.run_record(raw=raw)
        self.assertFalse(changed)
        self.assertEqual(replay, updated)
        with self.assertRaisesRegex(spine.ControlViolation, "PHASE_RECORD_REPLAY_CONFLICT"):
            self.run_record(raw=raw, event={**self.event, "expected_runtime_sha256": "0" * 64})
        updated["active_proshka_phase"]["phase_key"]["front_id"] = "foreign"
        with self.assertRaisesRegex(spine.ControlViolation, "PHASE_RECORD_REPLAY_CONFLICT"):
            self.run_record(raw=json.dumps(updated).encode())

    def test_stale_preimage_rejected(self):
        with self.assertRaisesRegex(spine.ControlViolation, "PHASE_RECORD_STALE_PREIMAGE"):
            self.run_record(raw=self.raw + b" ")

    def test_pins_and_observations_cannot_be_substituted(self):
        for field in (
            "conversation_id",
            "request_message_id",
            "response_message_id",
            "observed_at",
        ):
            with self.subTest(field=field), self.assertRaises(spine.ControlViolation):
                self.run_record(receipt={**self.receipt, field: "foreign"})
        for field in ("commit", "path", "blob", "sha256"):
            for side in ("opening_request", "verdict"):
                candidate = json.loads(json.dumps(self.receipt))
                candidate[side][field] = "wrong"
                with (
                    self.subTest(side=side, field=field),
                    self.assertRaises(spine.ControlViolation),
                ):
                    self.run_record(receipt=candidate)
        candidate = json.loads(json.dumps(self.receipt))
        candidate["owner_authorization"]["quote"] = "invented authorization"
        with self.assertRaises(spine.ControlViolation):
            self.run_record(receipt=candidate)

    def test_preexisting_new_chat_is_a_foreign_preimage(self):
        original = json.loads(self.raw)
        original["recorded_review_events"].append(
            {"request_message_id": "already", "conversation_id": self.receipt["conversation_id"]}
        )
        raw = json.dumps(original).encode()
        with self.assertRaisesRegex(spine.ControlViolation, "PHASE_RECORD_STALE_PREIMAGE"):
            self.run_record(
                raw=raw,
                event={**self.event, "expected_runtime_sha256": hashlib.sha256(raw).hexdigest()},
            )

    def test_same_boundary_with_different_message_is_rejected(self):
        updated, _ = self.run_record()
        last = dict(updated["recorded_review_events"][-1])
        last.update(request_message_id="another", phase_call_index=2, meter_call_index=47)
        with self.assertRaisesRegex(spine.ControlViolation, "EXPLORATION_REVIEW_DUPLICATE"):
            spine.record_delegated_review(updated, last)

    def test_cli_holds_writer_lock_and_rejects_changed_raw_preimage(self):
        from contextlib import contextmanager
        from unittest import mock

        with tempfile.TemporaryDirectory() as tmp:
            runtime_path = Path(tmp) / "runtime.json"
            event_path = Path(tmp) / "event.json"
            runtime_path.write_bytes(self.raw)
            event_path.write_text(json.dumps(self.event))
            events = []

            class Epoch:
                def recheck(self):
                    events.append("recheck")

            @contextmanager
            def writer_epoch(repo):
                events.append("lock")
                yield Epoch()
                events.append("unlock")

            def interrupted_record(raw, event, *, recorded_at):
                self.assertEqual(events, ["lock"])
                runtime_path.write_bytes(raw + b" ")
                return json.loads(raw), True

            with (
                mock.patch("orchestrator.workflow_runtime._execution_writer_epoch", writer_epoch),
                mock.patch.object(spine, "CHANNEL_RUNTIME", runtime_path),
                mock.patch.object(spine, "_validate_active_control"),
                mock.patch.object(spine, "record_observed_bridge_transition", interrupted_record),
                mock.patch.object(spine, "write_runtime_atomic") as write,
                mock.patch("sys.argv", ["spine", "--record-bridge-transition", str(event_path)]),
            ):
                self.assertEqual(spine.main(), 2)
                write.assert_not_called()
            self.assertIn("recheck", events)
            self.assertEqual(runtime_path.read_bytes(), self.raw + b" ")

    def test_pin_verifier_checks_exact_bytes(self):
        pin = self.receipt["opening_request"]
        self.assertIn(
            "REQUEST_ID: REQ-2026-09-09-BRIDGE", spine._phase_record_pin(pin, repo=spine.REPO)
        )
        with self.assertRaisesRegex(spine.ControlViolation, "PHASE_RECORD_INVALID"):
            spine._phase_record_pin({**pin, "sha256": "0" * 64}, repo=spine.REPO)


if __name__ == "__main__":
    unittest.main()
