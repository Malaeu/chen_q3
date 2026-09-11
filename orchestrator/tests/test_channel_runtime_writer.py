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
        self.assertEqual(
            updated["recorded_review_events"][:-1], original["recorded_review_events"]
        )
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
                mock.patch(
                    "orchestrator.workflow_runtime.team_guard", return_value=None
                ) as guard,
                mock.patch.object(spine, "record_observed_bridge_transition", interrupted_record),
                mock.patch.object(spine, "write_runtime_atomic") as write,
                mock.patch("sys.argv", ["spine", "--record-bridge-transition", str(event_path)]),
            ):
                self.assertEqual(spine.main(), 2)
                write.assert_not_called()
            guard.assert_called_once_with(
                spine.REPO,
                command="bridge-observed-phase-repair",
                paths=["orchestrator/state/CHANNEL_RUNTIME.json"],
            )
            self.assertIn("recheck", events)
            self.assertEqual(runtime_path.read_bytes(), self.raw + b" ")

    def test_cli_owner_epoch_and_pending_holds_precede_any_bridge_write(self):
        from contextlib import contextmanager
        from types import SimpleNamespace
        from unittest import mock
        from orchestrator.workflow_runtime import WorkflowRuntimeError

        with tempfile.TemporaryDirectory() as tmp:
            runtime_path = Path(tmp) / "runtime.json"
            event_path = Path(tmp) / "event.json"
            runtime_path.write_bytes(self.raw)
            event_path.write_text(json.dumps(self.event), encoding="utf-8")
            events = []

            @contextmanager
            def writer_epoch(repo):
                events.append("lock")
                yield SimpleNamespace(recheck=lambda: None)

            for code in (
                "TEAM_INTEGRATION_PENDING:existing-operation",
                "TEAM_OBSERVER_ONLY:owner installation/task mismatch",
                "TEAM_CALLER_EPOCH_CHANGED",
                "TEAM_OWNER_RECONCILIATION_REQUIRED",
            ):
                events.clear()

                def refused_guard(*args, **kwargs):
                    self.assertEqual(events, ["lock"])
                    raise WorkflowRuntimeError(code)

                with (
                    self.subTest(code=code),
                    mock.patch("orchestrator.workflow_runtime._execution_writer_epoch", writer_epoch),
                    mock.patch("orchestrator.workflow_runtime.team_guard", side_effect=refused_guard) as guard,
                    mock.patch.object(spine, "CHANNEL_RUNTIME", runtime_path),
                    mock.patch.object(spine, "_validate_active_control") as control,
                    mock.patch.object(spine, "record_observed_bridge_transition") as record,
                    mock.patch.object(spine, "write_runtime_atomic") as write,
                    mock.patch("sys.argv", ["spine", "--record-bridge-transition", str(event_path)]),
                ):
                    with self.assertRaisesRegex(WorkflowRuntimeError, code):
                        spine.main()
                    guard.assert_called_once_with(
                        spine.REPO,
                        command="bridge-observed-phase-repair",
                        paths=["orchestrator/state/CHANNEL_RUNTIME.json"],
                    )
                    control.assert_not_called()
                    record.assert_not_called()
                    write.assert_not_called()
                    self.assertEqual(runtime_path.read_bytes(), self.raw)

    def test_pin_verifier_checks_exact_bytes(self):
        pin = self.receipt["opening_request"]
        self.assertIn(
            "REQUEST_ID: REQ-2026-09-09-BRIDGE", spine._phase_record_pin(pin, repo=spine.REPO)
        )
        with self.assertRaisesRegex(spine.ControlViolation, "PHASE_RECORD_INVALID"):
            spine._phase_record_pin({**pin, "sha256": "0" * 64}, repo=spine.REPO)


class ObservedSlackManualReviewTests(unittest.TestCase):
    """Regression checks for the one observed owner-manual SLACK transport."""

    def setUp(self) -> None:
        import subprocess

        self.raw = subprocess.check_output(
            [
                "git",
                "show",
                "8a463c090d0c1d28568c05fe67f4891287e1405f:"
                "orchestrator/state/CHANNEL_RUNTIME.json",
            ],
            cwd=spine.REPO,
        )
        self.event = {
            "expected_runtime_sha256": spine.SLACK_MANUAL_REVIEW_PREIMAGE,
            "repair_id": spine.SLACK_MANUAL_REVIEW_ID,
            **{name: dict(pin) for name, pin in spine.SLACK_MANUAL_REVIEW_PINS.items()},
        }

    def run_record(self, raw=None, event=None, recorded_at="2026-09-11T16:00:00+02:00"):
        return spine.record_observed_slack_manual_review(
            self.raw if raw is None else raw,
            self.event if event is None else event,
            recorded_at=recorded_at,
        )

    def test_reconciles_only_the_observed_handle_and_review(self):
        original = json.loads(self.raw)
        updated, changed = self.run_record()
        self.assertTrue(changed)
        archive = updated["observed_manual_review_repairs"][0]
        self.assertEqual(archive["predecessor_phase"], original["active_proshka_phase"])
        self.assertEqual(archive["predecessor_meter"], original["meter"])
        self.assertEqual(archive["preimage_sha256"], hashlib.sha256(self.raw).hexdigest())
        self.assertFalse(archive["receipt"]["attachment_tile_observed"])
        self.assertEqual(
            updated["active_proshka_phase"]["phase_key"],
            original["active_proshka_phase"]["phase_key"],
        )
        self.assertEqual(
            updated["active_proshka_phase"]["phase_id"],
            original["active_proshka_phase"]["phase_id"],
        )
        self.assertEqual(
            updated["active_proshka_phase"]["conversation_id"],
            "6aa3e75b-cfac-83ed-a4e2-f7d3d81f5d59",
        )
        self.assertEqual(updated["active_proshka_phase"]["proshka_calls"], 7)
        self.assertEqual(updated["meter"]["delegated_strategic_review_calls"], 52)
        self.assertEqual(updated["meter"]["phases_opened"], 3)
        self.assertEqual(updated["meter"]["fresh_chats_opened"], 4)
        self.assertEqual(updated["meter"]["forced_rollovers"], 2)
        self.assertEqual(updated["recorded_review_events"][:-1], original["recorded_review_events"])
        for key in original.keys() - {
            "active_proshka_phase", "meter", "recorded_review_events",
        }:
            self.assertEqual(updated[key], original[key])

    def test_pinned_fixture_ignores_an_isolated_successor_runtime(self):
        from unittest import mock

        successor, _ = self.run_record()
        with tempfile.TemporaryDirectory() as tmp:
            successor_path = Path(tmp) / "CHANNEL_RUNTIME.json"
            successor_path.write_text(json.dumps(successor), encoding="utf-8")
            with mock.patch.object(spine, "CHANNEL_RUNTIME", successor_path):
                self.setUp()
                rebuilt, changed = self.run_record()
        self.assertTrue(changed)
        self.assertEqual(rebuilt, successor)

    def test_identical_replay_is_noop_after_a_later_legitimate_review(self):
        updated, _ = self.run_record()
        later, changed = spine.record_delegated_review(
            updated,
            {
                "request_message_id": "later-legitimate-review",
                "conversation_id": "6aa3e75b-cfac-83ed-a4e2-f7d3d81f5d59",
                "boundary_id": "GOAL058_LATER_LEGITIMATE_REVIEW",
                "adjudicated_pin": "1" * 40,
                "phase_call_index": 8,
                "meter_call_index": 53,
            },
        )
        self.assertTrue(changed)
        replayed, changed = self.run_record(raw=json.dumps(later).encode("utf-8"))
        self.assertFalse(changed)
        self.assertEqual(replayed, later)
        self.assertEqual(replayed["active_proshka_phase"]["proshka_calls"], 8)
        self.assertEqual(replayed["meter"]["delegated_strategic_review_calls"], 53)

    def test_stale_preimage_and_malformed_history_fail_closed(self):
        with self.assertRaisesRegex(spine.ControlViolation, "PHASE_RECORD_STALE_PREIMAGE"):
            self.run_record(raw=self.raw + b" ")
        malformed = json.loads(self.raw)
        malformed["observed_manual_review_repairs"] = ["not-an-object"]
        with self.assertRaisesRegex(spine.ControlViolation, "PHASE_RECORD_INVALID"):
            self.run_record(raw=json.dumps(malformed).encode("utf-8"))

    def test_conflicting_replay_and_closed_event_schema_are_rejected(self):
        updated, _ = self.run_record()
        updated["observed_manual_review_repairs"][0]["receipt"]["conversation_id"] = "foreign"
        with self.assertRaisesRegex(spine.ControlViolation, "PHASE_RECORD_REPLAY_CONFLICT"):
            self.run_record(raw=json.dumps(updated).encode("utf-8"))
        updated, _ = self.run_record()
        updated["observed_manual_review_repairs"][0].pop("predecessor_meter")
        with self.assertRaisesRegex(spine.ControlViolation, "PHASE_RECORD_REPLAY_CONFLICT"):
            self.run_record(raw=json.dumps(updated).encode("utf-8"))
        updated, _ = self.run_record()
        updated["recorded_review_events"] = [
            item for item in updated["recorded_review_events"]
            if item["request_message_id"] != "57e6f47f-d70f-4281-97fb-3f2b7641563d"
        ]
        with self.assertRaisesRegex(spine.ControlViolation, "PHASE_RECORD_REPLAY_CONFLICT"):
            self.run_record(raw=json.dumps(updated).encode("utf-8"))
        updated, _ = self.run_record()
        updated["observed_manual_review_repairs"][0]["event"] = "not-an-object"
        with self.assertRaisesRegex(spine.ControlViolation, "PHASE_RECORD_INVALID"):
            self.run_record(raw=json.dumps(updated).encode("utf-8"))
        cases = [
            ("status", ("active_proshka_phase", "status"), "CLOSED"),
            ("conversation", ("active_proshka_phase", "conversation_id"), "foreign-chat"),
            ("phase_id", ("active_proshka_phase", "phase_id"), "foreign-phase"),
            ("phase_calls", ("active_proshka_phase", "proshka_calls"), 6),
            ("meter_calls", ("meter", "delegated_strategic_review_calls"), 51),
            ("phases", ("meter", "phases_opened"), 2),
            ("fresh_chats", ("meter", "fresh_chats_opened"), 3),
            ("forced_rollovers", ("meter", "forced_rollovers"), 1),
        ]
        cases.extend(
            (
                f"phase_key_{field}",
                ("active_proshka_phase", "phase_key", field),
                f"foreign-{field}",
            )
            for field in spine.PHASE_KEY_FIELDS
        )
        for label, path, value in cases:
            candidate = json.loads(json.dumps(self.run_record()[0]))
            target = candidate
            for key in path[:-1]:
                target = target[key]
            target[path[-1]] = value
            with self.subTest(replay_state=label), self.assertRaisesRegex(
                spine.ControlViolation, "PHASE_RECORD_REPLAY_CONFLICT"
            ):
                self.run_record(raw=json.dumps(candidate).encode("utf-8"))
        with self.assertRaisesRegex(spine.ControlViolation, "PHASE_RECORD_INVALID"):
            self.run_record(event={**self.event, "transport_mode": "CANONICAL_ATTACHMENT"})
        for name in spine.SLACK_MANUAL_REVIEW_PINS:
            candidate = json.loads(json.dumps(self.event))
            candidate[name]["sha256"] = "0" * 64
            with self.subTest(pin=name), self.assertRaisesRegex(
                spine.ControlViolation, "PHASE_RECORD_INVALID"
            ):
                self.run_record(event=candidate)

    def test_duplicate_headers_wrong_lock_and_false_tile_are_rejected(self):
        from unittest import mock

        original_reader = spine._phase_record_pin

        def run_with(source_name, replacement):
            def reader(pin, *, repo):
                if pin == self.event[source_name]:
                    return replacement
                return original_reader(pin, repo=repo)

            with mock.patch.object(spine, "_phase_record_pin", side_effect=reader):
                with self.assertRaisesRegex(spine.ControlViolation, "PHASE_RECORD_INVALID"):
                    self.run_record()

        request = original_reader(self.event["request_pin"], repo=spine.REPO)
        run_with(
            "request_pin",
            request.replace(
                "REQUEST_ID: REQ-2026-09-11-SLACK",
                "REQUEST_ID: REQ-2026-09-11-SLACK\nREQUEST_ID: REQ-2026-09-11-SLACK",
                1,
            ),
        )
        verdict = original_reader(self.event["verdict_pin"], repo=spine.REPO)
        run_with(
            "verdict_pin",
            verdict.replace(
                "  COMMIT: d92fd17e78b28fe93939e6b94becf1b90c68dddc",
                "  COMMIT: " + "0" * 40,
                1,
            ),
        )
        receipt = original_reader(self.event["receipt_pin"], repo=spine.REPO)
        run_with(
            "receipt_pin",
            receipt.replace(
                "Exact attachment tile was not observed",
                "Exact attachment tile was observed",
                1,
            ),
        )

    def test_recording_before_acceptance_and_atomic_failure_leave_no_write(self):
        with self.assertRaisesRegex(spine.ControlViolation, "PHASE_RECORD_INVALID"):
            self.run_record(recorded_at="2026-09-11T14:50:00+02:00")
        updated, _ = self.run_record()
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "CHANNEL_RUNTIME.json"
            original = b"original bytes\n"
            path.write_bytes(original)
            from unittest import mock

            with mock.patch(
                "orchestrator.spine.os.replace", side_effect=OSError("replace failed")
            ):
                with self.assertRaises(OSError):
                    spine.write_runtime_atomic(updated, path)
            self.assertEqual(path.read_bytes(), original)

    def test_cli_rechecks_raw_before_replacement(self):
        from contextlib import contextmanager
        from types import SimpleNamespace
        from unittest import mock

        with tempfile.TemporaryDirectory() as tmp:
            runtime_path = Path(tmp) / "runtime.json"
            event_path = Path(tmp) / "event.json"
            runtime_path.write_bytes(self.raw)
            event_path.write_text(json.dumps(self.event), encoding="utf-8")
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
                mock.patch(
                    "orchestrator.workflow_runtime.build_startup_snapshot",
                    return_value=SimpleNamespace(fatal_errors=()),
                ),
                mock.patch(
                    "orchestrator.workflow_runtime.team_guard", return_value=None
                ) as guard,
                mock.patch.object(
                    spine, "record_observed_slack_manual_review", interrupted_record
                ),
                mock.patch.object(spine, "write_runtime_atomic") as write,
                mock.patch("sys.argv", ["spine", "--record-slack-manual-review", str(event_path)]),
            ):
                self.assertEqual(spine.main(), 2)
                write.assert_not_called()
            guard.assert_called_once_with(
                spine.REPO,
                command="slack-manual-chat-reconciliation",
                paths=["orchestrator/state/CHANNEL_RUNTIME.json"],
            )
            self.assertIn("recheck", events)
            self.assertEqual(runtime_path.read_bytes(), self.raw + b" ")

    def test_cli_rejects_startup_fatal_but_keeps_scoped_hold_eligible(self):
        from contextlib import contextmanager
        from types import SimpleNamespace
        from unittest import mock

        with tempfile.TemporaryDirectory() as tmp:
            runtime_path = Path(tmp) / "runtime.json"
            event_path = Path(tmp) / "event.json"
            runtime_path.write_bytes(self.raw)
            event_path.write_text(json.dumps(self.event), encoding="utf-8")

            @contextmanager
            def writer_epoch(repo):
                yield SimpleNamespace(recheck=lambda: None)

            with (
                mock.patch("orchestrator.workflow_runtime._execution_writer_epoch", writer_epoch),
                mock.patch.object(spine, "CHANNEL_RUNTIME", runtime_path),
                mock.patch.object(spine, "_validate_active_control"),
                mock.patch(
                    "orchestrator.workflow_runtime.build_startup_snapshot",
                    return_value=SimpleNamespace(fatal_errors=("STARTUP_FATAL",)),
                ),
                mock.patch(
                    "orchestrator.workflow_runtime.team_guard", return_value=None
                ),
                mock.patch.object(spine, "record_observed_slack_manual_review") as record,
                mock.patch.object(spine, "write_runtime_atomic") as write,
                mock.patch("sys.argv", ["spine", "--record-slack-manual-review", str(event_path)]),
            ):
                self.assertEqual(spine.main(), 2)
                record.assert_not_called()
                write.assert_not_called()

            with (
                mock.patch("orchestrator.workflow_runtime._execution_writer_epoch", writer_epoch),
                mock.patch.object(spine, "CHANNEL_RUNTIME", runtime_path),
                mock.patch.object(spine, "_validate_active_control"),
                mock.patch(
                    "orchestrator.workflow_runtime.build_startup_snapshot",
                    return_value=SimpleNamespace(fatal_errors=(), run_authorized=False),
                ),
                mock.patch(
                    "orchestrator.workflow_runtime.team_guard", return_value=None
                ),
                mock.patch.object(
                    spine,
                    "record_observed_slack_manual_review",
                    return_value=(json.loads(self.raw), False),
                ) as record,
                mock.patch.object(spine, "write_runtime_atomic") as write,
                mock.patch("sys.argv", ["spine", "--record-slack-manual-review", str(event_path)]),
            ):
                self.assertEqual(spine.main(), 0)
                record.assert_called_once()
                write.assert_not_called()


if __name__ == "__main__":
    unittest.main()
