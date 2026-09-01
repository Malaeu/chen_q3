"""Four source-locked AUTOPILOT_000 selector plants and contract tests."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from orchestrator import goal_runtime, three_body_loop

PHASE = {
    "route_id": "ROUTE",
    "front_id": "FRONT",
    "source_object_family_id": "SOURCE",
    "terminal_consumer_id": "CONSUMER",
    "honesty_state": "CHALLENGER_NOT_RH",
    "convention_lock_id": "LOCK",
}


class GoalRuntimePlants(unittest.TestCase):
    @staticmethod
    def _bind_spec_source(root: Path, spec: dict[str, object]) -> None:
        goal_runtime._bind_plant_spec(root, spec)

    @staticmethod
    def _write_canonical_phase(root: Path, phase: dict[str, str]) -> None:
        runtime_path = root / "orchestrator" / "state" / "CHANNEL_RUNTIME.json"
        runtime_path.parent.mkdir(parents=True, exist_ok=True)
        runtime_path.write_text(
            '{"active_proshka_phase":{"status":"ACTIVE",'
            '"conversation_id":"plant-conversation","phase_key":'
            + json.dumps(phase)
            + "}}\n",
            encoding="utf-8",
        )
        quarantine = root / "orchestrator" / "state" / "SEMANTIC_QUARANTINE.json"
        quarantine.write_text(
            json.dumps(
                {
                    "active_lease": None,
                    "control_version": 9,
                    "entries": [],
                    "event_ledger": [],
                    "schema": "q3_semantic_quarantine.v1",
                    "tactical_repairs": [],
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )

    @staticmethod
    def _grant(runtime: dict[str, object]) -> dict[str, object]:
        return {
            "schema": "q3_operational_grant_resolution.v1",
            "grant_id": runtime["operational_grant_id"],
            "status": "ACTIVE",
            "scope_goal_file": runtime["goal_file"],
            "allowed_actions": [runtime["next_action"]],
            "forbidden_actions": sorted(goal_runtime.REQUIRED_GRANT_FORBIDDENS),
        }

    @classmethod
    def _validate_runtime(
        cls, runtime: dict[str, object], *, root: Path
    ) -> dict[str, object]:
        grant = cls._grant(runtime)
        return goal_runtime.validate_runtime_state(
            runtime,
            repo_root=root,
            grant_resolver=lambda grant_id: grant if grant_id == grant["grant_id"] else None,
        )

    @staticmethod
    def _runtime_fixture(root: Path) -> dict[str, object]:
        bus = root / "docs" / "routeB_bus"
        bus.mkdir(parents=True, exist_ok=True)
        goal_runtime._write_goal(bus, "058", PHASE)
        goal = bus / "058_plant.goal.md"
        GoalRuntimePlants._write_canonical_phase(root, PHASE)
        if not (root / ".git").is_dir():
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        subprocess.run(["git", "add", "docs/routeB_bus/058_plant.goal.md"], cwd=root, check=True)
        staged = subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=root, check=False)
        if staged.returncode != 0:
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=AUTOPILOT Plant",
                    "-c",
                    "user.email=autopilot-plant@example.invalid",
                    "commit",
                    "-q",
                    "-m",
                    "plant goal source pin",
                ],
                cwd=root,
                check=True,
            )
        source_commit = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=root,
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout.strip()
        return {
            "schema": "q3_goal_run.v1",
            "goal_run_id": "GOAL058-20260813T120000Z",
            "goal_file": "docs/routeB_bus/058_plant.goal.md",
            "goal_sha256": hashlib.sha256(goal.read_bytes()).hexdigest(),
            "source_commit": source_commit,
            "answer_file": "docs/routeB_bus/058_plant.answer.md",
            "mathematical_phase_key_sha256": goal_runtime.phase_key_sha256(PHASE),
            "state": "RUNNING",
            "cycle_index": 3,
            "stall_counter": 1,
            "last_attempt_id": "ATTEMPT_GOAL058_003",
            "next_target": "ExactTarget",
            "next_action": "CONTINUE_STEP",
            "operational_grant_id": "AUTOPILOT_GRANT_001",
            "lease": {
                "holder": "CODEX_LINUX",
                "heartbeat_at": "2026-08-13T12:00:00+02:00",
            },
        }

    def test_P1_two_goal_numbers_keep_one_mathematical_phase(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            bus = Path(tmp)
            goal_runtime._write_goal(bus, "101", PHASE)
            goal_runtime._write_goal(bus, "102", PHASE)
            goals, _ = goal_runtime.scan_physical_goals(bus, repo_root=bus)
            self.assertEqual(
                {goal_runtime.phase_key_sha256(goal.phase_key) for goal in goals},
                {goal_runtime.phase_key_sha256(PHASE)},
            )

    def test_P2_two_executable_goals_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bus = root / "docs" / "routeB_bus"
            bus.mkdir(parents=True)
            goal_runtime._write_goal(bus, "101", PHASE)
            goal_runtime._write_goal(bus, "102", PHASE)
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_AMBIGUOUS_GOAL_SET"
            ):
                goal_runtime.select_action(bus, repo_root=root)

    def test_P3_post_outcome_spec_without_provenance_is_rejected(self) -> None:
        spec = goal_runtime._valid_spec(PHASE)
        spec["source_provenance"] = {}
        with self.assertRaisesRegex(
            goal_runtime.GoalRuntimeError,
            "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
        ):
            goal_runtime.validate_next_goal_spec(spec)

    def test_P4_px_rh_claim_cannot_advance(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec = goal_runtime._valid_spec(PHASE)
            spec["px_rh_claim"] = True
            self._bind_spec_source(root, spec)
            self._write_canonical_phase(root, PHASE)
            decision = goal_runtime.select_action(
                root / "docs" / "routeB_bus",
                next_goal_spec=spec,
                current_phase_key=PHASE,
                repo_root=root,
            )
            self.assertEqual(decision.action, "OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM")

    def test_valid_same_phase_spec_is_mint_ready_without_minting(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec = goal_runtime._valid_spec(PHASE)
            self._bind_spec_source(root, spec)
            self._write_canonical_phase(root, PHASE)
            before = sorted(path.relative_to(root) for path in root.rglob("*") if path.is_file())
            decision = goal_runtime.select_action(
                root / "docs" / "routeB_bus",
                next_goal_spec=spec,
                current_phase_key=PHASE,
                repo_root=root,
            )
            self.assertEqual(decision.action, "MINT_READY")
            after = sorted(path.relative_to(root) for path in root.rglob("*") if path.is_file())
            self.assertEqual(after, before)

    def test_phase_change_requires_transition(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            next_phase = dict(PHASE, front_id="NEXT_FRONT")
            spec = goal_runtime._valid_spec(next_phase)
            spec["phase_key_change"] = True
            self._bind_spec_source(root, spec)
            self._write_canonical_phase(root, PHASE)
            decision = goal_runtime.select_action(
                root / "docs" / "routeB_bus",
                next_goal_spec=spec,
                current_phase_key=PHASE,
                repo_root=root,
            )
            self.assertEqual(decision.action, "PHASE_TRANSITION_REQUIRED")

    def test_phase_change_declaration_drift_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            next_phase = dict(PHASE, front_id="NEXT_FRONT")
            spec = goal_runtime._valid_spec(next_phase)
            self._bind_spec_source(root, spec)
            self._write_canonical_phase(root, PHASE)
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError,
                "AUTOPILOT_PHASE_CHANGE_DECLARATION_DRIFT",
            ):
                goal_runtime.select_action(
                    root / "docs" / "routeB_bus",
                    next_goal_spec=spec,
                    current_phase_key=PHASE,
                    repo_root=root,
                )

    def test_unknown_unanswered_lifecycle_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bus = root / "docs" / "routeB_bus"
            bus.mkdir(parents=True)
            goal_runtime._write_goal(bus, "101", PHASE)
            goal = bus / "101_plant.goal.md"
            goal.write_text(
                goal.read_text(encoding="utf-8").replace(
                    "STATUS: OPEN", "STATUS: SUSPENDED_UNKNOWN"
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_UNKNOWN_GOAL_STATUS"
            ):
                goal_runtime.select_action(bus, repo_root=root)

    def test_paused_goal_is_physical_but_not_executable(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bus = root / "docs" / "routeB_bus"
            bus.mkdir(parents=True)
            goal_runtime._write_goal(bus, "101", PHASE)
            goal = bus / "101_plant.goal.md"
            goal.write_text(
                goal.read_text(encoding="utf-8").replace(
                    "STATUS: OPEN", "STATUS: PAUSED_RESTORABLE"
                ),
                encoding="utf-8",
            )
            executable, paused = goal_runtime.scan_physical_goals(bus, repo_root=bus)
            self.assertEqual(executable, [])
            self.assertEqual([item.goal_id for item in paused], ["101"])
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError,
                "AUTOPILOT_NEXT_GOAL_SPEC_MISSING",
            ):
                goal_runtime.select_action(bus, repo_root=root)

    def test_locally_forged_proshka_result_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec = goal_runtime._valid_spec(PHASE)
            self._bind_spec_source(root, spec)
            spec["source_provenance"]["origin"] = "OPERATIVE_PROSHKA_RESULT"
            spec["source_provenance"]["operative_class"] = "RUN_EXACT_TEST"
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError,
                "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
            ):
                goal_runtime.validate_next_goal_spec(spec, repo_root=root)

    def test_source_hash_drift_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec = goal_runtime._valid_spec(PHASE)
            self._bind_spec_source(root, spec)
            spec["source_provenance"]["source_sha256"] = "0" * 64
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError,
                "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
            ):
                goal_runtime.validate_next_goal_spec(spec, repo_root=root)

    def test_non_repo_relative_source_path_fails_closed(self) -> None:
        for source_path in ("../outside.md", "/etc/passwd", "docs/./CODEX_CONTROL.md"):
            with self.subTest(source_path=source_path):
                with tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    spec = goal_runtime._valid_spec(PHASE)
                    self._bind_spec_source(root, spec)
                    spec["source_provenance"]["source_path"] = source_path
                    with self.assertRaisesRegex(
                        goal_runtime.GoalRuntimeError,
                        "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
                    ):
                        goal_runtime.validate_next_goal_spec(spec, repo_root=root)

    def test_operative_class_must_exist_in_pinned_source(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec = goal_runtime._valid_spec(PHASE)
            self._bind_spec_source(root, spec)
            spec["source_provenance"]["origin"] = "OPERATIVE_PROSHKA_RESULT"
            spec["source_provenance"]["operative_class"] = "RUN_EXACT_TEST"
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError,
                "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
            ):
                goal_runtime.validate_next_goal_spec(spec, repo_root=root)

    def test_pinned_file_without_spec_semantics_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec = goal_runtime._valid_spec(PHASE)
            self._bind_spec_source(root, spec)
            spec["target_id"] = "POST_OUTCOME_INVENTION"
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError,
                "AUTOPILOT_NEXT_GOAL_SPEC_SOURCE_BINDING_INVALID",
            ):
                goal_runtime.validate_next_goal_spec(spec, repo_root=root)

    def test_precommit_spec_rejects_uncommitted_outcome_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec = goal_runtime._valid_spec(PHASE)
            self._bind_spec_source(root, spec)
            (root / "docs" / "routeB_bus" / "999_plant_guard.answer.md").write_text(
                "# outcome now exists\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError,
                "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
            ):
                goal_runtime.validate_next_goal_spec(spec, repo_root=root)

    def test_unstructured_frankenstein_spec_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec = goal_runtime._valid_spec(PHASE)
            self._bind_spec_source(root, spec)
            source = root / spec["source_provenance"]["source_path"]
            values = [
                spec["target_id"],
                spec["exact_statement_or_task"],
                spec["terminal_consumer"],
                spec["success_condition"],
                spec["failure_code"],
                *spec["source_objects"],
                *spec["required_inputs"],
                *spec["forbidden_shortcuts"],
                *spec["validation"],
            ]
            source.write_text("\n".join(values), encoding="utf-8")
            spec["source_provenance"]["source_sha256"] = hashlib.sha256(
                source.read_bytes()
            ).hexdigest()
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError,
                "AUTOPILOT_NEXT_GOAL_SPEC_PROVENANCE_INVALID",
            ):
                goal_runtime.validate_next_goal_spec(spec, repo_root=root)

    def test_runtime_schema_rejects_unknown_fields(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runtime = self._runtime_fixture(root)
            self.assertEqual(
                self._validate_runtime(copy.deepcopy(runtime), root=root),
                runtime,
            )
            runtime["phase"] = "goal"
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_RUNTIME_SCHEMA_INVALID"
            ):
                self._validate_runtime(runtime, root=root)

    def test_runtime_rejects_unpinned_paths_and_incoherent_state(self) -> None:
        mutations = {
            "absolute goal path": ("goal_file", "/etc/passwd"),
            "wrong answer": ("answer_file", "docs/routeB_bus/059_other.answer.md"),
            "unknown holder": (
                "lease",
                {"holder": "ANYONE", "heartbeat_at": "2026-08-13T12:00:00Z"},
            ),
            "bad heartbeat": (
                "lease",
                {"holder": "CODEX_LINUX", "heartbeat_at": "not-a-time"},
            ),
            "cycle overflow": ("cycle_index", 13),
            "last attempt drift": ("last_attempt_id", "ATTEMPT_GOAL058_002"),
        }
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name, (field, value) in mutations.items():
                with self.subTest(name=name):
                    runtime = self._runtime_fixture(root)
                    runtime[field] = value
                    with self.assertRaisesRegex(
                        goal_runtime.GoalRuntimeError, "AUTOPILOT_RUNTIME_"
                    ):
                        self._validate_runtime(runtime, root=root)

            runtime = self._runtime_fixture(root)
            runtime["state"] = "CLOSED"
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_RUNTIME_SCHEMA_INVALID"
            ):
                self._validate_runtime(runtime, root=root)

    def test_runtime_rejects_goal_hash_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runtime = self._runtime_fixture(root)
            runtime["goal_sha256"] = "a" * 64
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_RUNTIME_GOAL_PIN_INVALID"
            ):
                self._validate_runtime(runtime, root=root)

    def test_runtime_rejects_phase_hash_and_answer_state_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runtime = self._runtime_fixture(root)
            runtime["mathematical_phase_key_sha256"] = "a" * 64
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_RUNTIME_PHASE_PIN_INVALID"
            ):
                self._validate_runtime(runtime, root=root)

            runtime = self._runtime_fixture(root)
            runtime["state"] = "CLOSED"
            runtime["next_action"] = "MINT_READY"
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_RUNTIME_ANSWER_STATE_INVALID"
            ):
                self._validate_runtime(runtime, root=root)

            answer = root / runtime["answer_file"]
            answer.write_text("closed\n", encoding="utf-8")
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_GOAL_HEADER_INVALID"
            ):
                self._validate_runtime(runtime, root=root)

            answer.write_text(
                "# answer\n\n```yaml\nGOAL: '058'\nSTATUS: CLOSED\n"
                "EXACT_RESULT: SYNTHETIC_CLOSED\n```\n",
                encoding="utf-8",
            )
            self.assertEqual(self._validate_runtime(runtime, root=root)["state"], "CLOSED")

    def test_runtime_goal_phase_cannot_replace_canonical_channel_phase(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runtime = self._runtime_fixture(root)
            self._write_canonical_phase(root, dict(PHASE, front_id="CANONICAL_FRONT"))
            runtime["mathematical_phase_key_sha256"] = goal_runtime.phase_key_sha256(PHASE)
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_RUNTIME_PHASE_PIN_INVALID"
            ):
                self._validate_runtime(runtime, root=root)

    def test_answer_result_must_be_a_nonempty_scalar_token(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            bus = Path(tmp)
            goal_runtime._write_goal(bus, "101", PHASE)
            answer = bus / "101_plant.answer.md"
            answer.write_text(
                "# forged answer\n\n```yaml\nGOAL: '101'\nSTATUS: CLOSED\n"
                "RESULT:\n  nested: object\n```\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_ANSWER_INVALID"
            ):
                goal_runtime.scan_physical_goals(bus, repo_root=bus)

    def test_answer_cannot_hide_paused_goal_status(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            bus = Path(tmp)
            goal_runtime._write_goal(bus, "101", PHASE)
            goal = bus / "101_plant.goal.md"
            goal.write_text(
                goal.read_text(encoding="utf-8").replace(
                    "STATUS: OPEN", "STATUS: PAUSED_RESTORABLE"
                ),
                encoding="utf-8",
            )
            (bus / "101_plant.answer.md").write_text(
                "# answer\n\n```yaml\nGOAL: '101'\nSTATUS: CLOSED\n"
                "EXACT_RESULT: FORGED\n```\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_ANSWER_INVALID"
            ):
                goal_runtime.scan_physical_goals(bus, repo_root=bus)

    def test_runtime_enforces_cycle_and_stall_budgets(self) -> None:
        mutations = [
            {"cycle_index": 12, "last_attempt_id": "ATTEMPT_GOAL058_012"},
            {
                "cycle_index": 6,
                "stall_counter": 6,
                "last_attempt_id": "ATTEMPT_GOAL058_006",
            },
            {"stall_counter": 3},
        ]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for mutation in mutations:
                with self.subTest(mutation=mutation):
                    runtime = self._runtime_fixture(root)
                    runtime.update(mutation)
                    with self.assertRaisesRegex(
                        goal_runtime.GoalRuntimeError, "AUTOPILOT_RUNTIME_BUDGET_INVALID"
                    ):
                        self._validate_runtime(runtime, root=root)

    def test_goal_identity_uses_lexical_header_and_filename(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            bus = Path(tmp)
            goal_runtime._write_goal(bus, "057", PHASE)
            executable, _ = goal_runtime.scan_physical_goals(bus, repo_root=bus)
            self.assertEqual(executable[0].goal_id, "057")
            goal = bus / "057_plant.goal.md"
            renamed = bus / "058_plant.goal.md"
            goal.rename(renamed)
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_GOAL_IDENTITY_MISMATCH"
            ):
                goal_runtime.scan_physical_goals(bus)

    def test_duplicate_cli_control_key_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "spec.yaml"
            path.write_text("px_rh_claim: true\npx_rh_claim: false\n", encoding="utf-8")
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_INPUT_INVALID"
            ):
                goal_runtime._load_mapping(path)

    def test_caller_cannot_replace_canonical_phase(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec = goal_runtime._valid_spec(PHASE)
            self._bind_spec_source(root, spec)
            canonical = dict(PHASE, front_id="CANONICAL_FRONT")
            self._write_canonical_phase(root, canonical)
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_CURRENT_PHASE_KEY_DRIFT"
            ):
                goal_runtime.select_action(
                    root / "docs" / "routeB_bus",
                    next_goal_spec=spec,
                    current_phase_key=PHASE,
                    repo_root=root,
                )

    def test_fictitious_grant_id_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runtime = self._runtime_fixture(root)
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_OPERATIONAL_GRANT_INVALID"
            ):
                goal_runtime.validate_runtime_state(
                    runtime, repo_root=root, grant_resolver=lambda _grant_id: None
                )

    def test_runtime_source_pin_requires_a_real_git_commit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runtime = self._runtime_fixture(root)
            runtime["source_commit"] = "b" * 40
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_RUNTIME_SOURCE_PIN_INVALID"
            ):
                self._validate_runtime(runtime, root=root)

    def test_duplicate_canonical_phase_key_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write_canonical_phase(root, PHASE)
            runtime_path = root / "orchestrator" / "state" / "CHANNEL_RUNTIME.json"
            text = runtime_path.read_text(encoding="utf-8")
            runtime_path.write_text(
                text.replace(
                    '"conversation_id":"plant-conversation"',
                    '"conversation_id":"first","conversation_id":"second"',
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_CANONICAL_PHASE_UNAVAILABLE"
            ):
                goal_runtime._canonical_phase_key(repo_root=root)

    def test_executable_goal_must_match_canonical_phase(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bus = root / "docs" / "routeB_bus"
            bus.mkdir(parents=True)
            goal_runtime._write_goal(bus, "058", PHASE)
            self._write_canonical_phase(root, dict(PHASE, front_id="DIFFERENT_FRONT"))
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_CURRENT_PHASE_KEY_DRIFT"
            ):
                goal_runtime.select_action(bus, repo_root=root)

    def test_executable_goal_requires_living_conversation_handle(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bus = root / "docs" / "routeB_bus"
            bus.mkdir(parents=True)
            goal_runtime._write_goal(bus, "058", PHASE)
            runtime_path = root / "orchestrator" / "state" / "CHANNEL_RUNTIME.json"
            runtime_path.parent.mkdir(parents=True)
            runtime_path.write_text(
                '{"active_proshka_phase":{"status":"ACTIVE","phase_key":'
                + json.dumps(PHASE)
                + "}}\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_CANONICAL_PHASE_UNAVAILABLE"
            ):
                goal_runtime.select_action(bus, repo_root=root)

    def test_runtime_rejects_paused_goal_and_overbroad_grant(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runtime = self._runtime_fixture(root)
            goal = root / runtime["goal_file"]
            goal.write_text(
                goal.read_text(encoding="utf-8").replace(
                    "STATUS: OPEN", "STATUS: PAUSED_RESTORABLE"
                ),
                encoding="utf-8",
            )
            runtime["goal_sha256"] = hashlib.sha256(goal.read_bytes()).hexdigest()
            subprocess.run(["git", "add", runtime["goal_file"]], cwd=root, check=True)
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=AUTOPILOT Plant",
                    "-c",
                    "user.email=autopilot-plant@example.invalid",
                    "commit",
                    "-q",
                    "-m",
                    "plant paused source pin",
                ],
                cwd=root,
                check=True,
            )
            runtime["source_commit"] = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_RUNTIME_GOAL_PIN_INVALID"
            ):
                self._validate_runtime(runtime, root=root)

            runtime = self._runtime_fixture(root)
            grant = self._grant(runtime)
            grant["allowed_actions"] = [runtime["next_action"], "STOP"]
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_OPERATIONAL_GRANT_INVALID"
            ):
                goal_runtime.validate_runtime_state(
                    runtime,
                    repo_root=root,
                    grant_resolver=lambda _grant_id: grant,
                )

    def test_failing_grant_authority_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runtime = self._runtime_fixture(root)

            def broken_resolver(_grant_id: str) -> dict[str, object]:
                raise RuntimeError("authority unavailable")

            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "AUTOPILOT_OPERATIONAL_GRANT_INVALID"
            ):
                goal_runtime.validate_runtime_state(
                    runtime,
                    repo_root=root,
                    grant_resolver=broken_resolver,
                )

    def test_live_repository_selects_058_and_not_paused_057(self) -> None:
        state = json.loads(three_body_loop.DEFAULT_STATE.read_text(encoding="utf-8"))
        receipts = {}
        for entry in state["entries"]:
            if entry["status"] != "SEMANTICALLY_ADMITTED":
                continue
            attestation_id = entry["semantic_attestation_id"]
            issuer = (
                three_body_loop.EXACT_OWNER_WAIVER_ISSUER
                if (entry["entry_id"], attestation_id)
                in three_body_loop.EXACT_OWNER_WAIVERS
                else three_body_loop.SEMANTIC_ATTESTATION_ISSUER
            )
            receipts[attestation_id] = {
                "schema": "q3_semantic_attestation.v1",
                "attestation_id": attestation_id,
                "issuer": issuer,
                "status": "ADMITTED",
                "control_version": 9,
                **{
                    field: entry[field]
                    for field in (
                        "task_path",
                        "task_blob",
                        "source_commit",
                        "source_git_blob",
                        "theorem_ids",
                        "admitted_scope",
                        "terminal_consumer",
                        "closes",
                        "opens",
                        "normalization",
                        "domain",
                        "quantifiers",
                        "hypothesis_provenance_sha256",
                    )
                },
            }
        decision = goal_runtime.select_action(
            goal_runtime.DEFAULT_BUS,
            semantic_attestation_resolver=receipts.get,
        )
        self.assertEqual(decision.action, "SELECT_EXACT_GOAL")
        self.assertEqual(decision.selected_goal_id, "058")


if __name__ == "__main__":
    unittest.main()
