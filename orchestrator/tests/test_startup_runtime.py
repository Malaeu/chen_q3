"""Control-v10 production startup plus diagnostic shadow selector tests."""

from __future__ import annotations

import dataclasses
import fcntl
import hashlib
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from orchestrator import startup_runtime


class StartupRuntimeTests(unittest.TestCase):
    @staticmethod
    def _control(root: Path, version: int = 10, status: str = "ACTIVE") -> None:
        path = root / "docs" / "CODEX_CONTROL.md"
        path.parent.mkdir(parents=True, exist_ok=True)
        v10_locks = (
            "HONESTY_STATE: CHALLENGER_NOT_RH\nOWNER_ONLY_BOUNDARY: PX_RH_CLAIM\n"
            if version == 10
            else ""
        )
        path.write_text(
            "# control\n\n```yaml\n"
            "CONTROL_ID: Q3_EXECUTOR_CONTROL\n"
            f"CONTROL_VERSION: {version}\n"
            f"STATUS: {status}\n"
            f"{v10_locks}"
            "```\n",
            encoding="utf-8",
        )
        channel = root / "orchestrator/state/CHANNEL_RUNTIME.json"
        channel.parent.mkdir(parents=True, exist_ok=True)
        channel.write_text(
            "{\n"
            '  "schema": "q3_channel_runtime.v1",\n'
            '  "control_status": "ACTIVE",\n'
            '  "active_proshka_phase": null,\n'
            '  "active_exploration": null,\n'
            '  "last_exploration_close": null,\n'
            '  "mathematical_authority_mode": '
            '"CODEX_PROSHKA_FULL_EXCEPT_PX_RH_CLAIM",\n'
            '  "px_rh_claim_state": "NOT_READY",\n'
            '  "operational_action_pending": null,\n'
            '  "meter": {\n'
            '    "phases_opened": 0,\n'
            '    "fresh_chats_opened": 0,\n'
            '    "delegated_strategic_review_calls": 0,\n'
            '    "exploration_review_calls": 0,\n'
            '    "px_rh_claim_requests": 0,\n'
            '    "ordinary_goal_close_calls": 0,\n'
            '    "mathematical_owner_deferral_violations": 0,\n'
            '    "fanout_violations": 0,\n'
            '    "forced_rollovers": 0\n'
            "  }\n"
            "}\n",
            encoding="utf-8",
        )
        manifest = root / "docs/cartographer/TOOLS.yaml"
        manifest.parent.mkdir(parents=True, exist_ok=True)
        manifest.write_text(
            "schema: q3_tool_manifest.v2\n"
            "meta: {}\n"
            "status_semantics:\n"
            "  values: [ENABLED, AVAILABLE, DEGRADED, DISCONNECTED, RETIRED, BROKEN, PLANNED]\n"
            "mode_semantics:\n"
            "  values: [READ_ONLY, WRITES_DERIVED, WRITES_CANONICAL, NETWORK_WRITE, EXTERNAL]\n"
            "tool_contract:\n"
            "  required_fields: [id, status, audience, mode, path_or_paths, invocation, "
            "trigger, writes, approval, authority, records_to, last_verified]\n"
            "startup_contract:\n"
            "  validation:\n"
            "    command: python3 orchestrator/workflow_runtime.py plan\n"
            "    writes: false\n"
            "memory_event_routes:\n"
            "  SESSION_START:\n"
            "    run: [workflow-runtime]\n"
            "data_surfaces: {}\n"
            "tool_families:\n"
            "  runtime:\n"
            "    tools:\n"
            "      - id: workflow-runtime\n"
            "        status: ENABLED\n"
            "        audience: [CODEX]\n"
            "        mode: READ_ONLY\n"
            "        path: orchestrator/workflow_runtime.py\n"
            "        invoke: python3 orchestrator/workflow_runtime.py plan\n"
            "        trigger: SESSION_START\n"
            "        writes: false\n"
            "        approval: NONE\n"
            "        authority: TEST_ONLY\n"
            "        records_to: stdout\n"
            "        last_verified: 2026-09-02\n"
            "dynamic_queries: {}\n"
            "tool_lifecycle: {}\n"
            "known_hazards: []\n",
            encoding="utf-8",
        )

    @staticmethod
    def _current(
        root: Path,
        status: str,
        *,
        task_file: str = "docs/Codex/TASK_active.md",
        source_commit: str | None = None,
    ) -> None:
        path = root / "docs" / "Codex" / "CURRENT.md"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            "# current\n\n```yaml\n"
            "schema: q3_codex_current_task.v1\n"
            f"status: {status}\n"
            f"task_file: {task_file}\n"
            f"source_commit: {source_commit or 'a' * 40}\n"
            "```\n",
            encoding="utf-8",
        )

    @staticmethod
    def _goal(
        root: Path,
        relative: str,
        *,
        goal_id: str,
        status: str,
        node: str,
        source: str | None = None,
        source_pin: str | None = "source-pin",
        theorem: str | None = "theorem-pin",
        consumer: str | None = "consumer-pin",
    ) -> Path:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        source_line = f"SOURCE_PIN: {source_pin}\n" if source_pin is not None else ""
        source_path_line = f"SOURCE: {source}\n" if source is not None else ""
        theorem_line = f"THEOREM: {theorem}\n" if theorem is not None else ""
        consumer_line = f"TERMINAL_CONSUMER: {consumer}\n" if consumer is not None else ""
        path.write_text(
            "# goal\n\n```yaml\n"
            f"GOAL: '{goal_id}'\n"
            f"NODE: {node}\n"
            f"STATUS: {status}\n"
            f"{source_path_line}"
            f"{source_line}"
            f"{theorem_line}"
            f"{consumer_line}"
            "```\n",
            encoding="utf-8",
        )
        return path

    @staticmethod
    def _execution_state(root: Path, selected_path: str, goal_id: str) -> None:
        path = (
            root
            / "q3.lean.aristotle"
            / "ACTIVE"
            / "requests"
            / "routeB_twolevel_spectral_ladder"
            / "ROUTE_B_EXECUTION_STATE.json"
        )
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            "{\n"
            '  "schema_version": "route_b_execution_state.v3_live_bus",\n'
            '  "architecture": {"route_b_rh_status": "NOT_RH"},\n'
            '  "current": {\n'
            f'    "selected_bus_goal_path": "{selected_path}",\n'
            f'    "selected_bus_goal_nnn": "{goal_id}",\n'
            '    "route_promotion": false,\n'
            '    "rh_claimed": false\n'
            "  }\n"
            "}\n",
            encoding="utf-8",
        )

    @staticmethod
    def _git_commit(root: Path) -> None:
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        (root / ".git" / "q3-three-body.writer.lock").write_text("idle\n", encoding="utf-8")
        subprocess.run(["git", "add", "."], cwd=root, check=True)
        subprocess.run(
            [
                "git",
                "-c",
                "user.name=Startup Plant",
                "-c",
                "user.email=startup@example.invalid",
                "commit",
                "-q",
                "-m",
                "startup plant",
            ],
            cwd=root,
            check=True,
        )
        branch = subprocess.run(
            ["git", "branch", "--show-current"],
            cwd=root,
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout.strip()
        subprocess.run(
            ["git", "update-ref", f"refs/remotes/origin/{branch}", "HEAD"],
            cwd=root,
            check=True,
        )

    def _committed_open_snapshot_fixture(
        self,
        root: Path,
        *,
        source_rel: str = "docs/routeB_bus/source.md",
        theorem: str | None = "theorem-pin",
        consumer: str | None = "consumer-pin",
    ) -> dict[str, Path]:
        self._control(root)
        self._current(root, "CLOSED")
        source = root / source_rel
        source.parent.mkdir(parents=True, exist_ok=True)
        source_bytes = b"source\n"
        source.write_bytes(source_bytes)
        source_blob = hashlib.sha1(
            b"blob " + str(len(source_bytes)).encode("ascii") + b"\0" + source_bytes
        ).hexdigest()
        goal = self._goal(
            root,
            "docs/routeB_bus/058_live.goal.md",
            goal_id="058",
            status="OPEN",
            node="live-node",
            source=source_rel,
            source_pin=source_blob,
            theorem=theorem,
            consumer=consumer,
        )
        self._execution_state(root, "docs/routeB_bus/058_live.goal.md", "058")
        self._git_commit(root)
        state = (
            root / "q3.lean.aristotle/ACTIVE/requests/"
            "routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json"
        )
        return {
            "control": root / "docs/CODEX_CONTROL.md",
            "channel": root / "orchestrator/state/CHANNEL_RUNTIME.json",
            "manifest": root / "docs/cartographer/TOOLS.yaml",
            "current": root / "docs/Codex/CURRENT.md",
            "goal": goal,
            "source": source,
            "state": state,
        }

    def test_top_level_physical_bus_selects_open_goal_without_numeric_authority(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "ACTIVE")
            task = root / "docs" / "Codex" / "TASK_active.md"
            task.write_text("```yaml\nNODE: current-node\n```\n", encoding="utf-8")
            self._goal(
                root,
                "docs/routeB_bus/001_live.goal.md",
                goal_id="001",
                status="OPEN",
                node="physical-node",
            )
            self._goal(
                root,
                "docs/routeB_bus/999_paused.goal.md",
                goal_id="999",
                status="PAUSED_RESTORABLE",
                node="paused-node",
            )

            result = startup_runtime.select_v10_shadow_goal(root)

            self.assertEqual(
                result.selected_goal,
                "docs/routeB_bus/001_live.goal.md",
            )
            self.assertEqual(result.exact_node_pin, "physical-node")
            self.assertEqual(result.exact_source_pin, "source-pin")
            self.assertEqual(result.exact_theorem_pin, "theorem-pin")
            self.assertEqual(result.exact_consumer_pin, "consumer-pin")
            self.assertFalse(result.fatal_errors)
            self.assertTrue(
                any(item.startswith("PAUSED_RESTORABLE_EXCLUDED:") for item in result.warnings)
            )

    def test_more_than_one_global_open_goal_is_fatal(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            self._goal(
                root,
                "docs/routeB_bus/900_first.goal.md",
                goal_id="900",
                status="OPEN",
                node="first",
            )
            self._goal(
                root,
                "docs/routeB_bus/001_second.goal.md",
                goal_id="001",
                status="OPEN",
                node="second",
            )

            result = startup_runtime.select_v10_shadow_goal(root)

            self.assertIsNone(result.selected_goal)
            self.assertEqual(result.next_action, "STOP_FAIL_CLOSED")
            self.assertTrue(
                any(
                    item.startswith("STARTUP_AMBIGUOUS_OPEN_GOALS:") for item in result.fatal_errors
                )
            )

    def test_active_current_is_fallback_only_when_bus_has_no_open_goal(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "ACTIVE")
            (root / "docs" / "routeB_bus").mkdir(parents=True)
            task = root / "docs" / "Codex" / "TASK_active.md"
            task.write_text(
                "```yaml\n"
                "NODE: current-node\n"
                "THEOREM: current-theorem\n"
                "TERMINAL_CONSUMER: current-consumer\n"
                "```\n",
                encoding="utf-8",
            )

            result = startup_runtime.select_v10_shadow_goal(root)

            self.assertEqual(result.selected_goal, "docs/Codex/TASK_active.md")
            self.assertEqual(result.exact_node_pin, "current-node")
            self.assertEqual(result.exact_source_pin, "a" * 40)
            self.assertEqual(result.exact_theorem_pin, "current-theorem")
            self.assertEqual(result.exact_consumer_pin, "current-consumer")

    def test_closed_current_is_ignored(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            (root / "docs" / "routeB_bus").mkdir(parents=True)

            result = startup_runtime.select_v10_shadow_goal(root)

            self.assertIsNone(result.selected_goal)
            self.assertEqual(result.next_action, "SHADOW_STOP_NO_GOAL")
            self.assertIn("CURRENT_CLOSED_IGNORED", result.warnings)

    def test_arbitrary_answer_cannot_hide_open_goal(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            goal = self._goal(
                root,
                "docs/routeB_bus/058_live.goal.md",
                goal_id="058",
                status="OPEN",
                node="live-node",
            )
            goal.with_name("058_live.answer.md").write_text(
                "not a machine answer\n", encoding="utf-8"
            )

            result = startup_runtime.select_v10_shadow_goal(root)

            self.assertIsNone(result.selected_goal)
            self.assertTrue(
                any(
                    item.startswith("STARTUP_ANSWER_CLOSURE_UNTRACKED:")
                    for item in result.fatal_errors
                )
            )

    def test_production_paired_open_goal_blocks_active_current_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            task_rel = "docs/Codex/TASK_active.md"
            self._current(root, "CLOSED", task_file=task_rel)
            task = root / task_rel
            task.parent.mkdir(parents=True, exist_ok=True)
            task.write_text(
                "```yaml\nNODE: fallback-node\nTHEOREM: fallback-theorem\n"
                "TERMINAL_CONSUMER: fallback-consumer\n```\n",
                encoding="utf-8",
            )
            goal = self._goal(
                root,
                "docs/routeB_bus/058_hidden.goal.md",
                goal_id="058",
                status="OPEN",
                node="hidden-open",
            )
            goal.with_name("058_hidden.answer.md").write_text(
                "arbitrary answer bytes\n", encoding="utf-8"
            )
            self._execution_state(root, "", "")
            self._git_commit(root)
            source_commit = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()
            self._current(
                root,
                "ACTIVE",
                task_file=task_rel,
                source_commit=source_commit,
            )
            subprocess.run(["git", "add", "docs/Codex/CURRENT.md"], cwd=root, check=True)
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=Startup Plant",
                    "-c",
                    "user.email=startup@example.invalid",
                    "commit",
                    "-q",
                    "-m",
                    "activate fallback",
                ],
                cwd=root,
                check=True,
            )

            snapshot = startup_runtime.build_startup_snapshot(root)

            self.assertIsNone(snapshot.selected_goal)
            self.assertFalse(snapshot.run_authorized)
            self.assertTrue(
                any(item.startswith("STARTUP_ANSWER_INVALID:") for item in snapshot.fatal_errors),
                snapshot.fatal_errors,
            )

    def test_production_historical_pair_allowlist_is_content_bound(self) -> None:
        project = Path(startup_runtime.__file__).resolve().parents[1]
        historical_rel = "docs/routeB_bus/056a_k8_xw8_prolate_ktrial_provenance.goal.md"
        historical_answer_rel = historical_rel.removesuffix(".goal.md") + ".answer.md"
        for mutated_rel in (historical_rel, historical_answer_rel):
            with self.subTest(mutated_rel=mutated_rel), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._control(root)
                self._current(root, "CLOSED")
                for relative in (historical_rel, historical_answer_rel):
                    target = root / relative
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes((project / relative).read_bytes())
                source_rel = "docs/routeB_bus/live_source.md"
                source = root / source_rel
                source.write_bytes(b"live source\n")
                source_blob = hashlib.sha1(
                    b"blob "
                    + str(source.stat().st_size).encode("ascii")
                    + b"\0"
                    + source.read_bytes()
                ).hexdigest()
                live_goal = self._goal(
                    root,
                    "docs/routeB_bus/058_live.goal.md",
                    goal_id="058",
                    status="OPEN",
                    node="live-node",
                    source=source_rel,
                    source_pin=source_blob,
                )
                self._execution_state(root, live_goal.relative_to(root).as_posix(), "058")
                self._git_commit(root)
                baseline_commit = subprocess.run(
                    ["git", "rev-parse", "HEAD"],
                    cwd=root,
                    check=True,
                    stdout=subprocess.PIPE,
                    text=True,
                ).stdout.strip()

                with (
                    mock.patch.object(
                        startup_runtime,
                        "HISTORICAL_PAIRED_BASELINE_COMMIT",
                        baseline_commit,
                    ),
                ):
                    baseline = startup_runtime.build_startup_snapshot(root)
                    self.assertTrue(baseline.run_authorized, baseline.fatal_errors)
                    subprocess.run(
                        ["git", "update-index", "--skip-worktree", "--", mutated_rel],
                        cwd=root,
                        check=True,
                    )
                    mutated = root / mutated_rel
                    mutated.write_bytes(mutated.read_bytes() + b"\nmutated historical bytes\n")

                    snapshot = startup_runtime.build_startup_snapshot(root)

                self.assertFalse(snapshot.git_dirty)
                self.assertFalse(snapshot.run_authorized)
                self.assertIsNone(snapshot.selected_goal)
                self.assertTrue(
                    any(
                        item.startswith("STARTUP_ANSWER_CLOSURE_BLOB_DRIFT:")
                        for item in snapshot.fatal_errors
                    ),
                    snapshot.fatal_errors,
                )

    def test_orphan_answer_is_outside_top_level_goal_selection(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            answer = root / "docs/routeB_bus/777_orphan.answer.md"
            answer.parent.mkdir(parents=True, exist_ok=True)
            answer.write_text("legacy answer-only prose\n", encoding="utf-8")
            self._execution_state(root, "", "")
            self._git_commit(root)

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertIsNone(snapshot.selected_goal)
            self.assertFalse(snapshot.fatal_errors, snapshot.fatal_errors)

    def test_misnamed_answer_does_not_hide_top_level_open_goal(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            source_rel = "docs/routeB_bus/source.md"
            source = root / source_rel
            source.parent.mkdir(parents=True, exist_ok=True)
            source_bytes = b"source\n"
            source.write_bytes(source_bytes)
            source_blob = hashlib.sha1(
                b"blob " + str(len(source_bytes)).encode("ascii") + b"\0" + source_bytes
            ).hexdigest()
            self._goal(
                root,
                "docs/routeB_bus/058_live.goal.md",
                goal_id="058",
                status="OPEN",
                node="live-node",
                source=source_rel,
                source_pin=source_blob,
            )
            answer = root / "docs/routeB_bus/058_wrong.answer.md"
            answer.write_text("legacy answer-only prose\n", encoding="utf-8")
            self._execution_state(root, "docs/routeB_bus/058_live.goal.md", "058")
            self._git_commit(root)

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertEqual(snapshot.selected_goal, "docs/routeB_bus/058_live.goal.md")
            self.assertFalse(snapshot.fatal_errors, snapshot.fatal_errors)

    def test_wrong_goal_in_committed_modern_answer_is_fatal(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            goal = self._goal(
                root,
                "docs/routeB_bus/058_closed.goal.md",
                goal_id="058",
                status="CLOSED",
                node="closed-node",
            )
            goal.with_name("058_closed.answer.md").write_text(
                "```yaml\nGOAL: '999'\nNODE: closed-node\nSTATUS: CLOSED\nRESULT: PASS\n```\n",
                encoding="utf-8",
            )
            self._execution_state(root, "", "")
            self._git_commit(root)

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertIsNone(snapshot.selected_goal)
            self.assertTrue(
                any(item.startswith("STARTUP_ANSWER_INVALID:") for item in snapshot.fatal_errors),
                snapshot.fatal_errors,
            )

    def test_committed_legacy_headerless_goal_answer_pair_is_head_bound(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            bus = root / "docs/routeB_bus"
            bus.mkdir(parents=True, exist_ok=True)
            goal = bus / "004_legacy.goal.md"
            answer = bus / "004_legacy.answer.md"
            goal.write_text("# Legacy goal without a machine header\n", encoding="utf-8")
            answer.write_text("# Legacy closing answer\n", encoding="utf-8")
            self._execution_state(root, "", "")
            self._git_commit(root)
            baseline = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()

            with (
                mock.patch.object(
                    startup_runtime,
                    "HISTORICAL_PAIRED_BASELINE_COMMIT",
                    baseline,
                ),
            ):
                committed = startup_runtime.build_shadow_snapshot(root)

                self.assertIsNone(committed.selected_goal)
                self.assertFalse(committed.fatal_errors, committed.fatal_errors)
                goal.write_text("# Dirty legacy goal bytes\n", encoding="utf-8")
                dirty = startup_runtime.build_shadow_snapshot(root)
            self.assertTrue(
                any(
                    item.startswith("STARTUP_HISTORICAL_PAIRED_BLOB_DRIFT:")
                    for item in dirty.fatal_errors
                ),
                dirty.fatal_errors,
            )

    def test_frozen_structured_legacy_pair_is_blob_bound(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            bus = root / "docs/routeB_bus"
            bus.mkdir(parents=True, exist_ok=True)
            goal = bus / "056_k8_muntz_v3_slot_s2_bridge.goal.md"
            answer = bus / "056_k8_muntz_v3_slot_s2_bridge.answer.md"
            goal.write_text(
                "```yaml\nGOAL: '056'\nSTATUS: PHASE0_INTERFACE_AUDIT\n```\n",
                encoding="utf-8",
            )
            answer.write_text(
                "```yaml\nGOAL: '056'\nSTATUS: CLOSED_PHASE0\nSUCCESS: PASS\n```\n",
                encoding="utf-8",
            )
            self._execution_state(root, "", "")
            self._git_commit(root)
            baseline = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()

            with (
                mock.patch.object(
                    startup_runtime,
                    "HISTORICAL_PAIRED_BASELINE_COMMIT",
                    baseline,
                ),
            ):
                committed = startup_runtime.build_shadow_snapshot(root)
                self.assertFalse(committed.fatal_errors, committed.fatal_errors)

                answer.write_text(
                    "```yaml\nGOAL: '056'\nSTATUS: CLOSED_PHASE0\nSUCCESS: CHANGED\n```\n",
                    encoding="utf-8",
                )
                dirty = startup_runtime.build_shadow_snapshot(root)

            self.assertTrue(
                any(
                    item.startswith("STARTUP_HISTORICAL_PAIRED_BLOB_DRIFT:")
                    for item in dirty.fatal_errors
                ),
                dirty.fatal_errors,
            )

    def test_committed_phase_alias_pair_is_strictly_validated(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            goal = self._goal(
                root,
                "docs/routeB_bus/056a_legacy_phase.goal.md",
                goal_id="056",
                status="OPEN",
                node="legacy-phase",
            )
            raw = goal.read_text(encoding="utf-8").replace(
                "STATUS: OPEN\n", "PHASE: 1\nSTATUS: OPEN\n"
            )
            goal.write_text(raw, encoding="utf-8")
            goal.with_name("056a_legacy_phase.answer.md").write_text(
                "```yaml\nGOAL: '056'\nPHASE: '1'\nNODE: legacy-phase\n"
                "STATUS: CLOSED\nRESULT: PASS\n```\n",
                encoding="utf-8",
            )
            self._execution_state(root, "", "")
            self._git_commit(root)

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertIsNone(snapshot.selected_goal)
            self.assertFalse(snapshot.fatal_errors, snapshot.fatal_errors)

    def test_committed_goal_filename_header_mismatch_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            goal = self._goal(
                root,
                "docs/routeB_bus/058a_new.goal.md",
                goal_id="058",
                status="OPEN",
                node="new-node",
            )
            goal.with_name("058a_new.answer.md").write_text(
                "legacy answer bytes\n", encoding="utf-8"
            )
            self._execution_state(root, "", "")
            self._git_commit(root)

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertTrue(
                any(
                    item.startswith("STARTUP_GOAL_IDENTITY_MISMATCH:")
                    for item in snapshot.fatal_errors
                ),
                snapshot.fatal_errors,
            )

    def test_nested_ignored_answer_is_outside_top_level_bus(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            (root / "docs/routeB_bus").mkdir(parents=True)
            (root / ".gitignore").write_text("docs/routeB_bus/ignored/\n", encoding="utf-8")
            self._execution_state(root, "", "")
            self._git_commit(root)
            answer = root / "docs/routeB_bus/ignored/777_orphan.answer.md"
            answer.parent.mkdir(parents=True)
            answer.write_text(
                "```yaml\nGOAL: '777'\nSTATUS: CLOSED\nRESULT: PASS\n```\n",
                encoding="utf-8",
            )

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertIsNone(snapshot.selected_goal)
            self.assertFalse(snapshot.fatal_errors, snapshot.fatal_errors)

    def test_direct_bus_entry_limit_accepts_4096_and_rejects_4097(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bus = root / "docs/routeB_bus"
            bus.mkdir(parents=True)
            for index in range(startup_runtime.BUS_DIRECT_ENTRY_LIMIT):
                (bus / f"junk-{index:04d}").touch()

            goals, answers, manifest, _fingerprints = startup_runtime._physical_bus_paths(root)

            self.assertEqual(goals, ())
            self.assertEqual(answers, ())
            self.assertRegex(manifest, r"^[0-9a-f]{64}$")
            (bus / "one-too-many").touch()
            with self.assertRaisesRegex(
                startup_runtime.StartupRuntimeError,
                "STARTUP_BUS_SCAN_LIMIT_EXCEEDED",
            ):
                startup_runtime._physical_bus_paths(root)

    def test_bus_observation_failure_does_not_synthesize_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._committed_open_snapshot_fixture(root)

            with mock.patch.object(
                startup_runtime,
                "_physical_bus_paths",
                side_effect=startup_runtime.StartupRuntimeError(
                    "STARTUP_BUS_SCAN_UNAVAILABLE", "plant"
                ),
            ):
                snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertIn("STARTUP_BUS_SCAN_UNAVAILABLE: plant", snapshot.fatal_errors)
            self.assertFalse(
                any(
                    code in item
                    for item in snapshot.fatal_errors
                    for code in (
                        "STARTUP_SELECTOR_STATE_DRIFT",
                        "STARTUP_CONTROL_BLOB_DRIFT",
                        "STARTUP_STATE_BLOB_DRIFT",
                    )
                ),
                snapshot.fatal_errors,
            )

    def test_symlink_goal_component_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            outside = root / "outside"
            outside.mkdir()
            self._goal(
                root,
                "outside/058_live.goal.md",
                goal_id="058",
                status="OPEN",
                node="live-node",
            )
            bus = root / "docs" / "routeB_bus"
            bus.parent.mkdir(parents=True, exist_ok=True)
            bus.symlink_to(outside, target_is_directory=True)

            result = startup_runtime.select_v10_shadow_goal(root)

            self.assertEqual(result.fatal_errors, ("STARTUP_BUS_MISSING",))

    def test_production_v10_rejects_v9_and_requires_honesty_locks(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root, version=9)
            self._current(root, "CLOSED")
            (root / "docs" / "routeB_bus").mkdir(parents=True)
            self._git_commit(root)

            with self.assertRaisesRegex(
                startup_runtime.StartupRuntimeError,
                "BATTLE_V10_CONTROL_INVALID",
            ):
                startup_runtime.validate_battle_v10_control(root)

            self._control(root, version=10)
            control_path = root / "docs/CODEX_CONTROL.md"
            control_path.write_text(
                "```yaml\nexample: unrelated\n```\n\n" + control_path.read_text(encoding="utf-8"),
                encoding="utf-8",
            )
            identity = startup_runtime.validate_battle_v10_control(root)
            self.assertEqual(identity.version, 10)
            self.assertEqual(identity.status, "ACTIVE")

            control_path.write_text(
                control_path.read_text(encoding="utf-8").replace(
                    "HONESTY_STATE: CHALLENGER_NOT_RH\n", ""
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                startup_runtime.StartupRuntimeError,
                "BATTLE_V10_CONTROL_INVALID",
            ):
                startup_runtime.validate_battle_v10_control(root)

    def test_active_current_binds_task_blob_without_exceeding_git_budget(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            (root / "docs" / "routeB_bus").mkdir(parents=True)
            self._execution_state(root, "", "")
            task_rel = "docs/Codex/TASK_active.md"
            task = root / task_rel
            task.parent.mkdir(parents=True, exist_ok=True)
            task.write_text(
                "```yaml\nNODE: current-node\nTHEOREM: current-theorem\n"
                "TERMINAL_CONSUMER: current-consumer\n```\n",
                encoding="utf-8",
            )
            self._git_commit(root)
            source_commit = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()
            self._current(
                root,
                "ACTIVE",
                task_file=task_rel,
                source_commit=source_commit,
            )
            subprocess.run(["git", "add", "docs/Codex/CURRENT.md"], cwd=root, check=True)
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=Startup Plant",
                    "-c",
                    "user.email=startup@example.invalid",
                    "commit",
                    "-q",
                    "-m",
                    "current pointer",
                ],
                cwd=root,
                check=True,
            )
            calls: list[tuple[str, ...]] = []
            real_run = startup_runtime.subprocess.run

            def count_git(args: list[str], *pos: object, **kwargs: object) -> object:
                if args and args[0] == "git":
                    calls.append(tuple(args))
                return real_run(args, *pos, **kwargs)  # type: ignore[arg-type]

            with mock.patch.object(startup_runtime.subprocess, "run", side_effect=count_git):
                snapshot = startup_runtime.build_startup_snapshot(root)

            self.assertEqual(snapshot.selected_goal, task_rel)
            self.assertNotIn("STARTUP_CURRENT_SOURCE_COMMIT_DRIFT", snapshot.fatal_errors)
            self.assertLessEqual(len(calls), 5)

            task.write_text(
                "```yaml\nNODE: changed-node\nTHEOREM: current-theorem\n"
                "TERMINAL_CONSUMER: current-consumer\n```\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", task_rel], cwd=root, check=True)
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=Startup Plant",
                    "-c",
                    "user.email=startup@example.invalid",
                    "commit",
                    "-q",
                    "-m",
                    "task changed",
                ],
                cwd=root,
                check=True,
            )
            drifted = startup_runtime.build_shadow_snapshot(root)
            self.assertIn("STARTUP_CURRENT_SOURCE_COMMIT_DRIFT", drifted.fatal_errors)

    def test_active_current_hidden_task_worktree_bytes_fail_closed(self) -> None:
        for index_flag in ("--assume-unchanged", "--skip-worktree"):
            with self.subTest(index_flag=index_flag), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._control(root)
                (root / "docs/routeB_bus").mkdir(parents=True)
                self._execution_state(root, "", "")
                task_rel = "docs/Codex/TASK_active.md"
                task = root / task_rel
                task.parent.mkdir(parents=True, exist_ok=True)
                task.write_text(
                    "```yaml\nNODE: clean-node\nTHEOREM: clean-theorem\n"
                    "TERMINAL_CONSUMER: clean-consumer\n```\n",
                    encoding="utf-8",
                )
                self._git_commit(root)
                source_commit = subprocess.run(
                    ["git", "rev-parse", "HEAD"],
                    cwd=root,
                    check=True,
                    stdout=subprocess.PIPE,
                    text=True,
                ).stdout.strip()
                self._current(
                    root,
                    "ACTIVE",
                    task_file=task_rel,
                    source_commit=source_commit,
                )
                subprocess.run(["git", "add", "docs/Codex/CURRENT.md"], cwd=root, check=True)
                subprocess.run(
                    [
                        "git",
                        "-c",
                        "user.name=Startup Plant",
                        "-c",
                        "user.email=startup@example.invalid",
                        "commit",
                        "-q",
                        "-m",
                        "activate current",
                    ],
                    cwd=root,
                    check=True,
                )
                subprocess.run(
                    ["git", "update-index", index_flag, "--", task_rel],
                    cwd=root,
                    check=True,
                )
                task.write_text(
                    "```yaml\nNODE: forged-node\nTHEOREM: forged-theorem\n"
                    "TERMINAL_CONSUMER: forged-consumer\n```\n",
                    encoding="utf-8",
                )

                snapshot = startup_runtime.build_shadow_snapshot(root)

                self.assertFalse(snapshot.git_dirty)
                self.assertIsNone(snapshot.selected_goal)
                self.assertIsNone(snapshot.exact_node_pin)
                self.assertIn("STARTUP_CURRENT_TASK_WORKTREE_DRIFT", snapshot.fatal_errors)
                self.assertEqual(snapshot.next_action, "STOP_FAIL_CLOSED")

    def test_active_current_task_bytes_are_rechecked_at_snapshot_end(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            (root / "docs/routeB_bus").mkdir(parents=True)
            self._execution_state(root, "", "")
            task_rel = "docs/Codex/TASK_active.md"
            task = root / task_rel
            task.parent.mkdir(parents=True, exist_ok=True)
            task.write_text(
                "```yaml\nNODE: clean-node\nTHEOREM: clean-theorem\n"
                "TERMINAL_CONSUMER: clean-consumer\n```\n",
                encoding="utf-8",
            )
            self._git_commit(root)
            source_commit = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()
            self._current(
                root,
                "ACTIVE",
                task_file=task_rel,
                source_commit=source_commit,
            )
            subprocess.run(["git", "add", "docs/Codex/CURRENT.md"], cwd=root, check=True)
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=Startup Plant",
                    "-c",
                    "user.email=startup@example.invalid",
                    "commit",
                    "-q",
                    "-m",
                    "activate current",
                ],
                cwd=root,
                check=True,
            )
            original = startup_runtime._recheck_fingerprints

            def mutate_task_before_final_recheck(
                repo: Path,
                fingerprints: tuple[tuple[object, startup_runtime._PathFingerprint], ...],
            ) -> tuple[str, ...]:
                task.write_bytes(task.read_bytes() + b"\n")
                return original(repo, fingerprints)  # type: ignore[arg-type]

            with mock.patch.object(
                startup_runtime,
                "_recheck_fingerprints",
                side_effect=mutate_task_before_final_recheck,
            ):
                snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertIn("STARTUP_CURRENT_TASK_WORKTREE_DRIFT", snapshot.fatal_errors)
            self.assertEqual(snapshot.next_action, "STOP_FAIL_CLOSED")

    def test_v10_snapshot_parses_control_once(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root, version=10)
            self._current(root, "CLOSED")
            (root / "docs/routeB_bus").mkdir(parents=True)
            self._execution_state(root, "", "")
            self._git_commit(root)

            with mock.patch.object(
                startup_runtime,
                "_control_identity",
                wraps=startup_runtime._control_identity,
            ) as identity:
                snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertEqual(snapshot.control_version, 10)
            self.assertEqual(identity.call_count, 1)

    def test_snapshot_is_immutable_complete_and_asdict_compatible(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            source_rel = "docs/routeB_bus/source.md"
            source = root / source_rel
            source.parent.mkdir(parents=True, exist_ok=True)
            source_bytes = b"source\n"
            source.write_bytes(source_bytes)
            source_blob = hashlib.sha1(
                b"blob " + str(len(source_bytes)).encode("ascii") + b"\0" + source_bytes
            ).hexdigest()
            self._goal(
                root,
                "docs/routeB_bus/058_live.goal.md",
                goal_id="058",
                status="OPEN",
                node="live-node",
                source=source_rel,
                source_pin=source_blob,
            )
            self._execution_state(root, "docs/routeB_bus/058_live.goal.md", "058")
            self._git_commit(root)

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertTrue(dataclasses.is_dataclass(snapshot))
            self.assertEqual(snapshot.to_dict(), dataclasses.asdict(snapshot))
            self.assertEqual(snapshot.git_head, snapshot.git_origin_head)
            self.assertEqual(len(snapshot.git_tree or ""), 40)
            self.assertFalse(snapshot.git_dirty)
            self.assertEqual(snapshot.honesty_state, "CHALLENGER_NOT_RH")
            self.assertEqual(snapshot.selected_goal, "docs/routeB_bus/058_live.goal.md")
            self.assertEqual(snapshot.next_action, "SHADOW_INSPECT_SELECTED_GOAL")
            self.assertEqual(snapshot.blocked_features, ("RUN", "DISPATCH", "MINT", "STATE_WRITE"))
            with self.assertRaises(dataclasses.FrozenInstanceError):
                snapshot.next_action = "RUN"  # type: ignore[misc]

            rendered = json.dumps(snapshot.to_dict(), indent=2)
            self.assertLessEqual(len(rendered.encode("utf-8")), 4096)
            self.assertLessEqual(len(rendered.splitlines()), 60)

    def test_skip_worktree_control_bytes_fail_head_binding(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = self._committed_open_snapshot_fixture(root)
            subprocess.run(
                ["git", "update-index", "--skip-worktree", "docs/CODEX_CONTROL.md"],
                cwd=root,
                check=True,
            )
            paths["control"].write_text(
                paths["control"].read_text(encoding="utf-8") + "\n# hidden\n",
                encoding="utf-8",
            )

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertFalse(snapshot.git_dirty)
            self.assertIn("STARTUP_CONTROL_BLOB_DRIFT", snapshot.fatal_errors)

    def test_declared_surfaces_are_head_bound_despite_index_hiding(self) -> None:
        cases = (
            ("channel", "orchestrator/state/CHANNEL_RUNTIME.json"),
            ("manifest", "docs/cartographer/TOOLS.yaml"),
        )
        for index_flag in ("--skip-worktree", "--assume-unchanged"):
            for key, relative in cases:
                with (
                    self.subTest(index_flag=index_flag, surface=key),
                    tempfile.TemporaryDirectory() as tmp,
                ):
                    root = Path(tmp)
                    paths = self._committed_open_snapshot_fixture(root)
                    subprocess.run(
                        ["git", "update-index", index_flag, "--", relative],
                        cwd=root,
                        check=True,
                    )
                    paths[key].write_bytes(paths[key].read_bytes() + b"\nMUTATED\n")

                    snapshot = startup_runtime.build_startup_snapshot(root)

                    self.assertFalse(snapshot.git_dirty)
                    self.assertFalse(snapshot.run_authorized)
                    self.assertIn(
                        f"STARTUP_DECLARED_SURFACE_BLOB_DRIFT:{relative}",
                        snapshot.fatal_errors,
                    )

    def test_declared_surface_schema_and_duplicate_keys_fail_closed(self) -> None:
        cases = (
            (
                "channel",
                b'{"schema":"wrong","control_status":"ACTIVE"}\n',
                "STARTUP_CHANNEL_RUNTIME_INVALID",
            ),
            (
                "channel",
                b'{"schema":"q3_channel_runtime.v1","schema":"duplicate"}\n',
                "STARTUP_CHANNEL_RUNTIME_INVALID",
            ),
            (
                "channel",
                b'{"schema":"q3_channel_runtime.v1","control_status":"ACTIVE",'
                b'"mathematical_authority_mode":"OWNER_MAY_BE_DEFERRED_ANYTHING",'
                b'"px_rh_claim_state":"MADE"}\n',
                "STARTUP_CHANNEL_RUNTIME_INVALID",
            ),
            (
                "manifest",
                b"schema: wrong\nmeta: {}\n",
                "STARTUP_TOOL_MANIFEST_INVALID",
            ),
            (
                "manifest",
                b"schema: q3_tool_manifest.v2\nschema: duplicate\n",
                "STARTUP_TOOL_MANIFEST_INVALID",
            ),
            (
                "manifest",
                b"schema: q3_tool_manifest.v2\nmeta: {}\ntool_contract: {}\n"
                b"startup_contract: {}\nmemory_event_routes: {}\ndata_surfaces: {}\n"
                b"tool_families: {}\nknown_hazards: []\n",
                "STARTUP_TOOL_MANIFEST_INVALID",
            ),
        )
        for key, payload, code in cases:
            with self.subTest(surface=key, payload=payload), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                paths = self._committed_open_snapshot_fixture(root)
                paths[key].write_bytes(payload)

                snapshot = startup_runtime.build_startup_snapshot(root)

                self.assertFalse(snapshot.run_authorized)
                self.assertTrue(
                    any(item.startswith(code) for item in snapshot.fatal_errors),
                    snapshot.fatal_errors,
                )

    def test_tool_manifest_cannot_redefine_canonical_status_semantics(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = self._committed_open_snapshot_fixture(root)
            manifest = paths["manifest"].read_text(encoding="utf-8")
            manifest = manifest.replace(
                "[ENABLED, AVAILABLE, DEGRADED, DISCONNECTED, RETIRED, BROKEN, PLANNED]",
                "[EVIL]",
            ).replace("status: ENABLED", "status: EVIL")
            paths["manifest"].write_text(manifest, encoding="utf-8")

            snapshot = startup_runtime.build_startup_snapshot(root)

            self.assertFalse(snapshot.run_authorized)
            self.assertTrue(
                any(
                    item.startswith("STARTUP_TOOL_MANIFEST_INVALID")
                    for item in snapshot.fatal_errors
                ),
                snapshot.fatal_errors,
            )

    def test_channel_runtime_meter_and_phase_semantics_fail_closed(self) -> None:
        cases = (
            ("fanout_violations", 1),
            ("ordinary_goal_close_calls", 1),
            ("phases_opened", -1),
        )
        for field, value in cases:
            with self.subTest(field=field), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                paths = self._committed_open_snapshot_fixture(root)
                channel = json.loads(paths["channel"].read_text(encoding="utf-8"))
                channel["meter"][field] = value
                paths["channel"].write_text(json.dumps(channel), encoding="utf-8")

                snapshot = startup_runtime.build_startup_snapshot(root)

                self.assertFalse(snapshot.run_authorized)
                self.assertTrue(
                    any(
                        item.startswith("STARTUP_CHANNEL_RUNTIME_INVALID")
                        for item in snapshot.fatal_errors
                    ),
                    snapshot.fatal_errors,
                )

    def test_skip_worktree_open_goal_changed_to_paused_fails_head_binding(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = self._committed_open_snapshot_fixture(root)
            goal_rel = paths["goal"].relative_to(root).as_posix()
            subprocess.run(
                ["git", "update-index", "--skip-worktree", goal_rel],
                cwd=root,
                check=True,
            )
            paths["goal"].write_text(
                paths["goal"]
                .read_text(encoding="utf-8")
                .replace("STATUS: OPEN", "STATUS: PAUSED_RESTORABLE"),
                encoding="utf-8",
            )

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertFalse(snapshot.git_dirty)
            self.assertIsNone(snapshot.selected_goal)
            self.assertIn("STARTUP_GOAL_BLOB_DRIFT", snapshot.fatal_errors)

    def test_skip_worktree_execution_state_bytes_fail_head_binding(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = self._committed_open_snapshot_fixture(root)
            state_rel = paths["state"].relative_to(root).as_posix()
            subprocess.run(
                ["git", "update-index", "--skip-worktree", state_rel],
                cwd=root,
                check=True,
            )
            paths["state"].write_text(
                paths["state"].read_text(encoding="utf-8") + "\n",
                encoding="utf-8",
            )

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertFalse(snapshot.git_dirty)
            self.assertIn("STARTUP_STATE_BLOB_DRIFT", snapshot.fatal_errors)

    def test_skip_worktree_selected_source_bytes_fail_head_binding(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = self._committed_open_snapshot_fixture(root)
            source_rel = paths["source"].relative_to(root).as_posix()
            subprocess.run(
                ["git", "update-index", "--skip-worktree", source_rel],
                cwd=root,
                check=True,
            )
            paths["source"].write_bytes(paths["source"].read_bytes() + b"hidden\n")

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertFalse(snapshot.git_dirty)
            self.assertIn("STARTUP_SOURCE_WORKTREE_DRIFT", snapshot.fatal_errors)
            self.assertNotIn("STARTUP_SELECTOR_STATE_DRIFT", snapshot.fatal_errors)
            self.assertIsNone(snapshot.selected_goal)

    def test_exact_owned_dirty_lean_source_is_scoped_until_commit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source_rel = "q3.lean.aristotle/Q3/Proofs/RouteB/Candidate.lean"
            paths = self._committed_open_snapshot_fixture(root, source_rel=source_rel)
            paths["source"].write_bytes(paths["source"].read_bytes() + b"-- candidate\n")

            snapshot = startup_runtime.build_shadow_snapshot(root, owned_paths=(source_rel,))

            self.assertFalse(snapshot.fatal_errors, snapshot.fatal_errors)
            self.assertIn(
                "BLOCKED_FEATURE:OWNED_DIRTY_CANDIDATE_UNCOMMITTED",
                snapshot.blocked_features,
            )
            self.assertFalse(snapshot.run_authorized)
            self.assertEqual(snapshot.next_action, "SHADOW_BLOCKED_EXACT_EDGE_SELECTION")

    def test_owned_directory_scopes_nested_dirty_lean_source_until_commit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            owned_dir = "q3.lean.aristotle/Q3/Proofs/RouteB"
            source_rel = f"{owned_dir}/nested/Candidate.lean"
            paths = self._committed_open_snapshot_fixture(root, source_rel=source_rel)
            paths["source"].write_bytes(paths["source"].read_bytes() + b"-- nested candidate\n")

            snapshot = startup_runtime.build_shadow_snapshot(root, owned_paths=(owned_dir,))

            self.assertFalse(snapshot.fatal_errors, snapshot.fatal_errors)
            self.assertIn(
                "BLOCKED_FEATURE:OWNED_DIRTY_CANDIDATE_UNCOMMITTED",
                snapshot.blocked_features,
            )
            self.assertFalse(snapshot.run_authorized)

    def test_collapsed_untracked_parent_covers_nested_exact_source(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source_rel = "q3.lean.aristotle/Q3/Proofs/RouteB/new/Candidate.lean"
            goal_rel = "docs/routeB_bus/058_collapsed.goal.md"
            self._control(root)
            self._current(root, "CLOSED")
            source_pin = "a" * 40
            self._goal(
                root,
                goal_rel,
                goal_id="058",
                status="OPEN",
                node="collapsed-node",
                source=source_rel,
                source_pin=source_pin,
            )
            self._execution_state(root, goal_rel, "058")
            self._git_commit(root)
            head = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()
            goal = root / goal_rel
            goal.write_text(
                goal.read_text(encoding="utf-8").replace(source_pin, head),
                encoding="utf-8",
            )
            subprocess.run(["git", "add", goal_rel], cwd=root, check=True)
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=Startup Plant",
                    "-c",
                    "user.email=startup@example.invalid",
                    "commit",
                    "-q",
                    "-m",
                    "bind collapsed source",
                ],
                cwd=root,
                check=True,
            )
            branch = subprocess.run(
                ["git", "branch", "--show-current"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()
            subprocess.run(
                ["git", "update-ref", f"refs/remotes/origin/{branch}", "HEAD"],
                cwd=root,
                check=True,
            )
            source = root / source_rel
            source.parent.mkdir(parents=True)
            source.write_text("theorem candidate : True := by trivial\n", encoding="utf-8")
            status = subprocess.run(
                [
                    "git",
                    "status",
                    "--porcelain=v2",
                    "-z",
                    "--untracked-files=normal",
                ],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
            ).stdout

            self.assertIn(b"? q3.lean.aristotle/Q3/\0", status)
            unowned = startup_runtime.build_startup_snapshot(root)
            owned = startup_runtime.build_startup_snapshot(root, owned_paths=(source_rel,))

            self.assertIn("STARTUP_SOURCE_WORKTREE_DRIFT", unowned.fatal_errors)
            self.assertIsNone(unowned.selected_goal)
            self.assertFalse(unowned.run_authorized)
            self.assertFalse(owned.fatal_errors, owned.fatal_errors)
            self.assertEqual(owned.selected_goal, goal_rel)
            self.assertIn(
                "BLOCKED_FEATURE:OWNED_DIRTY_CANDIDATE_UNCOMMITTED",
                owned.blocked_features,
            )
            self.assertFalse(owned.run_authorized)

    def test_explicit_owned_new_untracked_lean_source_is_scoped_until_commit(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source_rel = "q3.lean.aristotle/Q3/Proofs/RouteB/NewCandidate.lean"
            goal_rel = "docs/routeB_bus/058_untracked.goal.md"
            self._control(root)
            self._current(root, "CLOSED")
            (root / "docs/routeB_bus").mkdir(parents=True)
            self._execution_state(root, "", "")
            self._git_commit(root)
            source_pin = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()
            self._goal(
                root,
                goal_rel,
                goal_id="058",
                status="OPEN",
                node="untracked-node",
                source=source_rel,
                source_pin=source_pin,
            )
            self._execution_state(root, goal_rel, "058")
            state_rel = (
                "q3.lean.aristotle/ACTIVE/requests/"
                "routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json"
            )
            subprocess.run(["git", "add", goal_rel, state_rel], cwd=root, check=True)
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=Startup Plant",
                    "-c",
                    "user.email=startup@example.invalid",
                    "commit",
                    "-q",
                    "-m",
                    "bind untracked candidate",
                ],
                cwd=root,
                check=True,
            )
            branch = subprocess.run(
                ["git", "branch", "--show-current"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()
            subprocess.run(
                ["git", "update-ref", f"refs/remotes/origin/{branch}", "HEAD"],
                cwd=root,
                check=True,
            )
            source = root / source_rel
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("theorem candidate : True := by trivial\n", encoding="utf-8")

            unowned = startup_runtime.build_shadow_snapshot(root)
            owned = startup_runtime.build_shadow_snapshot(root, owned_paths=(source_rel,))

            self.assertIn("STARTUP_SOURCE_WORKTREE_DRIFT", unowned.fatal_errors)
            self.assertFalse(owned.fatal_errors, owned.fatal_errors)
            self.assertTrue(owned.git_dirty)
            self.assertEqual(owned.selected_goal, goal_rel)
            self.assertIn(
                "BLOCKED_FEATURE:OWNED_DIRTY_CANDIDATE_UNCOMMITTED",
                owned.blocked_features,
            )
            self.assertFalse(owned.run_authorized)
            self.assertEqual(owned.next_action, "SHADOW_BLOCKED_EXACT_EDGE_SELECTION")

    def test_dirty_closed_current_is_ignored_with_physical_open_goal(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = self._committed_open_snapshot_fixture(root)
            paths["current"].write_text(
                paths["current"].read_text(encoding="utf-8") + "\n",
                encoding="utf-8",
            )

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertEqual(snapshot.selected_goal, "docs/routeB_bus/058_live.goal.md")
            self.assertFalse(
                any(
                    item.startswith(("STARTUP_RELEVANT_DIRTY_PATHS:", "STARTUP_CURRENT_"))
                    for item in snapshot.fatal_errors
                ),
                snapshot.fatal_errors,
            )

    def test_relevant_dirty_state_and_busy_writer_lock_are_fatal(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            self._goal(
                root,
                "docs/routeB_bus/058_live.goal.md",
                goal_id="058",
                status="OPEN",
                node="live-node",
                source_pin=None,
            )
            state_rel = (
                "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/"
                "ROUTE_B_EXECUTION_STATE.json"
            )
            self._execution_state(root, "docs/routeB_bus/058_live.goal.md", "058")
            self._git_commit(root)
            state = root / state_rel
            state.write_text(state.read_text(encoding="utf-8") + "\n", encoding="utf-8")

            dirty_snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertTrue(
                any(
                    item.startswith("STARTUP_RELEVANT_DIRTY_PATHS:")
                    for item in dirty_snapshot.fatal_errors
                )
            )

            lock_path = root / ".git" / "q3-three-body.writer.lock"
            lock_path.write_text("held\n", encoding="utf-8")
            with lock_path.open("rb") as handle:
                fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                locked_snapshot = startup_runtime.build_shadow_snapshot(root)
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
            self.assertIn("FATAL:WRITER_LOCK_COLLISION", locked_snapshot.fatal_errors)

    def test_nested_symlink_and_fake_goal_are_never_entered(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            (root / "docs/routeB_bus").mkdir(parents=True)
            self._execution_state(root, "", "")
            self._git_commit(root)
            outside = root / "outside"
            self._goal(
                root,
                "outside/999_hidden.goal.md",
                goal_id="999",
                status="OPEN",
                node="hidden",
            )
            nested_parent = root / "docs/routeB_bus/normal"
            nested_parent.mkdir()
            (nested_parent / "nested").symlink_to(outside, target_is_directory=True)
            ignored = root / "docs/routeB_bus/.lake-like"
            for index in range(300):
                nested = ignored / f"tree-{index:03d}"
                nested.mkdir(parents=True)
                (nested / "999_nested.goal.md").write_text("must remain opaque\n", encoding="utf-8")

            original_scandir = startup_runtime.os.scandir

            def direct_bus_only(path: object) -> object:
                if Path(path) != root / "docs/routeB_bus":
                    raise AssertionError(f"nested bus traversal: {path}")
                return original_scandir(path)

            with mock.patch.object(startup_runtime.os, "scandir", side_effect=direct_bus_only):
                result = startup_runtime.select_v10_shadow_goal(root)

            self.assertIsNone(result.selected_goal)
            self.assertFalse(result.fatal_errors, result.fatal_errors)

    def test_unrelated_untracked_file_is_outside_bounded_startup_scope(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            (root / "docs/routeB_bus").mkdir(parents=True)
            self._execution_state(root, "", "")
            self._git_commit(root)
            unrelated = root / "scratch/unrelated.txt"
            unrelated.parent.mkdir()
            unrelated.write_text("untracked\n", encoding="utf-8")

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertFalse(snapshot.git_dirty)
            self.assertNotIn("GIT_WORKTREE_DIRTY", snapshot.warnings)
            self.assertNotIn("GIT_FOREIGN_DIRTY_PATHS_PRESENT", snapshot.warnings)
            self.assertFalse(snapshot.fatal_errors, snapshot.fatal_errors)

    def test_nested_ignored_open_goal_does_not_block_active_current(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "ACTIVE")
            self._execution_state(root, "", "")
            task = root / "docs/Codex/TASK_active.md"
            task.parent.mkdir(parents=True, exist_ok=True)
            task.write_text(
                "```yaml\nNODE: current-node\nTHEOREM: current-theorem\n"
                "TERMINAL_CONSUMER: current-consumer\n```\n",
                encoding="utf-8",
            )
            (root / ".gitignore").write_text("docs/routeB_bus/ignored/\n", encoding="utf-8")
            (root / "docs/routeB_bus").mkdir(parents=True)
            self._git_commit(root)
            source_commit = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()
            self._current(root, "ACTIVE", source_commit=source_commit)
            subprocess.run(["git", "add", "docs/Codex/CURRENT.md"], cwd=root, check=True)
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=Startup Plant",
                    "-c",
                    "user.email=startup@example.invalid",
                    "commit",
                    "-q",
                    "-m",
                    "activate current",
                ],
                cwd=root,
                check=True,
            )
            self._goal(
                root,
                "docs/routeB_bus/ignored/999_hidden.goal.md",
                goal_id="999",
                status="OPEN",
                node="hidden-node",
            )

            result = startup_runtime.select_v10_shadow_goal(root)

            self.assertEqual(result.selected_goal, "docs/Codex/TASK_active.md")
            self.assertFalse(result.fatal_errors, result.fatal_errors)

    def test_nested_ignored_open_goal_is_not_part_of_global_set(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            self._execution_state(root, "", "")
            self._goal(
                root,
                "docs/routeB_bus/058_visible.goal.md",
                goal_id="058",
                status="OPEN",
                node="visible-node",
                source_pin=None,
            )
            (root / ".gitignore").write_text("docs/routeB_bus/ignored/\n", encoding="utf-8")
            self._git_commit(root)
            self._goal(
                root,
                "docs/routeB_bus/ignored/999_hidden.goal.md",
                goal_id="999",
                status="OPEN",
                node="hidden-node",
            )

            result = startup_runtime.select_v10_shadow_goal(root)

            self.assertEqual(result.selected_goal, "docs/routeB_bus/058_visible.goal.md")
            self.assertFalse(result.fatal_errors, result.fatal_errors)

    def test_modern_answer_phase_node_result_and_status_drift_are_fatal(self) -> None:
        cases = {
            "phase": (
                "GOAL: '056'\nPHASE: 'wrong'\nNODE: strict-node\nSTATUS: CLOSED\nRESULT: PASS\n"
            ),
            "node": ("GOAL: '056'\nPHASE: '1'\nNODE: wrong-node\nSTATUS: CLOSED\nRESULT: PASS\n"),
            "node_missing": ("GOAL: '056'\nPHASE: '1'\nSTATUS: CLOSED\nRESULT: PASS\n"),
            "node_null": ("GOAL: '056'\nPHASE: '1'\nNODE: ~\nSTATUS: CLOSED\nRESULT: PASS\n"),
            "result": (
                "GOAL: '056'\nPHASE: '1'\nNODE: strict-node\nSTATUS: CLOSED\nRESULT: '   '\n"
            ),
            "result_tilde": (
                "GOAL: '056'\nPHASE: '1'\nNODE: strict-node\nSTATUS: CLOSED\nRESULT: ~\n"
            ),
            "result_null": (
                "GOAL: '056'\nPHASE: '1'\nNODE: strict-node\nSTATUS: CLOSED\nRESULT: Null\n"
            ),
            "status": ("GOAL: '056'\nPHASE: '1'\nNODE: strict-node\nSTATUS: OPEN\nRESULT: PASS\n"),
        }
        for label, answer_header in cases.items():
            with self.subTest(drift=label), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._control(root)
                self._current(root, "CLOSED")
                goal = self._goal(
                    root,
                    "docs/routeB_bus/056a_strict.goal.md",
                    goal_id="056",
                    status="OPEN",
                    node="strict-node",
                )
                goal.write_text(
                    goal.read_text(encoding="utf-8").replace(
                        "STATUS: OPEN\n", "PHASE: '1'\nSTATUS: OPEN\n"
                    ),
                    encoding="utf-8",
                )
                goal.with_name("056a_strict.answer.md").write_text(
                    f"```yaml\n{answer_header}```\n", encoding="utf-8"
                )

                result = startup_runtime.select_v10_shadow_goal(root)

                self.assertIsNone(result.selected_goal)
                self.assertTrue(
                    any(item.startswith("STARTUP_ANSWER_INVALID:") for item in result.fatal_errors),
                    result.fatal_errors,
                )

    def test_paired_answer_cannot_hide_unknown_or_malformed_goal_status(self) -> None:
        cases = {
            "unknown": (
                "STATUS: OPEN\n",
                "STATUS: UNKNOWN_READY\n",
                "STARTUP_UNKNOWN_GOAL_STATUS:",
            ),
            "missing": (
                "STATUS: OPEN\n",
                "",
                "STARTUP_GOAL_HEADER_INVALID:",
            ),
            "yaml_null": (
                "STATUS: OPEN\n",
                "STATUS: ~\n",
                "STARTUP_GOAL_HEADER_INVALID:",
            ),
        }
        for label, (old, new, expected) in cases.items():
            with self.subTest(status=label), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._control(root)
                self._current(root, "CLOSED")
                goal = self._goal(
                    root,
                    "docs/routeB_bus/058_status.goal.md",
                    goal_id="058",
                    status="OPEN",
                    node="status-node",
                )
                goal.write_text(
                    goal.read_text(encoding="utf-8").replace(old, new),
                    encoding="utf-8",
                )
                goal.with_name("058_status.answer.md").write_text(
                    "```yaml\nGOAL: '058'\nNODE: status-node\nSTATUS: CLOSED\nRESULT: PASS\n```\n",
                    encoding="utf-8",
                )

                result = startup_runtime.select_v10_shadow_goal(root)

                self.assertIsNone(result.selected_goal)
                self.assertTrue(
                    any(item.startswith(expected) for item in result.fatal_errors),
                    result.fatal_errors,
                )
                self.assertEqual(len(result.fatal_errors), len(set(result.fatal_errors)))

    def test_phase_alias_and_node_cannot_use_yaml_null_identity(self) -> None:
        cases = {
            "phase": ("PHASE: ~", "NODE: strict-node"),
            "node": ("PHASE: '1'", "NODE: ~"),
        }
        for label, (phase_line, node_line) in cases.items():
            with self.subTest(identity=label), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._control(root)
                self._current(root, "CLOSED")
                goal = self._goal(
                    root,
                    "docs/routeB_bus/056a_identity.goal.md",
                    goal_id="056",
                    status="OPEN",
                    node="strict-node",
                )
                goal.write_text(
                    goal.read_text(encoding="utf-8")
                    .replace("NODE: strict-node", node_line)
                    .replace("STATUS: OPEN", f"{phase_line}\nSTATUS: OPEN"),
                    encoding="utf-8",
                )
                goal.with_name("056a_identity.answer.md").write_text(
                    "```yaml\nGOAL: '056'\n"
                    f"{phase_line}\n{node_line}\n"
                    "STATUS: CLOSED\nRESULT: PASS\n```\n",
                    encoding="utf-8",
                )

                result = startup_runtime.select_v10_shadow_goal(root)

                self.assertIsNone(result.selected_goal)
                expected = (
                    "STARTUP_GOAL_IDENTITY_MISMATCH:"
                    if label == "phase"
                    else "STARTUP_ANSWER_INVALID:"
                )
                self.assertTrue(
                    any(item.startswith(expected) for item in result.fatal_errors),
                    result.fatal_errors,
                )

    def test_exact_goal_modern_closure_does_not_require_phase(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            goal = self._goal(
                root,
                "docs/routeB_bus/058_closed.goal.md",
                goal_id="058",
                status="CLOSED",
                node="closed-node",
            )
            goal.with_name("058_closed.answer.md").write_text(
                "```yaml\nGOAL: '058'\nNODE: closed-node\nSTATUS: CLOSED\nRESULT: PASS\n```\n",
                encoding="utf-8",
            )
            self._execution_state(root, "", "")
            self._git_commit(root)

            result = startup_runtime.build_shadow_snapshot(root)

            self.assertFalse(result.fatal_errors, result.fatal_errors)
            self.assertIsNone(result.selected_goal)

    def test_paired_paused_goal_is_fatal(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            goal = self._goal(
                root,
                "docs/routeB_bus/058_paused.goal.md",
                goal_id="058",
                status="PAUSED_RESTORABLE",
                node="paused-node",
            )
            goal.with_name("058_paused.answer.md").write_text(
                "```yaml\nGOAL: '058'\nNODE: paused-node\nSTATUS: CLOSED\nRESULT: PASS\n```\n",
                encoding="utf-8",
            )

            result = startup_runtime.select_v10_shadow_goal(root)

            self.assertIsNone(result.selected_goal)
            self.assertTrue(
                any(
                    item.startswith("STARTUP_ANSWER_INVALID:paused goal has answer:")
                    for item in result.fatal_errors
                ),
                result.fatal_errors,
            )

    def test_tracked_bus_symlink_mode_is_fatal(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            (root / "docs/routeB_bus").mkdir(parents=True)
            self._execution_state(root, "", "")
            outside = root / "outside"
            outside.mkdir()
            (root / "docs/routeB_bus/tracked-link").symlink_to(outside, target_is_directory=True)
            self._git_commit(root)

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertTrue(
                any(item.startswith("STARTUP_SYMLINK_COMPONENT:") for item in snapshot.fatal_errors)
            )

    def test_porcelain_v2_z_handles_weird_rename_and_unmerged_paths(self) -> None:
        oid = b"a" * 40
        raw = (
            b"# branch.oid "
            + oid
            + b"\0# branch.head main\0"
            + b"1 .M N... 100644 100644 100644 "
            + oid
            + b" "
            + oid
            + b" weird space\nname\0"
            + b"2 R. N... 100644 100644 100644 "
            + oid
            + b" "
            + oid
            + b" R100 renamed new\nname\0renamed old name\0"
            + b"u UU N... 100644 100644 100644 100644 "
            + oid
            + b" "
            + oid
            + b" "
            + oid
            + b" conflict\nname\0"
        )
        status_completed = subprocess.CompletedProcess(["git", "status"], 0, stdout=raw)
        others_completed = subprocess.CompletedProcess(
            ["git", "ls-files"], 0, stdout=b"nested/untracked\0"
        )

        with mock.patch.object(
            startup_runtime.subprocess,
            "run",
            side_effect=(status_completed, others_completed),
        ):
            observed = startup_runtime._git_observation(Path("."), owned_paths=("nested",))

            commands = [call.args[0] for call in startup_runtime.subprocess.run.call_args_list]

        self.assertIn("weird space\nname", observed.dirty_paths)
        self.assertIn("renamed new\nname", observed.dirty_paths)
        self.assertIn("renamed old name", observed.dirty_paths)
        self.assertEqual(observed.unmerged_paths, ("conflict\nname",))
        self.assertIn("nested/untracked", observed.dirty_paths)
        self.assertTrue(any(item.startswith("STARTUP_GIT_UNMERGED:") for item in observed.errors))
        self.assertIn("--untracked-files=normal", commands[0])
        self.assertFalse(any(item.startswith("--ignored") for item in commands[0]))
        self.assertEqual(
            commands[1],
            [
                "git",
                "ls-files",
                "--others",
                "--exclude-standard",
                "-z",
                "--",
                "nested",
            ],
        )

    def test_linked_worktree_common_dir_lock_is_held_and_identity_checked(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            root = base / "worktree"
            common = base / "common"
            git_dir = common / "worktrees" / "w1"
            root.mkdir()
            git_dir.mkdir(parents=True)
            (root / ".git").write_text(f"gitdir: {git_dir}\n", encoding="utf-8")
            (git_dir / "commondir").write_text("../..\n", encoding="utf-8")
            lock = common / "q3-three-body.writer.lock"
            lock.write_text("idle\n", encoding="utf-8")

            guard, error = startup_runtime._acquire_writer_lock(root)
            try:
                self.assertIsNone(error)
                self.assertEqual(guard.path, lock)
                self.assertIsNone(guard.recheck())
                replacement = common / "replacement.lock"
                lock.rename(replacement)
                lock.write_text("new\n", encoding="utf-8")
                self.assertEqual(guard.recheck(), "FATAL:WRITER_LOCK_IDENTITY_CHANGED")
            finally:
                guard.close()

    def test_missing_writer_lock_is_fatal_and_never_created(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            lock = root / ".git/q3-three-body.writer.lock"

            guard, error = startup_runtime._acquire_writer_lock(root)

            self.assertEqual(error, "FATAL:WRITER_LOCK_UNAVAILABLE:missing")
            self.assertFalse(lock.exists())
            lock.write_text("appeared\n", encoding="utf-8")
            self.assertEqual(guard.recheck(), "FATAL:WRITER_LOCK_IDENTITY_CHANGED")
            guard.close()

    def test_path_and_final_status_mutations_fail_closed(self) -> None:
        for target_name in (
            "control",
            "channel",
            "manifest",
            "goal",
            "source",
            "state",
        ):
            with self.subTest(target=target_name), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                paths = self._committed_open_snapshot_fixture(root)
                original = startup_runtime._recheck_fingerprints

                def mutate_then_recheck(
                    repo: Path,
                    fingerprints: tuple[tuple[object, startup_runtime._PathFingerprint], ...],
                    *,
                    target: Path = paths[target_name],
                ) -> tuple[str, ...]:
                    target.write_bytes(target.read_bytes() + b"\n")
                    return original(repo, fingerprints)  # type: ignore[arg-type]

                with mock.patch.object(
                    startup_runtime,
                    "_recheck_fingerprints",
                    side_effect=mutate_then_recheck,
                ):
                    snapshot = startup_runtime.build_startup_snapshot(root)

                self.assertTrue(
                    any(
                        item.startswith("STARTUP_PATH_CONCURRENT_MUTATION:")
                        for item in snapshot.fatal_errors
                    )
                )
                if target_name in {"control", "channel", "manifest", "state"}:
                    self.assertIn("STARTUP_GIT_CONCURRENT_MUTATION", snapshot.fatal_errors)

    def test_new_physical_bus_record_during_snapshot_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._committed_open_snapshot_fixture(root)
            original = startup_runtime._recheck_fingerprints

            def add_hidden_goal_then_recheck(
                repo: Path,
                fingerprints: tuple[tuple[object, startup_runtime._PathFingerprint], ...],
            ) -> tuple[str, ...]:
                self._goal(
                    root,
                    "docs/routeB_bus/999_concurrent.goal.md",
                    goal_id="999",
                    status="OPEN",
                    node="concurrent-node",
                )
                return original(repo, fingerprints)  # type: ignore[arg-type]

            with mock.patch.object(
                startup_runtime,
                "_recheck_fingerprints",
                side_effect=add_hidden_goal_then_recheck,
            ):
                snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertIn("STARTUP_BUS_CONCURRENT_MUTATION", snapshot.fatal_errors)
            self.assertIsNone(snapshot.selected_goal)

    def test_answer_bytes_are_fingerprinted_and_rechecked(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            goal = self._goal(
                root,
                "docs/routeB_bus/058_closed.goal.md",
                goal_id="058",
                status="CLOSED",
                node="closed-node",
            )
            answer = goal.with_name("058_closed.answer.md")
            answer.write_text(
                "```yaml\nGOAL: '058'\nSTATUS: CLOSED\nRESULT: PASS\n```\n",
                encoding="utf-8",
            )
            self._execution_state(root, "", "")
            self._git_commit(root)
            original = startup_runtime._recheck_fingerprints
            answer_rel = answer.relative_to(root).as_posix()
            observed_answer_binding = False

            def mutate_answer_then_recheck(
                repo: Path,
                fingerprints: tuple[tuple[object, startup_runtime._PathFingerprint], ...],
            ) -> tuple[str, ...]:
                nonlocal observed_answer_binding
                observed_answer_binding = any(
                    relative.as_posix() == answer_rel for relative, _fingerprint in fingerprints
                )
                answer.write_bytes(answer.read_bytes() + b"\n")
                return original(repo, fingerprints)  # type: ignore[arg-type]

            with mock.patch.object(
                startup_runtime,
                "_recheck_fingerprints",
                side_effect=mutate_answer_then_recheck,
            ):
                snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertTrue(observed_answer_binding)
            self.assertIn(
                f"STARTUP_PATH_CONCURRENT_MUTATION:{answer_rel}",
                snapshot.fatal_errors,
            )

    def test_theorem_and_consumer_blockers_precede_generic_features(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._committed_open_snapshot_fixture(root, theorem=None, consumer=None)

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertEqual(
                snapshot.blocked_features[:2],
                (
                    "BLOCKED_FEATURE:EXACT_THEOREM_EDGE_UNSELECTED",
                    "BLOCKED_FEATURE:EXACT_CONSUMER_EDGE_UNSELECTED",
                ),
            )
            self.assertEqual(snapshot.blocked_features[2], "RUN")

    def test_duplicate_control_header_and_empty_current_fail_safely(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            control = root / "docs/CODEX_CONTROL.md"
            control.write_text(
                control.read_text(encoding="utf-8") + "\n```yaml\nCONTROL_ID: Q3_EXECUTOR_CONTROL\n"
                "CONTROL_VERSION: 10\nSTATUS: ACTIVE\n```\n",
                encoding="utf-8",
            )
            self._current(root, "EMPTY")
            (root / "docs/routeB_bus").mkdir(parents=True)
            self._execution_state(root, "", "")
            self._git_commit(root)

            snapshot = startup_runtime.build_startup_snapshot(root)

            self.assertTrue(
                any(item.startswith("STARTUP_CONTROL_INVALID:") for item in snapshot.fatal_errors)
            )
            self.assertIsNone(snapshot.selected_goal)
            self.assertIn("CURRENT_EMPTY_IGNORED", snapshot.warnings)

    def test_git_call_budget_is_at_most_five(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = self._committed_open_snapshot_fixture(root)
            owned = paths["source"].relative_to(root).as_posix()
            calls: list[tuple[str, ...]] = []
            environments: list[dict[str, str]] = []
            real_run = startup_runtime.subprocess.run

            def count_git(args: list[str], *pos: object, **kwargs: object) -> object:
                if args and args[0] == "git":
                    calls.append(tuple(args))
                    environments.append(kwargs["env"])  # type: ignore[arg-type]
                return real_run(args, *pos, **kwargs)  # type: ignore[arg-type]

            with mock.patch.object(startup_runtime.subprocess, "run", side_effect=count_git):
                snapshot = startup_runtime.build_startup_snapshot(root, owned_paths=(owned,))

            self.assertEqual(snapshot.schema, "q3_startup_snapshot.v10.v1")
            self.assertEqual(snapshot.mode, "PRODUCTION_V10_READ_ONLY")
            self.assertEqual(snapshot.control_version, 10)
            self.assertEqual(snapshot.next_action, "INSPECT_SELECTED_GOAL")
            self.assertLessEqual(len(calls), 5)
            self.assertTrue(any(call[:2] == ("git", "ls-files") for call in calls), calls)
            self.assertTrue(environments)
            self.assertTrue(all(env.get("GIT_OPTIONAL_LOCKS") == "0" for env in environments))
            rendered = json.dumps(snapshot.to_dict(), indent=2)
            self.assertLessEqual(len(rendered.encode("utf-8")), 4096)
            self.assertLessEqual(len(rendered.splitlines()), 60)

    def test_production_git_observation_does_not_refresh_index(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = self._committed_open_snapshot_fixture(root)
            index = root / ".git/index"
            before = (hashlib.sha256(index.read_bytes()).hexdigest(), index.stat().st_mtime_ns)
            control_stat = paths["control"].stat()
            os.utime(
                paths["control"],
                ns=(control_stat.st_atime_ns, control_stat.st_mtime_ns + 5_000_000_000),
            )

            snapshot = startup_runtime.build_startup_snapshot(root)
            after = (hashlib.sha256(index.read_bytes()).hexdigest(), index.stat().st_mtime_ns)

            self.assertTrue(snapshot.run_authorized, snapshot.fatal_errors)
            self.assertEqual(before, after)

    def test_production_headerless_pair_requires_exact_frozen_identity(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            goal = root / "docs/routeB_bus/001a_historical.goal.md"
            goal.parent.mkdir(parents=True, exist_ok=True)
            goal.write_text("legacy goal without machine header\n", encoding="utf-8")
            answer = goal.with_name("001a_historical.answer.md")
            answer.write_text("legacy prose without machine header\n", encoding="utf-8")
            source = root / "docs/routeB_bus/live_source.md"
            source.write_text("live source\n", encoding="utf-8")
            source_bytes = source.read_bytes()
            source_blob = hashlib.sha1(
                b"blob " + str(len(source_bytes)).encode("ascii") + b"\0" + source_bytes
            ).hexdigest()
            live_goal = self._goal(
                root,
                "docs/routeB_bus/058_live.goal.md",
                goal_id="058",
                status="OPEN",
                node="live-node",
                source="docs/routeB_bus/live_source.md",
                source_pin=source_blob,
            )
            self._execution_state(root, "docs/routeB_bus/058_live.goal.md", "058")
            self._git_commit(root)
            baseline = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()
            with (
                mock.patch.object(
                    startup_runtime,
                    "HISTORICAL_PAIRED_BASELINE_COMMIT",
                    baseline,
                ),
            ):
                committed = startup_runtime.build_startup_snapshot(root)
                self.assertEqual(
                    committed.selected_goal,
                    live_goal.relative_to(root).as_posix(),
                )
                self.assertTrue(committed.run_authorized, committed.fatal_errors)

                answer_rel = answer.relative_to(root).as_posix()
                subprocess.run(
                    ["git", "update-index", "--skip-worktree", "--", answer_rel],
                    cwd=root,
                    check=True,
                )
                answer.write_text("changed historical prose\n", encoding="utf-8")
                corrupted = startup_runtime.build_startup_snapshot(root)

            self.assertFalse(corrupted.git_dirty)
            self.assertFalse(corrupted.run_authorized)
            self.assertIsNone(corrupted.selected_goal)
            self.assertTrue(
                any(
                    item.startswith("STARTUP_HISTORICAL_PAIRED_BLOB_DRIFT:")
                    for item in corrupted.fatal_errors
                ),
                corrupted.fatal_errors,
            )

    def test_active_current_missing_edges_are_scoped_blockers(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            (root / "docs/routeB_bus").mkdir(parents=True)
            self._execution_state(root, "", "")
            task_rel = "docs/Codex/TASK_active.md"
            task = root / task_rel
            task.parent.mkdir(parents=True, exist_ok=True)
            task.write_text("```yaml\nNODE: current-node\n```\n", encoding="utf-8")
            self._git_commit(root)
            source_commit = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()
            self._current(
                root,
                "ACTIVE",
                task_file=task_rel,
                source_commit=source_commit,
            )
            subprocess.run(["git", "add", "docs/Codex/CURRENT.md"], cwd=root, check=True)
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=Startup Plant",
                    "-c",
                    "user.email=startup@example.invalid",
                    "commit",
                    "-q",
                    "-m",
                    "activate current",
                ],
                cwd=root,
                check=True,
            )

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertEqual(snapshot.selected_goal, task_rel)
            self.assertFalse(snapshot.fatal_errors, snapshot.fatal_errors)
            self.assertEqual(
                snapshot.blocked_features[:2],
                (
                    "BLOCKED_FEATURE:EXACT_THEOREM_EDGE_UNSELECTED",
                    "BLOCKED_FEATURE:EXACT_CONSUMER_EDGE_UNSELECTED",
                ),
            )
            self.assertEqual(snapshot.next_action, "SHADOW_BLOCKED_EXACT_EDGE_SELECTION")

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            (root / "docs/routeB_bus").mkdir(parents=True)
            self._execution_state(root, "", "")
            task_rel = "docs/Codex/TASK_active.md"
            task = root / task_rel
            task.write_text(
                "```yaml\nTHEOREM: current-theorem\nTERMINAL_CONSUMER: current-consumer\n```\n",
                encoding="utf-8",
            )
            self._git_commit(root)
            source_commit = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()
            self._current(
                root,
                "ACTIVE",
                task_file=task_rel,
                source_commit=source_commit,
            )
            subprocess.run(["git", "add", "docs/Codex/CURRENT.md"], cwd=root, check=True)
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=Startup Plant",
                    "-c",
                    "user.email=startup@example.invalid",
                    "commit",
                    "-q",
                    "-m",
                    "activate current without node",
                ],
                cwd=root,
                check=True,
            )

            missing_node = startup_runtime.build_shadow_snapshot(root)

            self.assertIn("STARTUP_EXACT_PINS_MISSING", missing_node.fatal_errors)
            self.assertEqual(missing_node.next_action, "STOP_FAIL_CLOSED")


if __name__ == "__main__":
    unittest.main()
