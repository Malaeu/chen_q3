"""Control-v10 pure startup selector and v9 shadow snapshot tests."""

from __future__ import annotations

import dataclasses
import fcntl
import hashlib
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from orchestrator import startup_runtime


class StartupRuntimeTests(unittest.TestCase):
    @staticmethod
    def _control(root: Path, version: int = 9, status: str = "ACTIVE") -> None:
        path = root / "docs" / "CODEX_CONTROL.md"
        path.parent.mkdir(parents=True, exist_ok=True)
        v10_locks = (
            "HONESTY_STATE: CHALLENGER_NOT_RH\n"
            "OWNER_ONLY_BOUNDARY: PX_RH_CLAIM\n"
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
        consumer_line = (
            f"TERMINAL_CONSUMER: {consumer}\n" if consumer is not None else ""
        )
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
        (root / ".git" / "q3-three-body.writer.lock").write_text(
            "idle\n", encoding="utf-8"
        )
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
        theorem: str | None = "theorem-pin",
        consumer: str | None = "consumer-pin",
    ) -> dict[str, Path]:
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
            root
            / "q3.lean.aristotle/ACTIVE/requests/"
            "routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json"
        )
        return {
            "control": root / "docs/CODEX_CONTROL.md",
            "current": root / "docs/Codex/CURRENT.md",
            "goal": goal,
            "source": source,
            "state": state,
        }

    def test_whole_physical_bus_selects_only_open_goal_without_numeric_authority(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "ACTIVE")
            task = root / "docs" / "Codex" / "TASK_active.md"
            task.write_text("```yaml\nNODE: current-node\n```\n", encoding="utf-8")
            self._goal(
                root,
                "docs/routeB_bus/archive/deep/001_live.goal.md",
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
                "docs/routeB_bus/archive/deep/001_live.goal.md",
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
                    item.startswith("STARTUP_AMBIGUOUS_OPEN_GOALS:")
                    for item in result.fatal_errors
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
                any(item.startswith("STARTUP_ANSWER_INVALID:") for item in result.fatal_errors)
            )

    def test_committed_orphan_or_misnamed_answer_fails_closed(self) -> None:
        for answer_relative in (
            "docs/routeB_bus/777_orphan.answer.md",
            "docs/routeB_bus/058_wrong.answer.md",
        ):
            with self.subTest(answer=answer_relative), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._control(root)
                self._current(root, "CLOSED")
                if "058_wrong" in answer_relative:
                    self._goal(
                        root,
                        "docs/routeB_bus/058_live.goal.md",
                        goal_id="058",
                        status="OPEN",
                        node="live-node",
                    )
                answer = root / answer_relative
                answer.parent.mkdir(parents=True, exist_ok=True)
                answer.write_text(
                    "```yaml\nGOAL: '058'\nSTATUS: CLOSED\nRESULT: PASS\n```\n",
                    encoding="utf-8",
                )
                self._execution_state(root, "", "")
                self._git_commit(root)

                snapshot = startup_runtime.build_shadow_snapshot(root)

                self.assertTrue(
                    any(
                        item.startswith("STARTUP_ANSWER_ORPHAN:")
                        for item in snapshot.fatal_errors
                    ),
                    snapshot.fatal_errors,
                )

    def test_committed_paired_answer_header_mismatch_fails_closed(self) -> None:
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
                "```yaml\nGOAL: '999'\nSTATUS: CLOSED\nRESULT: PASS\n```\n",
                encoding="utf-8",
            )
            self._execution_state(root, "", "")
            self._git_commit(root)

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertTrue(
                any(
                    item.startswith("STARTUP_ANSWER_INVALID:")
                    for item in snapshot.fatal_errors
                ),
                snapshot.fatal_errors,
            )

    def test_committed_goal_filename_header_mismatch_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            self._goal(
                root,
                "docs/routeB_bus/058a_new.goal.md",
                goal_id="058",
                status="OPEN",
                node="new-node",
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

    def test_ignored_orphan_answer_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            (root / "docs/routeB_bus").mkdir(parents=True)
            (root / ".gitignore").write_text(
                "docs/routeB_bus/ignored/\n", encoding="utf-8"
            )
            self._execution_state(root, "", "")
            self._git_commit(root)
            answer = root / "docs/routeB_bus/ignored/777_orphan.answer.md"
            answer.parent.mkdir(parents=True)
            answer.write_text(
                "```yaml\nGOAL: '777'\nSTATUS: CLOSED\nRESULT: PASS\n```\n",
                encoding="utf-8",
            )

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertTrue(
                any(
                    item.startswith("STARTUP_ANSWER_ORPHAN:")
                    for item in snapshot.fatal_errors
                ),
                snapshot.fatal_errors,
            )

    def test_frozen_historical_orphan_answer_is_exactly_grandfathered(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            answer = root / "docs/routeB_bus/001_historical.answer.md"
            answer.parent.mkdir(parents=True)
            answer.write_text("legacy answer-only prose\n", encoding="utf-8")
            self._execution_state(root, "", "")
            self._git_commit(root)
            baseline = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()

            with mock.patch.object(startup_runtime, "FROZEN_V9_BASELINE", baseline):
                frozen = startup_runtime.build_shadow_snapshot(root)
            self.assertFalse(
                any(
                    item.startswith("STARTUP_ANSWER_ORPHAN:")
                    for item in frozen.fatal_errors
                ),
                frozen.fatal_errors,
            )

            answer.write_text("changed answer-only prose\n", encoding="utf-8")
            with mock.patch.object(startup_runtime, "FROZEN_V9_BASELINE", baseline):
                changed = startup_runtime.build_shadow_snapshot(root)
            self.assertTrue(
                any(
                    item.startswith("STARTUP_ANSWER_ORPHAN:")
                    for item in changed.fatal_errors
                ),
                changed.fatal_errors,
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

    def test_battle_v10_validation_is_separate_from_v9_shadow_build(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root, version=9)
            self._current(root, "CLOSED")
            (root / "docs" / "routeB_bus").mkdir(parents=True)
            self._git_commit(root)

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertEqual(snapshot.control_version, 9)
            self.assertEqual(snapshot.mode, "SHADOW_NOT_AUTHORITY")
            self.assertFalse(snapshot.run_authorized)
            self.assertIn("CONTROL_V9_SHADOW_BASELINE", snapshot.warnings)
            with self.assertRaisesRegex(
                startup_runtime.StartupRuntimeError,
                "BATTLE_V10_CONTROL_INVALID",
            ):
                startup_runtime.validate_battle_v10_control(root)

            self._control(root, version=10)
            control_path = root / "docs/CODEX_CONTROL.md"
            control_path.write_text(
                "```yaml\nexample: unrelated\n```\n\n"
                + control_path.read_text(encoding="utf-8"),
                encoding="utf-8",
            )
            identity = startup_runtime.validate_battle_v10_control(root)
            self.assertEqual(identity.version, 10)
            self.assertEqual(identity.status, "ACTIVE")

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

            with mock.patch.object(
                startup_runtime.subprocess, "run", side_effect=count_git
            ):
                snapshot = startup_runtime.build_shadow_snapshot(root)

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
            self.assertIn(
                "STARTUP_CURRENT_SOURCE_COMMIT_DRIFT", drifted.fatal_errors
            )

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
                subprocess.run(
                    ["git", "add", "docs/Codex/CURRENT.md"], cwd=root, check=True
                )
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
                self.assertEqual(snapshot.exact_node_pin, "forged-node")
                self.assertIn(
                    "STARTUP_CURRENT_TASK_WORKTREE_DRIFT", snapshot.fatal_errors
                )
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
            subprocess.run(
                ["git", "add", "docs/Codex/CURRENT.md"], cwd=root, check=True
            )
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
                fingerprints: tuple[
                    tuple[object, startup_runtime._PathFingerprint], ...
                ],
            ) -> tuple[str, ...]:
                task.write_bytes(task.read_bytes() + b"\n")
                return original(repo, fingerprints)  # type: ignore[arg-type]

            with mock.patch.object(
                startup_runtime,
                "_recheck_fingerprints",
                side_effect=mutate_task_before_final_recheck,
            ):
                snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertIn(
                "STARTUP_CURRENT_TASK_WORKTREE_DRIFT", snapshot.fatal_errors
            )
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

    def test_untracked_nested_symlink_cannot_hide_open_goal(self) -> None:
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
            (root / "docs/routeB_bus/nested").symlink_to(
                outside, target_is_directory=True
            )

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertTrue(
                any(
                    item.startswith("STARTUP_SYMLINK_COMPONENT:")
                    for item in snapshot.fatal_errors
                )
            )
            self.assertNotEqual(snapshot.selected_goal, "outside/999_hidden.goal.md")

    def test_ignored_bus_directory_cannot_hide_open_goal(self) -> None:
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
            (root / ".gitignore").write_text(
                "docs/routeB_bus/ignored/\n", encoding="utf-8"
            )
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

            self.assertEqual(
                result.selected_goal,
                "docs/routeB_bus/ignored/999_hidden.goal.md",
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
            (root / "docs/routeB_bus/tracked-link").symlink_to(
                outside, target_is_directory=True
            )
            self._git_commit(root)

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertTrue(
                any(
                    item.startswith("STARTUP_TRACKED_BUS_SYMLINK:")
                    for item in snapshot.fatal_errors
                )
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
        completed = subprocess.CompletedProcess(["git", "status"], 0, stdout=raw)

        with mock.patch.object(startup_runtime.subprocess, "run", return_value=completed):
            observed = startup_runtime._git_observation(Path("."))

        self.assertIn("weird space\nname", observed.dirty_paths)
        self.assertIn("renamed new\nname", observed.dirty_paths)
        self.assertIn("renamed old name", observed.dirty_paths)
        self.assertEqual(observed.unmerged_paths, ("conflict\nname",))
        self.assertTrue(
            any(item.startswith("STARTUP_GIT_UNMERGED:") for item in observed.errors)
        )

    def test_linked_worktree_common_dir_lock_is_held_and_identity_checked(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            root = base / "worktree"
            common = base / "common"
            git_dir = common / "worktrees" / "w1"
            root.mkdir()
            git_dir.mkdir(parents=True)
            (root / ".git").write_text(
                f"gitdir: {git_dir}\n", encoding="utf-8"
            )
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
                self.assertEqual(
                    guard.recheck(), "FATAL:WRITER_LOCK_IDENTITY_CHANGED"
                )
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
            self.assertEqual(
                guard.recheck(), "FATAL:WRITER_LOCK_IDENTITY_CHANGED"
            )
            guard.close()

    def test_path_and_final_status_mutations_fail_closed(self) -> None:
        for target_name in ("control", "goal", "source", "state"):
            with self.subTest(target=target_name), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                paths = self._committed_open_snapshot_fixture(root)
                original = startup_runtime._recheck_fingerprints

                def mutate_then_recheck(
                    repo: Path,
                    fingerprints: tuple[
                        tuple[object, startup_runtime._PathFingerprint], ...
                    ],
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
                    snapshot = startup_runtime.build_shadow_snapshot(root)

                self.assertTrue(
                    any(
                        item.startswith("STARTUP_PATH_CONCURRENT_MUTATION:")
                        for item in snapshot.fatal_errors
                    )
                )
                self.assertIn("STARTUP_GIT_CONCURRENT_MUTATION", snapshot.fatal_errors)

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
            baseline = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()
            original = startup_runtime._recheck_fingerprints
            answer_rel = answer.relative_to(root).as_posix()
            observed_answer_binding = False

            def mutate_answer_then_recheck(
                repo: Path,
                fingerprints: tuple[
                    tuple[object, startup_runtime._PathFingerprint], ...
                ],
            ) -> tuple[str, ...]:
                nonlocal observed_answer_binding
                observed_answer_binding = any(
                    relative.as_posix() == answer_rel
                    for relative, _fingerprint in fingerprints
                )
                answer.write_bytes(answer.read_bytes() + b"\n")
                return original(repo, fingerprints)  # type: ignore[arg-type]

            with (
                mock.patch.object(startup_runtime, "FROZEN_V9_BASELINE", baseline),
                mock.patch.object(
                    startup_runtime,
                    "_recheck_fingerprints",
                    side_effect=mutate_answer_then_recheck,
                ),
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
                control.read_text(encoding="utf-8")
                + "\n```yaml\nCONTROL_ID: Q3_EXECUTOR_CONTROL\n"
                "CONTROL_VERSION: 9\nSTATUS: ACTIVE\n```\n",
                encoding="utf-8",
            )
            self._current(root, "EMPTY")
            (root / "docs/routeB_bus").mkdir(parents=True)
            self._execution_state(root, "", "")
            self._git_commit(root)

            snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertTrue(
                any(
                    item.startswith("STARTUP_CONTROL_INVALID:")
                    for item in snapshot.fatal_errors
                )
            )
            self.assertIsNone(snapshot.selected_goal)
            self.assertIn("CURRENT_EMPTY_IGNORED", snapshot.warnings)

    def test_git_call_budget_is_at_most_five(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._committed_open_snapshot_fixture(root)
            calls: list[tuple[str, ...]] = []
            real_run = startup_runtime.subprocess.run

            def count_git(args: list[str], *pos: object, **kwargs: object) -> object:
                if args and args[0] == "git":
                    calls.append(tuple(args))
                return real_run(args, *pos, **kwargs)  # type: ignore[arg-type]

            with mock.patch.object(
                startup_runtime.subprocess, "run", side_effect=count_git
            ):
                snapshot = startup_runtime.build_shadow_snapshot(root)

            self.assertLessEqual(len(calls), 5)
            rendered = json.dumps(snapshot.to_dict(), indent=2)
            self.assertLessEqual(len(rendered.encode("utf-8")), 4096)
            self.assertLessEqual(len(rendered.splitlines()), 60)

    def test_frozen_historical_answer_is_grandfathered_but_change_is_strict(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._control(root)
            self._current(root, "CLOSED")
            goal = self._goal(
                root,
                "docs/routeB_bus/001a_historical.goal.md",
                goal_id="001",
                status="OPEN",
                node="historical",
            )
            answer = goal.with_name("001a_historical.answer.md")
            answer.write_text("legacy prose without machine header\n", encoding="utf-8")
            self._execution_state(root, "", "")
            self._git_commit(root)
            baseline = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            ).stdout.strip()

            with mock.patch.object(startup_runtime, "FROZEN_V9_BASELINE", baseline):
                frozen = startup_runtime.build_shadow_snapshot(root)
            self.assertFalse(
                any(item.startswith("STARTUP_ANSWER_INVALID") for item in frozen.fatal_errors)
            )

            answer.write_text("changed invalid answer\n", encoding="utf-8")
            with mock.patch.object(startup_runtime, "FROZEN_V9_BASELINE", baseline):
                dirty = startup_runtime.build_shadow_snapshot(root)
            self.assertTrue(
                any(
                    item.startswith(
                        ("STARTUP_ANSWER_INVALID", "STARTUP_GOAL_IDENTITY_MISMATCH")
                    )
                    for item in dirty.fatal_errors
                )
            )
            subprocess.run(["git", "add", str(answer.relative_to(root))], cwd=root, check=True)
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
                    "change historical answer",
                ],
                cwd=root,
                check=True,
            )
            with mock.patch.object(startup_runtime, "FROZEN_V9_BASELINE", baseline):
                changed = startup_runtime.build_shadow_snapshot(root)
            self.assertTrue(
                any(
                    item.startswith(
                        ("STARTUP_ANSWER_INVALID", "STARTUP_GOAL_IDENTITY_MISMATCH")
                    )
                    for item in changed.fatal_errors
                )
            )

    def test_active_current_missing_edges_is_fatal(self) -> None:
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
            self.assertIn("STARTUP_EXACT_PINS_MISSING", snapshot.fatal_errors)
            self.assertEqual(
                snapshot.blocked_features[:2],
                (
                    "BLOCKED_FEATURE:EXACT_THEOREM_EDGE_UNSELECTED",
                    "BLOCKED_FEATURE:EXACT_CONSUMER_EDGE_UNSELECTED",
                ),
            )
            self.assertEqual(snapshot.next_action, "STOP_FAIL_CLOSED")


if __name__ == "__main__":
    unittest.main()
