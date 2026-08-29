"""Block 0 plants for bounded request-history validation and in-run gate reuse."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from orchestrator import spine, three_body_loop


def _run(root: Path, *args: str) -> str:
    return subprocess.run(
        list(args),
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _init(root: Path) -> None:
    _run(root, "git", "init", "-q", "-b", "rh_clean")


def _commit(root: Path, message: str) -> str:
    _run(root, "git", "add", "-A")
    _run(
        root,
        "git",
        "-c",
        "user.name=Block Zero Plant",
        "-c",
        "user.email=block-zero@example.invalid",
        "commit",
        "-qm",
        message,
    )
    return _run(root, "git", "rev-parse", "HEAD")


def _empty_quarantine(root: Path) -> Path:
    path = root / "orchestrator" / "state" / "SEMANTIC_QUARANTINE.json"
    path.parent.mkdir(parents=True)
    path.write_text(
        json.dumps(
            {
                "active_lease": None,
                "control_version": 9,
                "entries": [],
                "event_ledger": [],
                "schema": "q3_semantic_quarantine.v1",
                "tactical_repairs": [],
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    return path


class RequestHistoryBatchPlants(unittest.TestCase):
    def test_batch_lookup_rejects_line_break_in_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _init(root)
            (root / "README").write_text("base\n", encoding="utf-8")
            head = _commit(root, "base")
            with self.assertRaises(three_body_loop.ThreeBodyViolation) as caught:
                three_body_loop._first_commit_with_blob(
                    repo_root=root,
                    commits=(head,),
                    path="docs/routeB_bus/CODEX_REQ_OK.md\nHEAD:README",
                    expected_blob="a" * 40,
                    code="CODEX_REQUEST_STATE_INVALID",
                )
            self.assertEqual(caught.exception.code, "CODEX_REQUEST_STATE_INVALID")

    def test_batch_lookup_preserves_first_appearance_after_blob_reappears(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _init(root)
            target = root / "docs" / "routeB_bus" / "CODEX_REQ_PLANT.md"
            target.parent.mkdir(parents=True)
            target.write_text("first bytes\n", encoding="utf-8")
            first = _commit(root, "first appearance")
            expected_blob = _run(root, "git", "rev-parse", f"{first}:docs/routeB_bus/CODEX_REQ_PLANT.md")

            target.write_text("different bytes\n", encoding="utf-8")
            _commit(root, "different blob")
            target.write_text("first bytes\n", encoding="utf-8")
            _commit(root, "blob reappears")
            commits = three_body_loop._first_parent_commits(
                root, code="CODEX_REQUEST_STATE_INVALID"
            )

            original_run = subprocess.run
            with mock.patch.object(
                three_body_loop.subprocess,
                "run",
                wraps=original_run,
            ) as run:
                actual = three_body_loop._first_commit_with_blob(
                    repo_root=root,
                    commits=commits,
                    path="docs/routeB_bus/CODEX_REQ_PLANT.md",
                    expected_blob=expected_blob,
                    code="CODEX_REQUEST_STATE_INVALID",
                )

            self.assertEqual(actual, first)
            self.assertEqual(run.call_count, 1)
            command = run.call_args.args[0]
            self.assertEqual(command[:3], ["git", "cat-file", "--batch-check=%(objectname)"])

    def test_batch_lookup_sees_first_parent_merge_state(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _init(root)
            (root / "README").write_text("base\n", encoding="utf-8")
            _commit(root, "base")
            _run(root, "git", "checkout", "-qb", "request-side")
            target = root / "docs" / "routeB_bus" / "CODEX_REQ_MERGE.md"
            target.parent.mkdir(parents=True)
            target.write_text("merged request\n", encoding="utf-8")
            _commit(root, "request on side branch")
            _run(root, "git", "checkout", "-q", "rh_clean")
            (root / "MAIN").write_text("main\n", encoding="utf-8")
            _commit(root, "main advance")
            _run(
                root,
                "git",
                "-c",
                "user.name=Block Zero Plant",
                "-c",
                "user.email=block-zero@example.invalid",
                "merge",
                "--no-ff",
                "-qm",
                "merge request",
                "request-side",
            )
            merge = _run(root, "git", "rev-parse", "HEAD")
            expected_blob = _run(
                root, "git", "rev-parse", "HEAD:docs/routeB_bus/CODEX_REQ_MERGE.md"
            )
            commits = three_body_loop._first_parent_commits(
                root, code="CODEX_REQUEST_STATE_INVALID"
            )
            actual = three_body_loop._first_commit_with_blob(
                repo_root=root,
                commits=commits,
                path="docs/routeB_bus/CODEX_REQ_MERGE.md",
                expected_blob=expected_blob,
                code="CODEX_REQUEST_STATE_INVALID",
            )
            self.assertEqual(actual, merge)

    def test_repository_gate_reads_first_parent_history_once(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _init(root)
            (root / "README").write_text("base\n", encoding="utf-8")
            head = _commit(root, "base")
            quarantine = _empty_quarantine(root)
            bus = root / "docs" / "routeB_bus"
            bus.mkdir(parents=True)
            for suffix in ("A", "B"):
                (bus / f"CODEX_REQ_STATE_{suffix}.yaml").write_text("plant\n", encoding="utf-8")

            states = iter(
                [
                    {
                        "status": "ANSWERED",
                        "request_id": "REQ-A",
                        "blocker_fingerprint": "a" * 64,
                        "codex_session_id": "SESSION-A",
                    },
                    {
                        "status": "ANSWERED",
                        "request_id": "REQ-B",
                        "blocker_fingerprint": "b" * 64,
                        "codex_session_id": "SESSION-B",
                    },
                ]
            )
            with mock.patch.object(
                three_body_loop,
                "_first_parent_commits",
                return_value=(head,),
            ) as history, mock.patch.object(
                three_body_loop,
                "validate_request_file_binding",
                side_effect=lambda *args, **kwargs: next(states),
            ) as binding, mock.patch.object(
                three_body_loop,
                "validate_request_open_set",
                return_value=[],
            ):
                three_body_loop.validate_repository_gate(
                    repo_root=root,
                    state_path=quarantine,
                )

            history.assert_called_once_with(root, code="CODEX_REQUEST_STATE_INVALID")
            self.assertEqual(binding.call_count, 2)
            for call in binding.call_args_list:
                self.assertEqual(call.kwargs["first_parent_commits"], (head,))


class SpineRunReusePlants(unittest.TestCase):
    def test_main_reuses_one_validation_for_state_and_render(self) -> None:
        validation = {"authority": "TEST_AUTHORITY"}
        state: dict[str, object] = {"schema": "plant"}
        with mock.patch.object(sys, "argv", ["spine.py", "--stdout"]), mock.patch.object(
            spine, "validate_p9a", return_value=validation
        ) as validate, mock.patch.object(
            spine, "build_state", return_value=state
        ) as build_state, mock.patch.object(
            spine, "build", return_value="PLANT_VIEW\n"
        ), mock.patch.object(sys.stdout, "write"):
            self.assertEqual(spine.main(), 0)

        validate.assert_called_once_with()
        build_state.assert_called_once_with(validation)


if __name__ == "__main__":
    unittest.main()
