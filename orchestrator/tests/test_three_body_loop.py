"""Control-v9 mandatory plants and supporting mutation/concurrency tests."""

from __future__ import annotations

import hashlib
import json
import multiprocessing as mp
import os
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest import mock

import yaml

from orchestrator import goal_runtime, spine, three_body_loop

SESSION_ID = "01a023d5-6eea-7a61-926f-4101ed130b86"
LATEST_OTHER_SESSION = "01a023d5-6eea-7a61-926f-4101ed130b87"
PHASE = {
    "route_id": "ROUTE",
    "front_id": "FRONT",
    "source_object_family_id": "SOURCE",
    "terminal_consumer_id": "CONSUMER",
    "honesty_state": "CHALLENGER_NOT_RH",
    "convention_lock_id": "LOCK",
}


def _run(
    root: Path, *args: str, check: bool = True, capture: bool = False
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        list(args),
        cwd=root,
        check=check,
        text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.PIPE if capture else None,
    )


def _git_init(root: Path) -> None:
    _run(root, "git", "init", "-q", "-b", "rh_clean")


def _git_commit(root: Path, message: str) -> str:
    _run(root, "git", "add", "-A")
    _run(
        root,
        "git",
        "-c",
        "user.name=Three Body Plant",
        "-c",
        "user.email=three-body-plant@example.invalid",
        "commit",
        "-qm",
        message,
    )
    return _run(root, "git", "rev-parse", "HEAD", capture=True).stdout.strip()


def _empty_state() -> dict[str, object]:
    return {
        "active_lease": None,
        "control_version": 9,
        "entries": [],
        "event_ledger": [],
        "schema": "q3_semantic_quarantine.v1",
        "tactical_repairs": [],
    }


def _write_state(root: Path, state: dict[str, object] | None = None) -> Path:
    path = root / "orchestrator" / "state" / "SEMANTIC_QUARANTINE.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(state or _empty_state(), ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return path


def _write_phase(root: Path) -> None:
    path = root / "orchestrator" / "state" / "CHANNEL_RUNTIME.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "active_proshka_phase": {
                    "status": "ACTIVE",
                    "conversation_id": "plant-conversation",
                    "phase_key": PHASE,
                }
            },
            ensure_ascii=False,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )


def _phase_hash() -> str:
    return hashlib.sha256(
        json.dumps(PHASE, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def _request_bytes(
    *, request_blob_override: str | None = None, source_commit: str | None = None
) -> bytes:
    payload = b"Exact wall payload.\n"
    envelope = {
        "REQUEST_SCHEMA": "q3_codex_request.v1",
        "CODEX_REQ": "REQ-PLANT-001",
        "ELIGIBILITY": "FATAL",
        "CODEX_SESSION_ID": SESSION_ID,
        "PHASE_KEY_HASH": "a" * 64,
        "BLOCKER_FINGERPRINT": "b" * 64,
        "SOURCE_OBJECT": "SOURCE_OBJECT",
        "TERMINAL_CONSUMER": "TERMINAL_CONSUMER",
        "WALL": "Source identity ambiguity",
        "TRIED": ["exact source audit"],
        "ASK_SHELF_RECEIPT": "ASK_SHELF_PASS",
        "CHEAPEST_KILLER_RUN": "SOURCE_BLOB_CHECK",
        "PROGRESS_DELTAS": [],
        "NEED": "Independent decision",
        "BLOCKS": "Current source node",
        "REQUEST_BLOB": request_blob_override or hashlib.sha256(payload).hexdigest(),
        "SOURCE_COMMIT": source_commit or "c" * 40,
    }
    return (
        b"# request\n\n```yaml\n"
        + yaml.safe_dump(envelope, allow_unicode=True, sort_keys=False).encode("utf-8")
        + b"```\n\n"
        + three_body_loop.REQUEST_PAYLOAD_BEGIN
        + payload
        + three_body_loop.REQUEST_PAYLOAD_END
    )


def _request_state(*, status: str = "OPEN", request_raw: bytes | None = None) -> dict[str, object]:
    request_raw = request_raw or _request_bytes()
    request_git_blob = three_body_loop._git_blob_id(request_raw)
    return {
        "schema": "q3_codex_request_state.v1",
        "request_id": "REQ-PLANT-001",
        "request_blob": hashlib.sha256(b"Exact wall payload.\n").hexdigest(),
        "request_git_blob": request_git_blob,
        "request_introducing_commit": "e" * 40,
        "phase_key_hash": "a" * 64,
        "blocker_fingerprint": "b" * 64,
        "codex_session_id": SESSION_ID,
        "status": status,
        "resolved_locally_after_claim": False,
        "revision": 0,
        "previous_state_sha256": None,
    }


def _cas_worker(
    state_path: str, lock_path: str, expected: str, target: str, queue: mp.Queue
) -> None:
    try:
        result = three_body_loop.cas_transition_request_state(
            Path(state_path),
            expected_state_sha256=expected,
            target_status=target,
            lock_path=Path(lock_path),
        )
        queue.put(("OK", result["status"]))
    except three_body_loop.ThreeBodyViolation as exc:
        queue.put(("ERR", exc.code))


def _writer_lock_worker(lock_path: str, ready: mp.Event, release: mp.Event) -> None:
    record = {
        "schema": "q3_writer_lock.v1",
        "worktree": str(Path(lock_path).parent),
        "branch": "rh_clean",
        "writer_body": "CODEX",
        "pid": os.getpid(),
        "process_start_time": three_body_loop._process_start_time(os.getpid()),
        "boot_id": three_body_loop._boot_id(),
        "codex_session_id": SESSION_ID,
        "task_path": "docs/Codex/TASK_PLANT.md",
        "task_blob": "a" * 40,
        "phase_key_hash": "b" * 64,
        "base_head": "c" * 40,
        "run_id": "RUN_LOCK_HOLDER",
        "trigger_nonce": "NONCE_LOCK_HOLDER",
    }
    fd = three_body_loop._acquire_writer_lock(Path(lock_path), record)
    ready.set()
    release.wait(5)
    os.close(fd)


class ThreeBodyPlants(unittest.TestCase):
    def assert_code(self, code: str, fn, *args, **kwargs) -> three_body_loop.ThreeBodyViolation:
        with self.assertRaises(three_body_loop.ThreeBodyViolation) as caught:
            fn(*args, **kwargs)
        self.assertEqual(caught.exception.code, code)
        return caught.exception

    @staticmethod
    def _launch_fixture(root: Path) -> dict[str, object]:
        _git_init(root)
        _write_phase(root)
        state_path = _write_state(root)
        task_path = root / "docs" / "Codex" / "TASK_PLANT.md"
        task_path.parent.mkdir(parents=True)
        task_path.write_text("# pinned task\n", encoding="utf-8")
        control = root / "docs" / "CODEX_CONTROL.md"
        control.write_text("CONTROL_VERSION: 9\n", encoding="utf-8")
        head = _git_commit(root, "launch fixture")
        task_blob = _run(
            root, "git", "hash-object", "docs/Codex/TASK_PLANT.md", capture=True
        ).stdout.strip()
        return {
            "state_path": state_path,
            "lock_path": root / ".git" / "three-body.lock",
            "event": {
                "run_id": "RUN_PLANT_001",
                "trigger_nonce": "NONCE_PLANT_001",
                "source_event_commit": head,
                "answer_blob": "f" * 64,
            },
            "repo_root": root,
            "branch": "rh_clean",
            "session_id": SESSION_ID,
            "task_path": "docs/Codex/TASK_PLANT.md",
            "task_blob": task_blob,
            "phase_key_hash": _phase_hash(),
            "base_head": head,
        }

    def _kernel_green_state(self, root: Path) -> tuple[Path, str]:
        _git_init(root)
        source = root / "Q3" / "Receiver.lean"
        source.parent.mkdir(parents=True)
        source.write_text(
            "axiom normalizedPhysicalMode_continuous : Continuous normalizedPhysicalMode\n",
            encoding="utf-8",
        )
        task = root / "docs" / "Codex" / "TASK.md"
        task.parent.mkdir(parents=True)
        task.write_text("# task\n", encoding="utf-8")
        commit = _git_commit(root, "uninhabited antecedent fixture")
        source_blob = _run(
            root, "git", "rev-parse", f"{commit}:Q3/Receiver.lean", capture=True
        ).stdout.strip()
        task_blob = _run(
            root, "git", "rev-parse", f"{commit}:docs/Codex/TASK.md", capture=True
        ).stdout.strip()
        provenance = [
            {
                "hypothesis_id": "GLOBAL_CONTINUOUS_NORMALIZED_MODE",
                "class": "SOURCE_FIELD",
                "source_or_supplier": "production normalizedPhysicalMode",
                "exact_type": "Continuous normalizedPhysicalMode",
                "consumer": "endpoint equality receiver",
                "production_inhabitant_or_plant": {
                    "kind": "PRODUCTION_INHABITANT",
                    "path": "Q3/Receiver.lean",
                    "blob": source_blob,
                    "declaration": "normalizedPhysicalMode_continuous",
                    "exact_type": "Continuous normalizedPhysicalMode",
                    "verifier": "LINUX_INDEPENDENT_SEMANTIC_AUDITOR",
                    "scope": "production normalized physical modes",
                },
            }
        ]
        canonical, digest = three_body_loop.canonical_hypothesis_provenance(provenance, opens=[])
        state = _empty_state()
        state["entries"] = [
            {
                "entry_id": "D5B28A09_REPLAY",
                "status": "KERNEL_GREEN",
                "task_path": "docs/Codex/TASK.md",
                "task_blob": task_blob,
                "source_path": "Q3/Receiver.lean",
                "source_commit": commit,
                "source_git_blob": source_blob,
                "theorem_ids": ["centerNormalized_eqOn_closed"],
                "admitted_scope": [],
                "terminal_consumer": "endpoint equality receiver",
                "closes": ["FALSE_CLOSE_PLANT"],
                "opens": [],
                "normalization": "centerNormalized",
                "domain": "Icc closed window",
                "quantifiers": "all production normalized physical modes",
                "hypothesis_provenance": canonical,
                "hypothesis_provenance_sha256": digest,
                "semantic_attestation_id": None,
            }
        ]
        return _write_state(root, state), commit

    @staticmethod
    def _semantic_receipt(entry: dict[str, object]) -> dict[str, object]:
        return {
            "schema": "q3_semantic_attestation.v1",
            "attestation_id": entry["semantic_attestation_id"],
            "issuer": "LINUX_INDEPENDENT_SEMANTIC_AUDITOR",
            "status": "ADMITTED",
            "control_version": 9,
            "task_path": entry["task_path"],
            "task_blob": entry["task_blob"],
            "source_commit": entry["source_commit"],
            "source_git_blob": entry["source_git_blob"],
            "theorem_ids": entry["theorem_ids"],
            "admitted_scope": entry["admitted_scope"],
            "terminal_consumer": entry["terminal_consumer"],
            "closes": entry["closes"],
            "opens": entry["opens"],
            "normalization": entry["normalization"],
            "domain": entry["domain"],
            "quantifiers": entry["quantifiers"],
            "hypothesis_provenance_sha256": entry["hypothesis_provenance_sha256"],
        }

    def test_MALFORMED_INHABITANT_OR_PLANT_REPLAY(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state_path, _commit = self._kernel_green_state(root)
            state = three_body_loop.load_state(state_path, repo_root=root)
            self.assertEqual(state["entries"][0]["status"], "KERNEL_GREEN")
            duplicate_pending = json.loads(json.dumps(state))
            duplicate = dict(duplicate_pending["entries"][0])
            duplicate["entry_id"] = "D5B28A09_SECOND_PENDING"
            duplicate["status"] = "SOURCE_WRITTEN"
            duplicate_pending["entries"].append(duplicate)
            self.assert_code(
                "SEMANTIC_QUARANTINE_CAP_EXCEEDED",
                three_body_loop.validate_state,
                duplicate_pending,
                repo_root=root,
            )
            admitted = json.loads(json.dumps(state))
            admitted["entries"][0]["status"] = "SEMANTICALLY_ADMITTED"
            admitted["entries"][0]["admitted_scope"] = ["production"]
            admitted["entries"][0]["semantic_attestation_id"] = "ATTEST_PLANT"
            receipt = self._semantic_receipt(admitted["entries"][0])
            accepted = three_body_loop.validate_state(
                admitted,
                repo_root=root,
                semantic_attestation_resolver=lambda _attestation_id: receipt,
            )
            self.assertEqual(accepted["entries"][0]["admitted_scope"], ["production"])

            replay = json.loads(json.dumps(admitted))
            replay_provenance = replay["entries"][0]["hypothesis_provenance"]
            replay_provenance[0]["production_inhabitant_or_plant"] = (
                "UNINHABITED: Icc.indicator has nonzero endpoint value"
            )
            replay["entries"][0]["hypothesis_provenance_sha256"] = hashlib.sha256(
                three_body_loop._canonical_json_bytes(replay_provenance)
            ).hexdigest()
            replay_receipt = self._semantic_receipt(replay["entries"][0])
            self.assert_code(
                "HYPOTHESIS_PROVENANCE_INVALID",
                three_body_loop.validate_state,
                replay,
                repo_root=root,
                semantic_attestation_resolver=lambda _attestation_id: replay_receipt,
            )

    def test_KERNEL_GREEN_NOT_SEMANTICALLY_ADMITTED(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._kernel_green_state(root)
            _write_phase(root)
            bus = root / "docs" / "routeB_bus"
            bus.mkdir(parents=True)
            goal_runtime._write_goal(bus, "058", PHASE)
            with self.assertRaisesRegex(
                goal_runtime.GoalRuntimeError, "SEMANTIC_QUARANTINE_ACTIVE"
            ):
                goal_runtime.select_action(bus, repo_root=root)

    def test_WRONG_LAST_SESSION(self) -> None:
        command = three_body_loop.build_codex_resume_command(
            session_id=SESSION_ID,
            repo_root=Path("/tmp"),
            output_schema=Path("/tmp/schema.json"),
            final_reply=Path("/tmp/reply.json"),
            prompt=f"REQ_ID=REQ-PLANT session={LATEST_OTHER_SESSION}",
        )
        self.assertIn(SESSION_ID, command)
        self.assertNotIn("--last", command)
        resume_index = command.index("resume")
        self.assertEqual(command[resume_index + 1], SESSION_ID)
        self.assertLess(command.index("-C"), resume_index)
        self.assertLess(command.index("--sandbox"), resume_index)
        self.assertLess(command.index("--output-schema"), resume_index)

    def test_read_only_watch_noops_when_origin_is_not_ahead(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            prompt = root / "docs" / "Codex" / "WATCH_PROMPT.md"
            prompt.parent.mkdir(parents=True)
            prompt.write_text("Inspect remote state only.\n", encoding="utf-8")
            with (
                mock.patch.object(three_body_loop, "_current_branch", return_value="rh_clean"),
                mock.patch.object(three_body_loop, "_git_output", side_effect=[b"", b"0\n"]),
                mock.patch.object(three_body_loop.subprocess, "run") as resume,
            ):
                result = three_body_loop.run_read_only_watch(
                    repo_root=root,
                    branch="rh_clean",
                    session_id=SESSION_ID,
                    prompt_path="docs/Codex/WATCH_PROMPT.md",
                    lock_path=root / "watch.lock",
                )
            self.assertEqual(result, {"result": "NO_REMOTE_ADVANCE", "remote_ahead": 0})
            resume.assert_not_called()

    def test_read_only_watch_uses_pinned_session_and_read_only_sandbox(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            prompt = root / "docs" / "Codex" / "WATCH_PROMPT.md"
            prompt.parent.mkdir(parents=True)
            prompt.write_text("Inspect remote state only.\n", encoding="utf-8")
            with (
                mock.patch.object(three_body_loop, "_current_branch", return_value="rh_clean"),
                mock.patch.object(three_body_loop, "_git_output", side_effect=[b"", b"2\n"]),
                mock.patch.object(
                    three_body_loop.subprocess,
                    "run",
                    return_value=subprocess.CompletedProcess([], 0),
                ) as resume,
            ):
                result = three_body_loop.run_read_only_watch(
                    repo_root=root,
                    branch="rh_clean",
                    session_id=SESSION_ID,
                    prompt_path="docs/Codex/WATCH_PROMPT.md",
                    codex_bin="/opt/codex",
                    lock_path=root / "watch.lock",
                )
            command = resume.call_args.args[0]
            resume_index = command.index("resume")
            self.assertEqual(command[0], "/opt/codex")
            self.assertEqual(command[resume_index + 1], SESSION_ID)
            self.assertEqual(command[command.index("--sandbox") + 1], "read-only")
            self.assertLess(command.index("-C"), resume_index)
            self.assertEqual(result["result"], "READ_ONLY_WAKE_COMPLETE")
            self.assertEqual(result["remote_ahead"], 2)
            self.assertIs(resume.call_args.kwargs["stdin"], subprocess.DEVNULL)

    def test_watch_prompt_never_fast_forwards_the_worktree(self) -> None:
        prompt = (three_body_loop.REPO_ROOT / "docs" / "Codex" / "WATCH_PROMPT.md").read_text(
            encoding="utf-8"
        )
        self.assertNotIn("git pull --ff-only", prompt)
        self.assertIn("git show origin/rh_clean:<path>", prompt)

    def test_launch_cli_routes_branch_pin_to_launcher(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            resume_command = ["codex", "exec", "resume", SESSION_ID]
            with (
                mock.patch.object(three_body_loop, "REPO_ROOT", root),
                mock.patch.object(
                    three_body_loop,
                    "build_codex_resume_command",
                    return_value=resume_command,
                ) as build,
                mock.patch.object(
                    three_body_loop,
                    "launch_pinned_session",
                    return_value={"result": "DUPLICATE_TRIGGER_NOOP"},
                ) as launch,
            ):
                result = three_body_loop.main(
                    [
                        "launch",
                        "--state",
                        str(root / "state.json"),
                        "--lock",
                        str(root / "writer.lock"),
                        "--run-id",
                        "RUN_CLI_PLANT",
                        "--trigger-nonce",
                        "NONCE_CLI_PLANT",
                        "--source-event-commit",
                        "a" * 40,
                        "--answer-blob",
                        "b" * 64,
                        "--session-id",
                        SESSION_ID,
                        "--branch",
                        "rh_clean",
                        "--task-path",
                        "docs/Codex/TASK_PLANT.md",
                        "--task-blob",
                        "c" * 40,
                        "--phase-key-hash",
                        "d" * 64,
                        "--base-head",
                        "e" * 40,
                        "--output-schema",
                        str(root / "schema.json"),
                        "--final-reply",
                        str(root / "reply.json"),
                        "--prompt",
                        "pinned follow-up",
                    ]
                )

            self.assertEqual(result, 0)
            self.assertNotIn("branch", build.call_args.kwargs)
            self.assertEqual(launch.call_args.kwargs["branch"], "rh_clean")
            self.assertEqual(launch.call_args.kwargs["command"], resume_command)

    def test_DUPLICATE_TRIGGER(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture = self._launch_fixture(root)
            counter = root / "launch_count.txt"
            command = [
                sys.executable,
                "-c",
                (
                    "from pathlib import Path; "
                    "p=Path('launch_count.txt'); "
                    "p.write_text((p.read_text() if p.exists() else '')+'1\\n')"
                ),
                SESSION_ID,
            ]
            first = three_body_loop.launch_pinned_session(**fixture, command=command)
            second = three_body_loop.launch_pinned_session(**fixture, command=command)
            deadline = time.monotonic() + 3
            while not counter.exists() and time.monotonic() < deadline:
                time.sleep(0.02)
            first["process"].wait(timeout=3)
            self.assertEqual(second["result"], "DUPLICATE_TRIGGER_NOOP")
            self.assertEqual(counter.read_text(encoding="utf-8"), "1\n")

    def test_duplicate_trigger_rechecks_ledger_after_lock(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture = self._launch_fixture(root)
            empty = _empty_state()
            existing = _empty_state()
            existing_event = {
                **fixture["event"],
                "status": "FAILED_BEFORE_LAUNCH",
                "child_identity": None,
                "failure": "prior delivery",
            }
            existing["event_ledger"].append(existing_event)
            command = [sys.executable, "-c", "raise SystemExit(99)", SESSION_ID]

            with mock.patch.object(
                three_body_loop,
                "validate_repository_gate",
                side_effect=[empty, existing],
            ):
                result = three_body_loop.launch_pinned_session(**fixture, command=command)

            self.assertEqual(result["result"], "DUPLICATE_TRIGGER_NOOP")
            self.assertEqual(result["event"], existing_event)

    def test_DROP_CLAIM_RACE(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state_path = root / "CODEX_REQ_STATE_PLANT.yaml"
            raw = three_body_loop._canonical_yaml_bytes(_request_state())
            state_path.write_bytes(raw)
            expected = hashlib.sha256(raw).hexdigest()
            lock_path = root / "request.lock"
            queue: mp.Queue = mp.Queue()
            workers = [
                mp.Process(
                    target=_cas_worker,
                    args=(str(state_path), str(lock_path), expected, target, queue),
                )
                for target in ("IN_REVIEW", "DROPPED")
            ]
            for worker in workers:
                worker.start()
            for worker in workers:
                worker.join(5)
                self.assertFalse(worker.is_alive())
            results = [queue.get(timeout=1) for _ in workers]
            self.assertEqual(sum(tag == "OK" for tag, _ in results), 1)
            self.assertEqual(
                sum(value == "CODEX_REQUEST_STATE_CAS_CONFLICT" for _, value in results),
                1,
            )

    def test_resolved_locally_after_claim_survives_answered_transition(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state_path = root / "CODEX_REQ_STATE_PLANT.yaml"
            state = _request_state(status="IN_REVIEW")
            state["resolved_locally_after_claim"] = True
            raw = three_body_loop._canonical_yaml_bytes(state)
            state_path.write_bytes(raw)

            answered = three_body_loop.cas_transition_request_state(
                state_path,
                expected_state_sha256=hashlib.sha256(raw).hexdigest(),
                target_status="ANSWERED",
                lock_path=root / "request.lock",
            )

            self.assertEqual(answered["status"], "ANSWERED")
            self.assertTrue(answered["resolved_locally_after_claim"])

    def test_REQUEST_ID_BLOB_DRIFT(self) -> None:
        answer = {
            "ANSWER_SCHEMA_VERSION": "q3_codex_answer.v1",
            "ANSWERS_REQ": "REQ-PLANT-001",
            "REQUEST_BLOB": "0" * 64,
            "REQUEST_GIT_BLOB": "d" * 40,
            "REQUEST_SOURCE_COMMIT": "e" * 40,
            "PHASE_KEY_HASH": "a" * 64,
            "BLOCKER_FINGERPRINT": "b" * 64,
            "VERDICT_PATH": "docs/verdict.md",
            "VERDICT_BLOB": "f" * 40,
            "DECISION": "RUN_PLANT",
            "NEXT_NODE": "NONE",
            "FORBIDDEN": ["REQUEST_SUBSTITUTION"],
        }
        raw = ("# answer\n\n```yaml\n" + yaml.safe_dump(answer, sort_keys=False) + "```\n").encode(
            "utf-8"
        )
        self.assert_code(
            "CODEX_ANSWER_BINDING_INVALID",
            three_body_loop.validate_answer_binding,
            _request_bytes(),
            _request_state(status="IN_REVIEW"),
            raw,
            repo_root=Path("/tmp"),
        )

    def test_request_state_and_open_set_are_identity_closed(self) -> None:
        request, _payload = three_body_loop.parse_request_body(_request_bytes())
        state = _request_state(status="IN_REVIEW")
        drifted = dict(state, phase_key_hash="9" * 64)
        self.assert_code(
            "CODEX_REQUEST_STATE_INVALID",
            three_body_loop.validate_request_state_binding,
            request,
            drifted,
        )

        same_blocker = dict(
            state,
            request_id="REQ-PLANT-002",
            codex_session_id=LATEST_OTHER_SESSION,
        )
        self.assert_code(
            "CODEX_REQUEST_STATE_INVALID",
            three_body_loop.validate_request_open_set,
            [state, same_blocker],
        )
        same_session = dict(
            state,
            request_id="REQ-PLANT-003",
            blocker_fingerprint="8" * 64,
        )
        self.assert_code(
            "CODEX_REQUEST_STATE_INVALID",
            three_body_loop.validate_request_open_set,
            [state, same_session],
        )

    def test_repository_gate_binds_request_file_to_first_commit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _git_init(root)
            (root / "README").write_text("base\n", encoding="utf-8")
            source_commit = _git_commit(root, "source pin")
            request_raw = _request_bytes(source_commit=source_commit)
            request_path = root / "docs" / "routeB_bus" / "CODEX_REQ_PLANT.md"
            request_path.parent.mkdir(parents=True)
            request_path.write_bytes(request_raw)
            request_commit = _git_commit(root, "request body")
            request_state = _request_state(request_raw=request_raw)
            request_state["request_introducing_commit"] = request_commit
            state_path = request_path.with_name("CODEX_REQ_STATE_PLANT.yaml")
            state_path.write_bytes(three_body_loop._canonical_yaml_bytes(request_state))
            quarantine_path = _write_state(root)

            three_body_loop.validate_repository_gate(
                repo_root=root,
                state_path=quarantine_path,
            )

            request_path.write_bytes(request_raw + b"tamper\n")
            self.assert_code(
                "CODEX_REQUEST_STATE_INVALID",
                three_body_loop.validate_repository_gate,
                repo_root=root,
                state_path=quarantine_path,
            )

    def test_WRITER_LOCK_COLLISION(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            lock_path = Path(tmp) / "writer.lock"
            ready = mp.Event()
            release = mp.Event()
            holder = mp.Process(target=_writer_lock_worker, args=(str(lock_path), ready, release))
            holder.start()
            self.assertTrue(ready.wait(3))
            record = {
                "schema": "q3_writer_lock.v1",
                "worktree": str(lock_path.parent),
                "branch": "rh_clean",
                "writer_body": "CODEX",
                "pid": os.getpid(),
                "process_start_time": three_body_loop._process_start_time(os.getpid()),
                "boot_id": three_body_loop._boot_id(),
                "codex_session_id": SESSION_ID,
                "task_path": "docs/Codex/TASK_PLANT.md",
                "task_blob": "a" * 40,
                "phase_key_hash": "b" * 64,
                "base_head": "c" * 40,
                "run_id": "RUN_LOCK_CONTENDER",
                "trigger_nonce": "NONCE_LOCK_CONTENDER",
            }
            self.assert_code(
                "WRITER_LOCK_COLLISION",
                three_body_loop._acquire_writer_lock,
                lock_path,
                record,
            )
            release.set()
            holder.join(5)
            self.assertFalse(holder.is_alive())

    def test_OLDER_REQUEST_PRIORITY(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _git_init(root)
            (root / "README").write_text("base\n", encoding="utf-8")
            _git_commit(root, "base")
            _run(root, "git", "checkout", "-qb", "side-b")
            path_b = root / "docs" / "routeB_bus" / "CODEX_REQ_B.md"
            path_b.parent.mkdir(parents=True)
            path_b.write_text("B\n", encoding="utf-8")
            _git_commit(root, "side B")
            blob_b = _run(root, "git", "hash-object", str(path_b), capture=True).stdout.strip()
            _run(root, "git", "checkout", "-q", "rh_clean")
            _run(root, "git", "checkout", "-qb", "side-a")
            path_a = root / "docs" / "routeB_bus" / "CODEX_REQ_A.md"
            path_a.parent.mkdir(parents=True, exist_ok=True)
            path_a.write_text("A\n", encoding="utf-8")
            _git_commit(root, "side A")
            blob_a = _run(root, "git", "hash-object", str(path_a), capture=True).stdout.strip()
            _run(root, "git", "checkout", "-q", "rh_clean")
            _run(
                root,
                "git",
                "-c",
                "user.name=Three Body Plant",
                "-c",
                "user.email=three-body-plant@example.invalid",
                "merge",
                "-q",
                "--no-ff",
                "side-a",
                "side-b",
                "-m",
                "octopus arrival",
            )
            ordered = three_body_loop.first_parent_request_order(
                [
                    {
                        "path": "docs/routeB_bus/CODEX_REQ_B.md",
                        "request_id": "REQ-B",
                        "request_git_blob": blob_b,
                    },
                    {
                        "path": "docs/routeB_bus/CODEX_REQ_A.md",
                        "request_id": "REQ-A",
                        "request_git_blob": blob_a,
                    },
                ],
                repo_root=root,
            )
            self.assertEqual([row["request_id"] for row in ordered], ["REQ-A", "REQ-B"])

    def test_crash_after_spawn_before_parent_started_is_adopted(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture = self._launch_fixture(root)
            command = [
                sys.executable,
                "-c",
                "import time; time.sleep(1.5)",
                SESSION_ID,
            ]
            result = three_body_loop.launch_pinned_session(
                **fixture, command=command, crash_after_exec=True
            )
            observed = three_body_loop.recover_launch_state(
                state_path=fixture["state_path"],
                lock_path=fixture["lock_path"],
                marker_path=Path(result["marker"]),
                event=fixture["event"],
                repo_root=root,
            )
            duplicate = three_body_loop.launch_pinned_session(**fixture, command=command)
            self.assertEqual(observed, "STARTED_OBSERVED")
            self.assertEqual(duplicate["result"], "DUPLICATE_TRIGGER_NOOP")
            result["process"].wait(timeout=3)

    def test_completed_child_after_parent_crash_stays_started(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture = self._launch_fixture(root)
            command = [sys.executable, "-c", "pass", SESSION_ID]
            result = three_body_loop.launch_pinned_session(
                **fixture, command=command, crash_after_exec=True
            )
            result["process"].wait(timeout=3)

            observed = three_body_loop.recover_launch_state(
                state_path=fixture["state_path"],
                lock_path=fixture["lock_path"],
                marker_path=Path(result["marker"]),
                event=fixture["event"],
                repo_root=root,
            )
            state = three_body_loop.load_state(fixture["state_path"], repo_root=root)

            self.assertEqual(observed, "STARTED")
            self.assertEqual(state["event_ledger"][0]["status"], "STARTED")

    def test_hypothesis_provenance_permutation_and_duplicate_plants(self) -> None:
        rows = [
            {
                "hypothesis_id": token,
                "class": "SOURCE_FIELD",
                "source_or_supplier": f"source {token}",
                "exact_type": f"type {token}",
                "consumer": "consumer",
                "production_inhabitant_or_plant": {
                    "kind": "REACHABILITY_PLANT",
                    "path": "Q3/Plant.lean",
                    "blob": "a" * 40,
                    "declaration": f"plant_{token}",
                    "exact_type": f"type {token}",
                    "verifier": "LEAN_KERNEL",
                    "scope": "production",
                },
            }
            for token in ("HYP_B", "HYP_A")
        ]
        canonical_one, digest_one = three_body_loop.canonical_hypothesis_provenance(rows, opens=[])
        canonical_two, digest_two = three_body_loop.canonical_hypothesis_provenance(
            list(reversed(rows)), opens=[]
        )
        self.assertEqual(canonical_one, canonical_two)
        self.assertEqual(digest_one, digest_two)
        self.assert_code(
            "HYPOTHESIS_PROVENANCE_INVALID",
            three_body_loop.canonical_hypothesis_provenance,
            [rows[0], dict(rows[0])],
            opens=[],
        )
        non_nfc = dict(rows[0], source_or_supplier="e\u0301")
        self.assert_code(
            "HYPOTHESIS_PROVENANCE_INVALID",
            three_body_loop.canonical_hypothesis_provenance,
            [non_nfc],
            opens=[],
        )

    def test_tactical_repair_protected_surface_and_budget_plants(self) -> None:
        baseline = {
            "statement_sha256": "1" * 64,
            "hypotheses_sha256": "2" * 64,
            "imports_sha256": "3" * 64,
            "definitions_sha256": "4" * 64,
            "public_surface_sha256": "5" * 64,
            "source_object_sha256": "6" * 64,
            "consumer_sha256": "7" * 64,
            "proof_body_ranges": [[100, 200]],
        }
        changed = dict(baseline, hypotheses_sha256="8" * 64)
        self.assert_code(
            "TACTICAL_REPAIR_SURFACE_DRIFT",
            three_body_loop.validate_tactical_repair_candidate,
            baseline,
            changed,
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state_path = _write_state(root)
            lock = root / "repair.lock"
            kwargs = {
                "repair_id": "REPAIR_PLANT",
                "task_blob": "a" * 40,
                "source_commit": "b" * 40,
                "baseline": baseline,
                "lock_path": lock,
            }
            three_body_loop.record_tactical_repair_attempt(state_path, **kwargs)
            three_body_loop.record_tactical_repair_attempt(state_path, **kwargs)
            self.assert_code(
                "TACTICAL_REPAIR_BUDGET_EXHAUSTED",
                three_body_loop.record_tactical_repair_attempt,
                state_path,
                **kwargs,
            )

    def test_active_lease_cannot_cover_policy_ancestors(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture = self._launch_fixture(root)
            lease = {
                "schema": "q3_codex_autonomy_lease.v1",
                "grant_id": "LEASE_PLANT_001",
                "status": "ACTIVE",
                "control_version": 9,
                "branch": "rh_clean",
                "worktree": str(root.resolve()),
                "writer_lock_holder": "CODEX",
                "phase_key_hash": fixture["phase_key_hash"],
                "current_task_path": fixture["task_path"],
                "current_task_blob": fixture["task_blob"],
                "allowed_paths": ["orchestrator"],
                "activation_commit": fixture["base_head"],
                "expires_at": "2099-01-01T00:00:00Z",
                "node_budget": 1,
                "nodes_consumed": 0,
                "revoked": False,
            }
            state = _empty_state()
            state["active_lease"] = lease
            three_body_loop.validate_state(
                state,
                repo_root=root,
                autonomy_lease_resolver=lambda _grant_id: lease,
            )

            broad_lease = dict(lease, allowed_paths=["docs"])
            broad_state = dict(state, active_lease=broad_lease)
            self.assert_code(
                "CODEX_AUTONOMY_LEASE_INVALID",
                three_body_loop.validate_state,
                broad_state,
                repo_root=root,
                autonomy_lease_resolver=lambda _grant_id: broad_lease,
            )

    def test_control_state_and_manifest_mutations_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bad_control = root / "CODEX_CONTROL.md"
            bad_control.write_text(
                spine.CONTROL.read_text(encoding="utf-8").replace(
                    "CONTROL_VERSION: 9", "CONTROL_VERSION: 8"
                ),
                encoding="utf-8",
            )
            with mock.patch.object(spine, "CONTROL", bad_control):
                with self.assertRaisesRegex(spine.ControlViolation, "EXPLORATION_CONTOUR_ORPHANED"):
                    spine._validate_active_control()

            bad_state = _empty_state()
            del bad_state["active_lease"]
            self.assert_code(
                "SEMANTIC_QUARANTINE_STATE_INVALID",
                three_body_loop.validate_state,
                bad_state,
                repo_root=root,
            )

            manifest = yaml.safe_load(spine.TOOL_MANIFEST.read_text(encoding="utf-8"))
            manifest["tool_families"]["startup_and_control"]["tools"] = [
                row
                for row in manifest["tool_families"]["startup_and_control"]["tools"]
                if row["id"] != "three-body-loop"
            ]
            bad_manifest = root / "TOOLS.yaml"
            bad_manifest.write_text(
                yaml.safe_dump(manifest, allow_unicode=True, sort_keys=False),
                encoding="utf-8",
            )
            with mock.patch.object(spine, "TOOL_MANIFEST", bad_manifest):
                with self.assertRaisesRegex(spine.ControlViolation, "TOOL_MANIFEST_INVALID"):
                    spine.validate_tool_manifest()


class SemanticAdmissionPlants(ThreeBodyPlants):
    """Mandatory plants for CONTROL_V9_LINUX_ATTESTATION_BROKER_AND_ATOMIC_ADMIT.

    The admission path must fail closed on every route that would let a
    committing body mint, name or edit its own semantic attestation.
    """

    ATTEST = "ATTEST_PLANT_V1"

    def _green(self, root: Path) -> tuple[Path, dict[str, object]]:
        state_path, _commit = self._kernel_green_state(root)
        state = three_body_loop.load_state(state_path, repo_root=root)
        return state_path, state

    def _receipt_for(self, state: dict[str, object], attestation_id: str) -> dict[str, object]:
        entry = json.loads(json.dumps(state["entries"][0]))
        entry["semantic_attestation_id"] = attestation_id
        entry["admitted_scope"] = ["production"]
        return self._semantic_receipt(entry)

    def _admit(self, root: Path, state_path: Path, resolver, attestation_id=None):
        entry_id = json.loads(state_path.read_bytes())["entries"][0]["entry_id"]
        return three_body_loop.materialize_semantic_admission(
            entry_id=entry_id,
            attestation_id=attestation_id or self.ATTEST,
            state_path=state_path,
            lock_path=root / "writer.lock",
            repo_root=root,
            semantic_attestation_resolver=resolver,
        )

    def test_PLANT_DEFAULT_ADMISSION_RESOLVER_IS_LINUX_BROKER(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state_path, _state = self._green(root)
            entry_id = json.loads(state_path.read_bytes())["entries"][0]["entry_id"]
            with mock.patch.object(
                three_body_loop,
                "resolve_linux_semantic_attestation",
                return_value=None,
            ), mock.patch.object(
                three_body_loop,
                "resolve_semantic_attestation",
                side_effect=AssertionError("tracked receipt must not admit a new entry"),
            ):
                self.assert_code(
                    "SEMANTIC_ADMISSION_REFUSED",
                    three_body_loop.materialize_semantic_admission,
                    entry_id=entry_id,
                    attestation_id=self.ATTEST,
                    state_path=state_path,
                    lock_path=root / "writer.lock",
                    repo_root=root,
                )

    def test_EXACT_OWNER_WAIVER_ADMITS_ONLY_THE_PINNED_ENTRY(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state_path, _state = self._green(root)
            state = json.loads(state_path.read_bytes())
            state["entries"][0]["entry_id"] = three_body_loop.EXACT_OWNER_WAIVER_ENTRY_ID
            state_path.write_bytes(three_body_loop._canonical_state_bytes(state))
            loaded = three_body_loop.load_state(state_path, repo_root=root)
            receipt = self._receipt_for(
                loaded, three_body_loop.EXACT_OWNER_WAIVER_ATTESTATION_ID
            )
            receipt["issuer"] = three_body_loop.EXACT_OWNER_WAIVER_ISSUER
            with mock.patch.object(
                three_body_loop,
                "resolve_semantic_attestation",
                return_value=receipt,
            ):
                result = three_body_loop.materialize_semantic_admission(
                    entry_id=three_body_loop.EXACT_OWNER_WAIVER_ENTRY_ID,
                    attestation_id=three_body_loop.EXACT_OWNER_WAIVER_ATTESTATION_ID,
                    state_path=state_path,
                    lock_path=root / "writer.lock",
                    repo_root=root,
                )
            self.assertTrue(result["changed"])
            self.assertEqual(result["status"], "SEMANTICALLY_ADMITTED")

    def test_OWNER_WAIVER_ISSUER_REJECTS_ANY_OTHER_ENTRY(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state_path, state = self._green(root)
            forged = self._receipt_for(state, self.ATTEST)
            forged["issuer"] = three_body_loop.EXACT_OWNER_WAIVER_ISSUER
            self.assert_code(
                "SEMANTIC_ADMISSION_REFUSED",
                self._admit,
                root,
                state_path,
                lambda _id: forged,
            )

    def test_PLANT_BROKER_UNAVAILABLE_REJECTS_ADMISSION(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state_path, _state = self._green(root)
            self.assert_code(
                "SEMANTIC_ADMISSION_REFUSED",
                self._admit,
                root,
                state_path,
                lambda _id: None,
            )
            after = three_body_loop.load_state(state_path, repo_root=root)
            self.assertEqual(after["entries"][0]["status"], "KERNEL_GREEN")

    def test_PLANT_UNKNOWN_ATTESTATION_ID_REJECTS_ADMISSION(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state_path, state = self._green(root)
            known = self._receipt_for(state, self.ATTEST)
            resolver = lambda requested: known if requested == self.ATTEST else None
            self.assert_code(
                "SEMANTIC_ADMISSION_REFUSED",
                self._admit,
                root,
                state_path,
                resolver,
                "ATTEST_NEVER_ISSUED",
            )

    def test_PLANT_WRONG_ISSUER_REJECTS_ADMISSION(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state_path, state = self._green(root)
            forged = self._receipt_for(state, self.ATTEST)
            forged["issuer"] = "CODEX_EXECUTOR"
            self.assert_code(
                "SEMANTIC_ADMISSION_REFUSED",
                self._admit,
                root,
                state_path,
                lambda _id: forged,
            )

    def test_PLANT_RECEIPT_FIELD_DRIFT_REJECTS_ADMISSION(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state_path, state = self._green(root)
            drifted = self._receipt_for(state, self.ATTEST)
            drifted["source_commit"] = "0" * 40
            with self.assertRaises(three_body_loop.ThreeBodyViolation):
                self._admit(root, state_path, lambda _id: drifted)
            after = three_body_loop.load_state(state_path, repo_root=root)
            self.assertEqual(after["entries"][0]["status"], "KERNEL_GREEN")

    def test_PLANT_ARBITRARY_RECEIPT_PATH_IS_NOT_AN_INTERFACE(self) -> None:
        parser = three_body_loop._parser()
        for forbidden in ("--receipt-path", "--receipt-json", "--issuer", "--admitted-scope"):
            with self.assertRaises(SystemExit):
                parser.parse_args(
                    [
                        "semantic-admit",
                        "--entry-id",
                        "E",
                        "--attestation-id",
                        "A",
                        forbidden,
                        "value",
                    ]
                )

    def test_PLANT_INLINE_JSON_RECEIPT_IS_NOT_AN_INTERFACE(self) -> None:
        import inspect

        signature = inspect.signature(three_body_loop.materialize_semantic_admission)
        for forbidden in ("receipt", "receipt_path", "receipt_json", "issuer", "admitted_scope"):
            self.assertNotIn(forbidden, signature.parameters)
        broker_signature = inspect.signature(
            three_body_loop.resolve_linux_semantic_attestation
        )
        self.assertEqual(
            [name for name in broker_signature.parameters if name != "socket_path"],
            ["attestation_id"],
        )

    def test_PLANT_SOURCE_WRITTEN_CANNOT_BE_ADMITTED(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state_path, state = self._green(root)
            raw = json.loads(state_path.read_bytes())
            raw["entries"][0]["status"] = "SOURCE_WRITTEN"
            state_path.write_bytes(three_body_loop._canonical_state_bytes(raw))
            receipt = self._receipt_for(state, self.ATTEST)
            self.assert_code(
                "SEMANTIC_ADMISSION_REFUSED",
                self._admit,
                root,
                state_path,
                lambda _id: receipt,
            )

    def test_PLANT_SECOND_ATTESTATION_CANNOT_REPLACE_ADMITTED(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state_path, state = self._green(root)
            receipt = self._receipt_for(state, self.ATTEST)
            first = self._admit(root, state_path, lambda _id: receipt)
            self.assertTrue(first["changed"])
            replay = self._admit(root, state_path, lambda _id: receipt)
            self.assertFalse(replay["changed"])
            other = self._receipt_for(state, "ATTEST_OTHER_V1")
            self.assert_code(
                "SEMANTIC_ADMISSION_REFUSED",
                self._admit,
                root,
                state_path,
                lambda _id: other,
                "ATTEST_OTHER_V1",
            )

    def test_PLANT_KERNEL_GREEN_STILL_BLOCKS_DISPATCH(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._green(root)
            self.assert_code(
                "SEMANTIC_QUARANTINE_ACTIVE",
                three_body_loop.validate_repository_gate,
                repo_root=root,
                require_dispatch_clear=True,
                semantic_attestation_resolver=lambda _id: None,
            )

    def test_PLANT_ADMISSION_CLEARS_ONLY_THE_QUARANTINE_BARRIER(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state_path, state = self._green(root)
            before = json.loads(state_path.read_bytes())["entries"][0]
            receipt = self._receipt_for(state, self.ATTEST)
            self._admit(root, state_path, lambda _id: receipt)
            after = json.loads(state_path.read_bytes())["entries"][0]
            self.assertEqual(after["status"], "SEMANTICALLY_ADMITTED")
            self.assertEqual(after["admitted_scope"], ["production"])
            self.assertEqual(after["semantic_attestation_id"], self.ATTEST)
            mutable = {"status", "admitted_scope", "semantic_attestation_id"}
            for field in set(before) | set(after):
                if field in mutable:
                    continue
                self.assertEqual(before[field], after[field], f"{field} must be byte-identical")
            three_body_loop.validate_repository_gate(
                repo_root=root,
                require_dispatch_clear=True,
                semantic_attestation_resolver=lambda _id: receipt,
            )


if __name__ == "__main__":
    unittest.main()
