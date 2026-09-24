"""Focused v13 -> v14 activation tests; all Git publication is fixture-local."""
from __future__ import annotations

import base64
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock

from orchestrator import control14_activation as activation
from orchestrator import workflow_runtime as w


ROOT = Path(__file__).resolve().parents[2]
BASELINE_HEAD = "e11d64b77ac4848c0ad5f213c3276d47ef20c90c"
OWNER_INSTRUCTION = "naxuj???? piwem zanogo i wse !!!"
REVIEWER_IDS = ["native-astra-reviewer-one", "native-astra-reviewer-two"]
RETIRED_ASSIGNMENT_ID = "ASSIGNMENT_SELECTOR_PLAN2_LAUNCH_20260916"
RETIRED_ASSIGNMENT = {
    "command": "agent-launch", "evidence": [], "id": RETIRED_ASSIGNMENT_ID,
    "inputs": {
        "orchestrator/team_records.py": "2dfae6880df1e83b7722a9542cae4a6ff51c02d3f28f047255159c386f362a3a",
        "orchestrator/tests/test_workflow_runtime.py": "7e3e2ffcff6ee77e3444955ec114492b4d74a57fdf4af467e6ab69efea82ca8a",
    },
    "kind": "ASSIGN", "state": "UNKNOWN",
    "subject": {
        "id": "ASSIGNMENT_SELECTOR_PLAN2_20260916", "kind": "ASSIGNMENT",
        "sha256": "cdfe7cad598604bff0354eee2d131f0375607e6bd74c8d2ea037606516bafa19",
    },
}


def git(repo: Path, *args: str, check: bool = True) -> str:
    result = subprocess.run(["git", *args], cwd=repo, capture_output=True, text=True,
                            check=False, timeout=45)
    if check and result.returncode:
        raise AssertionError(result.stderr)
    return result.stdout.strip()


class Control14ActivationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="q3-control14-activation-test-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.remote = self.root / "origin.git"
        from orchestrator.tests.test_workflow_runtime import TeamRuntimeTests

        self.fixture = TeamRuntimeTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.target = self.fixture.repo
        original_document = self.fixture.document
        marker = ("Retired assignment (outcome UNKNOWN): "
                  + json.dumps(RETIRED_ASSIGNMENT, ensure_ascii=False, sort_keys=True)
                  + "\n").encode("utf-8")

        def document_with_retired_assignment(*args, **kwargs):
            return original_document(*args, **kwargs) + marker

        self.fixture.document = document_with_retired_assignment
        private_local = Path(git(self.target, "rev-parse", "--git-common-dir"))
        if not private_local.is_absolute():
            private_local = (self.target / private_local).resolve()
        private_local /= w.TEAM_LOCAL
        local = w._team_local(self.target)
        private_local.write_bytes(w._team_json(local))
        private_local.chmod(0o600)
        git(self.target, "checkout", "-qb", "rh_clean")
        base_head = BASELINE_HEAD
        for relative in activation.SOURCE_PATHS:
            if relative in activation.ADDED_PATHS:
                continue
            dst = self.target / relative
            dst.parent.mkdir(parents=True, exist_ok=True)
            result = subprocess.run(["git", "show", f"{base_head}:{relative}"], cwd=ROOT,
                                    capture_output=True, check=True, timeout=45)
            dst.write_bytes(result.stdout)
        control = self.target / activation.CONTROL_PATH
        control.write_text(control.read_text().replace("CONTROL_VERSION: 10", "CONTROL_VERSION: 13"))

        data = self.fixture.data()
        map_sha = "a" * 64
        data["operation"].update(
            kind="PUBLISH", state="INTENT", id="TEST_OLD_COMPACT_PUBLICATION",
            subject={"kind": "REPAIR", "id": "TEST_OLD_COMPACT_PUBLICATION", "sha256": map_sha},
            command="publication", inputs={"docs/session_protocols/team-evidence-" + map_sha + ".bin": map_sha})
        self.fixture.install(data)
        git(self.target, "add", "-A")
        subprocess.run(["git", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                        "commit", "-qm", "TEST v13 FATAL preimage"], cwd=self.target,
                       check=True, timeout=45)
        self.base = git(self.target, "rev-parse", "HEAD")
        subprocess.run(["git", "clone", "--bare", "-q", str(self.target), str(self.remote)],
                       check=True, timeout=45)
        git(self.target, "remote", "add", "origin", str(self.remote))
        self.engine = self.root / "candidate"
        self._clone(self.target, self.engine)
        for relative in activation.SOURCE_PATHS:
            dst = self.engine / relative
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / relative, dst)
        git(self.engine, "add", "--", *activation.SOURCE_PATHS)
        git(self.engine, "-c", "user.name=Candidate Author", "-c",
            "user.email=candidate@example.invalid", "commit", "-qm", "TEST v14 candidate")
        self.candidate_commit = git(self.engine, "rev-parse", "HEAD")
        self.plan = mock.patch.object(w, "live_plan_v10", return_value={
            "status": "FATAL", "holds": [activation.FATAL], "startup": {"fatal_errors": []}})
        self.plan.start()
        self.addCleanup(self.plan.stop)

    def _clone(self, source: Path, destination: Path):
        subprocess.run(["git", "clone", "--shared", "--branch", "rh_clean", "-q",
                        str(source), str(destination)], check=True, timeout=45)
        git(destination, "remote", "remove", "origin")

    def _report(self, manifest: dict, reviewer_id: str, *, verdict="APPROVED",
                findings=None, dispositions=None, file_name=None) -> tuple[Path, bytes]:
        report = {
            "schema": activation.REVIEW_SCHEMA,
            "reviewer_id": reviewer_id,
            "manifest_sha256": activation._digest(activation._json(manifest)),
            "candidate_commit": manifest["candidate_engine"]["commit"],
            "files": [{"path": row["path"], "sha256": row["sha256"]}
                      for row in manifest["files"]],
            "checks": list(activation.REVIEW_CHECKS),
            "verdict": verdict,
            "findings": findings or [],
            "original_finding_dispositions": dispositions or [{
                "id": "prior-high-route-finding", "severity": "HIGH",
                "disposition": "FIXED", "reason": "The activation route now records intent before review."}],
        }
        # Keep noncanonical whitespace and the final newline to prove the
        # observer stores precisely the report bytes supplied by the owner.
        raw = (json.dumps(report, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
        path = self.root / (file_name or f"{reviewer_id}-report.json")
        path.write_bytes(raw)
        return path, raw

    def _prepare(self, candidate_commit: str | None = None) -> dict:
        return activation.prepare_review(
            self.target, candidate_commit=candidate_commit or self.candidate_commit,
            engine_root=self.engine, instruction=OWNER_INSTRUCTION.encode("utf-8"),
            reviewer_ids=REVIEWER_IDS)

    def _install_assignment_receipt(self, operation_id=RETIRED_ASSIGNMENT_ID) -> tuple[Path, bytes]:
        local = w._team_local(self.target)
        assignment = dict(RETIRED_ASSIGNMENT)
        assignment["id"] = operation_id
        binding_operation = {key: assignment[key]
                             for key in ("id", "kind", "subject", "command", "inputs")}
        receipt = {
            "schema": "q3_team_remote_observation.v1", "operation_id": operation_id,
            "state": "RESERVED", "installation_ref": local["installation_ref"],
            "actor": "previous-owner-task", "epoch": 0,
            "checkpoint_sha256": "a" * 64, "local_head": self.base,
            "remote_commit": self.base, "remote_resume_sha256": "b" * 64,
            "remote_ownership": {}, "remote_thread": "previous-owner-task", "evidence": {},
            "launch_binding": {"operation": binding_operation,
                                "assignment_sha256": assignment["subject"]["sha256"]},
        }
        local["operations"][operation_id] = receipt
        common = Path(git(self.target, "rev-parse", "--git-common-dir"))
        if not common.is_absolute():
            common = (self.target / common).resolve()
        path = common / w.TEAM_LOCAL
        path.write_bytes(w._team_json(local))
        path.chmod(0o600)
        return path, path.read_bytes()

    def _assert_changed_pins_block(self, change, expected_error):
        prepared = self._prepare()
        self._observe_clean_pair(prepared)
        change()
        before = git(self.target, "rev-parse", "HEAD")
        with self.assertRaisesRegex(w.WorkflowRuntimeError, expected_error):
            activation.activate(self.target, operation_id=prepared["operation_id"])
        self.assertEqual(git(self.target, "rev-parse", "HEAD"), before)
        self.assertEqual(activation._read_reservation(self.target)["state"], "REVIEW_CONFIRMED")
        with self.assertRaisesRegex(w.WorkflowRuntimeError, expected_error):
            activation._readback(self.target, prepared["manifest"], self.base)

    def _observe_clean_pair(self, prepared: dict) -> tuple[bytes, bytes]:
        first_raw = second_raw = b""
        for reviewer_id in REVIEWER_IDS:
            path, raw = self._report(prepared["manifest"], reviewer_id)
            result = activation.observe_review(
                self.target, operation_id=prepared["operation_id"], reviewer_id=reviewer_id,
                report_path=path, expected_report_sha256=hashlib.sha256(raw).hexdigest())
            if reviewer_id == REVIEWER_IDS[0]:
                self.assertEqual(result["status"], "REVIEW_PENDING")
                first_raw = raw
            else:
                self.assertEqual(result["status"], "REVIEW_CONFIRMED")
                second_raw = raw
        return first_raw, second_raw

    def test_prepare_manifest_binds_exact_six_sources_owner_and_local_private_state(self):
        manifest = activation.prepare_manifest(
            self.target, candidate_commit=self.candidate_commit, engine_root=self.engine)
        self.assertEqual(manifest["base_head"], self.base)
        self.assertEqual(manifest["remote"]["head"], self.base)
        self.assertEqual([row["path"] for row in manifest["files"]], list(activation.SOURCE_PATHS))
        added = [row for row in manifest["files"] if row["path"] in activation.ADDED_PATHS]
        self.assertEqual(len(added), len(activation.ADDED_PATHS))
        self.assertTrue(all(row["before_sha256"] is None and row["before_mode"] is None for row in added))
        self.assertEqual(manifest["owner"]["operation"]["state"], "INTENT")
        self.assertEqual(manifest["local"]["team_local_mode"], 0o600)
        self.assertRegex(manifest["local"]["team_local_sha256"], r"^[0-9a-f]{64}$")
        self.assertEqual(activation._control_version((self.target / activation.CONTROL_PATH).read_bytes()), 13)

    def test_lower_epoch_retired_assignment_receipt_is_pinned_without_being_resolved(self):
        path, before = self._install_assignment_receipt()
        manifest = activation.prepare_manifest(
            self.target, candidate_commit=self.candidate_commit, engine_root=self.engine)
        self.assertEqual(manifest["local"]["team_local_sha256"], hashlib.sha256(before).hexdigest())
        self.assertEqual(path.read_bytes(), before)
        saved = w._team_local(self.target)["operations"][RETIRED_ASSIGNMENT_ID]
        self.assertEqual((saved["state"], saved["epoch"]), ("RESERVED", 0))

    def test_unmarked_lower_epoch_reserved_assignment_still_blocks(self):
        self._install_assignment_receipt("UNMARKED_HISTORICAL_ASSIGNMENT")
        with self.assertRaisesRegex(w.WorkflowRuntimeError, "LOCAL_RESERVED_OR_UNKNOWN_EFFECT"):
            activation.prepare_manifest(
                self.target, candidate_commit=self.candidate_commit, engine_root=self.engine)

    def test_fetch_endpoint_change_blocks_activation_and_readback(self):
        def change():
            git(self.target, "remote", "set-url", "origin", str(self.root / "changed-fetch.git"))
            git(self.target, "remote", "set-url", "--push", "origin", str(self.remote))
        self._assert_changed_pins_block(change, "SINGLE_ORIGIN_ENDPOINT_REQUIRED|ORIGIN_ENDPOINT_CHANGED")

    def test_push_endpoint_change_blocks_activation_and_readback(self):
        def change():
            git(self.target, "remote", "set-url", "--push", "origin", str(self.root / "changed-push.git"))
        self._assert_changed_pins_block(change, "SINGLE_ORIGIN_ENDPOINT_REQUIRED|ORIGIN_ENDPOINT_CHANGED")

    def test_active_branch_change_blocks_activation_and_readback(self):
        def change():
            git(self.target, "checkout", "-qb", "other-branch")
        self._assert_changed_pins_block(change, "ACTIVE_BRANCH_CHANGED")

    def test_review_intent_precedes_launch_and_requires_two_distinct_clean_reports(self):
        prepared = self._prepare()
        self.assertTrue(prepared["launch_intent_recorded"])
        self.assertTrue(prepared["launches_permitted"])
        self.assertEqual(prepared["status"], "PREPARED_NOT_DISPATCHED")
        self.assertEqual(base64.b64decode(activation._read_reservation(self.target)["owner_instruction"]["raw_base64"]),
                         OWNER_INSTRUCTION.encode("utf-8"))
        again = self._prepare()
        self.assertFalse(again["launches_permitted"])
        with self.assertRaisesRegex(w.WorkflowRuntimeError, "TWO_CLEAN_NATIVE_REVIEW_PASSES_REQUIRED"):
            activation.activate(self.target, operation_id=prepared["operation_id"])

        report_a, raw_a = self._report(prepared["manifest"], REVIEWER_IDS[0])
        first = activation.observe_review(
            self.target, operation_id=prepared["operation_id"], reviewer_id=REVIEWER_IDS[0],
            report_path=report_a, expected_report_sha256=hashlib.sha256(raw_a).hexdigest())
        self.assertEqual(first["status"], "REVIEW_PENDING")
        reservation = activation._read_reservation(self.target)
        saved = reservation["review_observations"][0]
        self.assertEqual(saved["provenance"], "ROOT_OBSERVED_NATIVE_REVIEW")
        self.assertIs(saved["provider_verified"], False)
        self.assertEqual(base64.b64decode(saved["report_base64"]), raw_a)
        self.assertEqual(saved["requested_model"], "gpt-6-astra")
        self.assertEqual(saved["requested_effort"], "low")

        report_b, raw_b = self._report(prepared["manifest"], REVIEWER_IDS[1])
        second = activation.observe_review(
            self.target, operation_id=prepared["operation_id"], reviewer_id=REVIEWER_IDS[1],
            report_path=report_b, expected_report_sha256=hashlib.sha256(raw_b).hexdigest())
        self.assertEqual(second["status"], "REVIEW_CONFIRMED")
        self.assertEqual(len(activation._read_reservation(self.target)["review_observations"]), 2)

    def test_cli_keeps_exact_owner_instruction_and_emits_structured_json(self):
        output = io.StringIO()
        args = ["--root", str(self.target), "prepare-review",
                "--candidate-commit", self.candidate_commit,
                "--engine-root", str(self.engine),
                "--reviewer-id", REVIEWER_IDS[0], "--reviewer-id", REVIEWER_IDS[1],
                "--owner-instruction", OWNER_INSTRUCTION]
        with contextlib.redirect_stdout(output):
            status = activation.main(args)
        self.assertEqual(status, 0)
        payload = json.loads(output.getvalue())
        self.assertEqual(payload["schema"], activation.CLI_SCHEMA)
        self.assertEqual(payload["command"], "prepare-review")
        self.assertTrue(payload["launches_permitted"])
        saved = activation._read_reservation(self.target)["owner_instruction"]
        self.assertEqual(base64.b64decode(saved["raw_base64"]), OWNER_INSTRUCTION.encode("utf-8"))

    def test_negative_review_is_preserved_and_new_candidate_appends_immutable_history(self):
        prepared = self._prepare()
        path, raw = self._report(
            prepared["manifest"], REVIEWER_IDS[0], verdict="REJECTED",
            findings=[{"id": "new-high", "severity": "HIGH", "summary": "A real blocker."}])
        result = activation.observe_review(
            self.target, operation_id=prepared["operation_id"], reviewer_id=REVIEWER_IDS[0],
            report_path=path, expected_report_sha256=hashlib.sha256(raw).hexdigest())
        self.assertEqual(result["status"], "REJECTED")
        before = activation._read_reservation(self.target)
        self.assertEqual(base64.b64decode(before["review_observations"][0]["report_base64"]), raw)
        with self.assertRaisesRegex(w.WorkflowRuntimeError, "REJECTED_CANDIDATE_CANNOT_BE_REVIEWED_AGAIN"):
            self._prepare()

        candidate_source = self.engine / "orchestrator/startup_runtime.py"
        candidate_source.write_bytes(candidate_source.read_bytes() + b"\n# second reviewed candidate\n")
        git(self.engine, "add", "--", "orchestrator/startup_runtime.py")
        git(self.engine, "-c", "user.name=Candidate Author", "-c",
            "user.email=candidate@example.invalid", "commit", "-qm", "TEST second v14 candidate")
        second_commit = git(self.engine, "rev-parse", "HEAD")
        next_attempt = self._prepare(second_commit)
        after = activation._read_reservation(self.target)
        self.assertEqual(len(after["history"]), 1)
        old = after["history"][0]
        self.assertEqual(old["operation_id"], prepared["operation_id"])
        self.assertEqual(base64.b64decode(old["review_observations"][0]["report_base64"]), raw)
        self.assertNotEqual(next_attempt["manifest_sha256"], prepared["manifest_sha256"])

    def test_alternate_index_commit_recovers_crash_and_preserves_foreign_staging(self):
        foreign = self.target / "foreign-staged.txt"
        foreign.write_text("preserve my staged bytes\n")
        git(self.target, "add", "--", "foreign-staged.txt")
        prepared = self._prepare()
        self._observe_clean_pair(prepared)
        original_save = activation._save_reservation

        def crash_after_commit(repo, value):
            if value.get("candidate_commit"):
                raise RuntimeError("injected crash after commit before reservation readback")
            original_save(repo, value)

        with mock.patch.object(activation, "_save_reservation", side_effect=crash_after_commit):
            with self.assertRaisesRegex(RuntimeError, "after commit"):
                activation.activate(self.target, operation_id=prepared["operation_id"])
        committed = git(self.target, "rev-parse", "HEAD")
        self.assertNotEqual(committed, self.base)
        self.assertEqual(git(self.target, "diff-tree", "--no-commit-id", "--name-only",
                             "--no-renames", "-r", committed).splitlines(), list(activation.SOURCE_PATHS))
        self.assertEqual(git(self.target, "diff", "--cached", "--name-only"), "foreign-staged.txt")
        self.assertEqual((self.target / "foreign-staged.txt").read_text(), "preserve my staged bytes\n")

        recovered = activation.recover(self.target, operation_id=prepared["operation_id"])
        self.assertEqual(recovered["status"], "CONFIRMED")
        self.assertEqual(recovered["remote_commit"], committed)
        self.assertEqual(git(self.target, "ls-remote", "origin", activation.BRANCH).split()[0], committed)
        self.assertEqual(git(self.target, "diff", "--cached", "--name-only"), "foreign-staged.txt")
        self.assertEqual(w._team_remote_checkpoint(self.target)[1],
                         (self.target / str(w.RESUME_PATH)).read_bytes())

    def test_recovery_refuses_and_preserves_staged_owned_third_state(self):
        prepared = self._prepare()
        self._observe_clean_pair(prepared)
        original_save = activation._save_reservation

        def crash_after_commit(repo, value):
            if value.get("candidate_commit"):
                raise RuntimeError("injected crash after commit before reservation readback")
            original_save(repo, value)

        with mock.patch.object(activation, "_save_reservation", side_effect=crash_after_commit):
            with self.assertRaisesRegex(RuntimeError, "after commit"):
                activation.activate(self.target, operation_id=prepared["operation_id"])

        relative = "orchestrator/startup_runtime.py"
        path = self.target / relative
        candidate_bytes = path.read_bytes()
        path.write_bytes(candidate_bytes + b"\nthird-state staged after crash\n")
        git(self.target, "add", "--", relative)
        third_state = git(self.target, "ls-files", "--stage", "--", relative)
        path.write_bytes(candidate_bytes)
        with self.assertRaisesRegex(w.WorkflowRuntimeError, "OWNED_INDEX_STAGE_INVALID"):
            activation.recover(self.target, operation_id=prepared["operation_id"])
        self.assertEqual(git(self.target, "ls-files", "--stage", "--", relative), third_state)
        self.assertEqual(path.read_bytes(), candidate_bytes)
        self.assertEqual(git(self.target, "ls-remote", str(self.remote), activation.BRANCH).split()[0],
                         self.base)

    def test_manifest_rejects_unrelated_fatal_and_duplicate_reviewer_ids(self):
        with self.assertRaisesRegex(w.WorkflowRuntimeError, "TWO_DISTINCT_NATIVE_REVIEWERS_REQUIRED"):
            activation.prepare_review(self.target, candidate_commit=self.candidate_commit,
                                      engine_root=self.engine, instruction=OWNER_INSTRUCTION,
                                      reviewer_ids=[REVIEWER_IDS[0], REVIEWER_IDS[0]])
        with mock.patch.object(w, "live_plan_v10", return_value={
                "status": "FATAL", "holds": ["OTHER_FATAL"],
                "startup": {"fatal_errors": ["OTHER_FATAL"]}}):
            with self.assertRaisesRegex(w.WorkflowRuntimeError, "OTHER_FATAL_BLOCKED"):
                activation.prepare_manifest(self.target, candidate_commit=self.candidate_commit,
                                            engine_root=self.engine)
        self.assertIsNone(activation._read_reservation(self.target))


if __name__ == "__main__":
    unittest.main()
