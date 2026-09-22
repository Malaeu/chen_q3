"""Scoped Control12 -> 13 recovery and read-only review/delivery adapters.

Remote observations are explicit. No provider launch, commit or push is executed
by this module; those remain separately reserved native host operations.

Authorization to do the bounded work and review of exact bytes are distinct.
The active host records the ACTUAL owner instruction, not an invented approval
of a manifest. A non-author operational reviewer binds the exact manifest.
Instruction/reviewer provenance remains a host responsibility: neither JSON
nor Unix flock authenticates a human or manufactures a native repair review.
"""
from __future__ import annotations

import copy
import hashlib
import json
import os
from pathlib import Path
from typing import Any

SCHEMA = "q3_control13_recovery.v2"
SIGNOFF_SCHEMA = "q3_control13_owner_signoff.v1"  # optional, genuinely supplied legacy route
SCOPED_ACTIVATION_SCHEMA = "q3_control13_scoped_activation.v2"
INSTALLATION_SCHEMA = "q3_control13_installation.v3"
SELECTOR_TEST_PATH = "orchestrator/tests/test_workflow_runtime.py"
SELECTOR_TEST_BEFORE_SHA256 = "7a637b6b34985ae21bfe879c01b578b81c8ed2b7551ee55773322fe31281753f"
SCOPED_WORK = "CHECKPOINT_UNRESERVED_SELECTOR_REPAIR_RECOVERY"
REQUIRED_CHECKS = frozenset({
    "exact_preimages_and_engine", "never_reserved_named_implementation",
    "original_checkpoint_chain", "all_effect_and_foreign_fences",
    "limit_16384_and_mathematical_hold", "selector_regressions_retained",
    "rhc_and_publication_prefix_audited",
})
CANCEL_ID = "SELECTOR_DELIVERY_LAUNCH_20260922"
ASSIGNMENT_ID = "SELECTOR_REPAIR_DELIVERY_20260922"
BASE_HEAD = "00c7cbf4426234abafd35faecba183edc9ce29ce"
BASE_HASHES = {
    "docs/CODEX_CONTROL.md": "b77a0f8a78e96873e3139baebe8e86454f42a8628a69e52bb9712f22cbac1715",
    "docs/cartographer/TOOLS.yaml": "ff406e102a0b401fb1d64b000e3382939532123d050c6358dc6f862e4f07e8b9",
    "orchestrator/startup_runtime.py": "fa79aadd4739f503527ed974ef68f2dc24f1434c41775af7b0395038c856e13e",
    "orchestrator/team_records.py": "8fe0e907d11e78f1631008652352f5e9bc71c640e3245db5979b62f354a0df16",
    "orchestrator/workflow_runtime.py": "1a2912dcf0a10c6d6def0d9b1b9f993c416b77e6c54f72386a2fa404a762827d",
    "orchestrator/control13_recovery.py": "ABSENT",
    "orchestrator/tests/test_control13_recovery.py": "ABSENT",
    SELECTOR_TEST_PATH: SELECTOR_TEST_BEFORE_SHA256,
}
OBSERVATION_FIELDS = {
    "schema", "operation_id", "state", "installation_ref", "actor", "epoch",
    "checkpoint_sha256", "local_head", "remote_commit", "remote_resume_sha256",
    "remote_ownership", "remote_thread", "evidence",
}
MANIFEST_FIELDS = {
    "schema", "operation_id", "cancel_operation_id", "head", "owner", "author_id", "author_ids",
    "checkpoint_sha256", "history_sha256", "local_sha256", "assignments_sha256",
    "issues_sha256", "assignment_sha256", "index_sha256", "foreign_sha256",
    "engine_commit", "files",
}


def _w():
    from orchestrator import workflow_runtime
    return workflow_runtime


def fail(code: str) -> None:
    raise _w().WorkflowRuntimeError("CONTROL13_RECOVERY_" + code)


def digest(value: Any) -> str:
    return _w()._resume_digest(_w()._team_json(value))


def owner(data: dict) -> dict:
    return {"task": data["owner_thread_id"], "host": data["owner_host_id"],
            "installation_ref": data["ownership"]["installation_ref"],
            "epoch": data["ownership"]["epoch"]}


def _read_json(path: Path, expected: str | None) -> tuple[bytes, dict]:
    from orchestrator import team_records
    if path.is_symlink() or not path.is_file():
        fail("INPUT_NOT_REGULAR")
    raw = path.read_bytes()
    if expected is None or _w()._resume_digest(raw) != expected:
        fail("INPUT_HASH_MISMATCH")
    value = team_records.load_payload(raw)
    if _w()._team_json(value) != raw:
        fail("NONCANONICAL_JSON")
    return raw, value


def validate_manifest(m: dict) -> None:
    w = _w()
    if not isinstance(m, dict) or set(m) != MANIFEST_FIELDS or not isinstance(m.get("owner"), dict):
        fail("MANIFEST_IDENTITY")
    if (set(m) != MANIFEST_FIELDS or m["schema"] != SCHEMA
            or m["head"] != BASE_HEAD or m["cancel_operation_id"] != CANCEL_ID
            or m["operation_id"] != CANCEL_ID + ":control13"
            or m["author_id"] != "Proshka"
            or not isinstance(m["author_ids"], list)
            or any(not isinstance(x, str) or not x for x in m["author_ids"])
            or m["author_ids"] != sorted(set(m["author_ids"]))
            or not {"Proshka", m.get("owner", {}).get("task")}.issubset(m["author_ids"])
            or not w._team_hex(m["engine_commit"], 40)
            or not isinstance(m["owner"], dict)
            or set(m["owner"]) != {"task", "host", "installation_ref", "epoch"}
            or type(m["owner"]["epoch"]) is not int or m["owner"]["epoch"] != 2):
        fail("MANIFEST_IDENTITY")
    for key in MANIFEST_FIELDS:
        if key.endswith("_sha256") and not w._team_hex(m[key]):
            fail("MANIFEST_HASH")
    if (not isinstance(m["files"], list) or any(not isinstance(row, dict) for row in m["files"])
            or [row.get("path") for row in m["files"]] != sorted(BASE_HASHES)):
        fail("MANIFEST_EXACT_SCOPE")
    for r in m["files"]:
        if (set(r) != {"path", "before_sha256", "before_mode", "sha256", "mode"}
                or r["before_sha256"] != BASE_HASHES[r["path"]]
                or not w._team_hex(r["sha256"])
                or type(r["mode"]) is not int or r["mode"] not in {0o644, 0o755}
                or (r["before_mode"] is not None and (type(r["before_mode"]) is not int
                    or r["before_mode"] not in {0o644, 0o755}))
                or (r["before_sha256"] == "ABSENT") != (r["before_mode"] is None)):
            fail("MANIFEST_FILE")


def validate_signoff(a: dict, m: dict, expected: str | None) -> None:
    fields = {"schema", "approval_class", "reviewer_id", "author_id", "owner",
              "manifest_sha256", "instruction", "independent_acceptance",
              "mathematical_acceptance", "publication_authorized"}
    if (set(a) != fields or a["schema"] != SIGNOFF_SCHEMA
            or a["approval_class"] != "OWNER_SIGNOFF"
            or a["reviewer_id"] != "HUMAN_OWNER" or a["author_id"] != m["author_id"]
            or a["reviewer_id"] in {m["author_id"], m["owner"]["task"]}
            or a["owner"] != m["owner"] or a["manifest_sha256"] != digest(m)
            or not isinstance(a["instruction"], str) or not a["instruction"].strip()
            or len(a["instruction"].encode()) > 4096
            or any(a[k] is not False for k in ("independent_acceptance", "mathematical_acceptance", "publication_authorized"))
            or digest(a) != expected):
        fail("EXACT_OWNER_SIGNOFF_REQUIRED")



def combined_source_manifest(m: dict) -> dict[str, str]:
    """Eight final source bytes for review; NOT an installation or push grant."""
    validate_manifest(m)
    return {row["path"]: row["sha256"] for row in m["files"]}


def validate_activation_record(a: dict, m: dict, expected: str | None) -> None:
    """Typed alternative to exact human signoff, not a relabelled human receipt.

    The host must have observed the source instruction and the non-author review.
    These schema checks bind that observation; they cannot prove its provenance.
    No returned value satisfies native FIX_VERIFIED or any publication gate.
    """
    w = _w()
    if isinstance(a, dict) and a.get("schema") == SIGNOFF_SCHEMA:
        validate_signoff(a, m, expected)
        return
    fields = {"schema", "authority_basis", "owner", "grant", "operational_review",
              "mathematical_acceptance", "native_repair_acceptance", "publication_authorized"}
    if (not isinstance(a, dict) or set(a) != fields or a.get("schema") != SCOPED_ACTIVATION_SCHEMA
            or a["authority_basis"] != "EXISTING_SCOPED_OWNER_INSTRUCTION"
            or a["owner"] != m["owner"] or digest(a) != expected
            or any(a[k] is not False for k in
                   ("mathematical_acceptance", "native_repair_acceptance", "publication_authorized"))):
        fail("SCOPED_AUTHORIZATION_INVALID")
    grant = a["grant"]
    if (not isinstance(grant, dict) or set(grant) != {
            "recorded_by", "source_locator", "source_text", "source_sha256", "instruction",
            "scope", "cancel_operation_id", "plan_max_bytes", "exact_manifest_human_approved"}
            or grant["recorded_by"] != m["owner"]["task"]
            or grant["scope"] != SCOPED_WORK or grant["cancel_operation_id"] != CANCEL_ID
            or type(grant["plan_max_bytes"]) is not int or grant["plan_max_bytes"] != 16384
            or grant["exact_manifest_human_approved"] is not False):
        fail("SCOPED_GRANT_SCOPE_INVALID")
    for key, limit in (("instruction", 4096), ("source_text", 65536), ("source_locator", 2048)):
        if not isinstance(grant[key], str) or not grant[key].strip() or len(grant[key].encode()) > limit:
            fail("SCOPED_GRANT_SOURCE_INVALID")
    if (grant["instruction"] not in grant["source_text"]
            or w._resume_digest(grant["source_text"].encode()) != grant["source_sha256"]):
        fail("SCOPED_GRANT_SOURCE_INVALID")
    review = a["operational_review"]
    if (not isinstance(review, dict) or set(review) != {
            "class", "author_id", "author_ids", "reviewer_id", "manifest_sha256", "engine_commit",
            "dispatch_id", "native_evidence_sha256",
            "combined_source_manifest", "checks", "evidence", "verdict"}
            or review["class"] != "NONAUTHOR_OPERATIONAL_REVIEW"
            or review["author_id"] != m["author_id"]
            or review["author_ids"] != m["author_ids"]
            or not isinstance(review["reviewer_id"], str) or not review["reviewer_id"].strip()
            or review["reviewer_id"] in {*m["author_ids"], "HUMAN_OWNER"}
            or review["dispatch_id"] != review_operation_id(m)
            or not w._team_hex(review["native_evidence_sha256"])
            or review["manifest_sha256"] != digest(m) or review["engine_commit"] != m["engine_commit"]
            or review["combined_source_manifest"] != combined_source_manifest(m)
            or review["verdict"] != "ACTIVATION_CANDIDATE_APPROVED"
            or not isinstance(review["checks"], list)
            or any(not isinstance(x, str) for x in review["checks"])
            or review["checks"] != sorted(REQUIRED_CHECKS)
            or not isinstance(review["evidence"], list) or not review["evidence"]):
        fail("NONAUTHOR_OPERATIONAL_REVIEW_REQUIRED")
    locators = set()
    for row in review["evidence"]:
        if (not isinstance(row, dict) or set(row) != {"locator", "sha256"}
                or not isinstance(row["locator"], str) or not row["locator"].strip()
                or len(row["locator"].encode()) > 2048 or row["locator"] in locators
                or not w._team_hex(row["sha256"])):
            fail("OPERATIONAL_REVIEW_EVIDENCE_INVALID")
        locators.add(row["locator"])


def _selector_regression_check(repo: Path, m: dict) -> None:
    """Bind changed test bytes via the same before/after CAS as all eight files.

    The immutable selector regression class must remain structurally identical;
    the separately reviewed v10/v13 fixture edits outside it are permitted.
    """
    import ast
    w = _w()
    row = next(r for r in m["files"] if r["path"] == SELECTOR_TEST_PATH)
    body, mode = w._team_integration_blob(Path(w.REPO), m["engine_commit"], SELECTOR_TEST_PATH)
    if body is None or w._resume_digest(body) != row["sha256"] or mode != row["mode"]:
        fail("SELECTOR_REGRESSION_NOT_AT_ENGINE")
    classes = [n for n in ast.parse(body).body if isinstance(n, ast.ClassDef) and n.name == "TeamRecordsTests"]
    if len(classes) != 1 or hashlib.sha256(ast.dump(classes[0], include_attributes=False).encode()).hexdigest() != '091c548b612d242116ffeaab22dc1c475ff4b21a093a9239a2eeaa9fa3f45aad':
        fail("SELECTOR_TESTS_REMOVED_OR_CHANGED")
    # Destination third-state detection and replay are handled by _preimages,
    # which admits exactly the named old OR named final bytes on recovery.


def _index_hash(repo: Path) -> str:
    w = _w()
    path = Path(w._team_git(repo, "rev-parse", "--git-path", "index").decode().strip())
    if not path.is_absolute():
        path = repo / path
    if path.is_symlink() or not path.is_file():
        fail("INDEX_UNAVAILABLE")
    return w._resume_digest(path.read_bytes())


def _file(repo: Path, path: str) -> dict:
    w = _w()
    raw = w._resume_file(repo, Path(path))
    return {"sha256": w._resume_digest(raw),
            "mode": None if raw is None else (0o755 if (repo / path).stat().st_mode & 0o111 else 0o644)}


def _foreign_hash(repo: Path) -> str:
    """Hash actual dirty foreign bytes as well as statuses; do not stage anything."""
    w = _w()
    rows = w._team_git(repo, "--no-optional-locks", "status", "--porcelain=v1", "-z", "--untracked-files=all").split(b"\0")
    found = []
    i = 0
    while i < len(rows) and rows[i]:
        row = rows[i].decode("utf-8"); i += 1
        status, path = row[:2], row[3:]
        names = [path]
        if "R" in status or "C" in status:
            if i >= len(rows) or not rows[i]:
                fail("STATUS_TRUNCATED")
            names.append(rows[i].decode("utf-8")); i += 1
            if any(p in BASE_HASHES for p in names):
                fail("OWNED_RENAME_FORBIDDEN")
        for p in names:
            if p not in BASE_HASHES:
                found.append({"path": p, "status": status, **_file(repo, p)})
    return digest(found)


def _history_origin(repo: Path, raw: bytes, data: dict, observation: dict) -> str:
    """No fresh observation, gap skipping or reconstruction from later notes."""
    w = _w()
    history = w._resume_history(w._resume_file(repo, w.RESUME_HISTORY_PATH) or b"")
    versions = {n: b for kind, n, b in history.values() if kind in {"resume", "intent"}}
    start = [(n, b) for n, b in versions.items() if w._resume_digest(b) == observation["checkpoint_sha256"]]
    if len(start) != 1:
        fail("OBSERVATION_ORIGIN_MISSING:" + observation["checkpoint_sha256"])
    n, previous = start[0]
    origin, _ = w._resume_document(previous)
    mutable = {"revision", "observed_at", "previous_sha256"}
    machine = {k: v for k, v in origin.items() if k not in mutable}
    if n > data["revision"]:
        fail("HISTORY_ORDER")
    for revision in range(n + 1, data["revision"] + 1):
        value = versions.get(revision)
        if value is None:
            fail("HISTORY_FRAME_MISSING:" + str(revision))
        next_data, _ = w._resume_document(value)
        if (next_data["previous_sha256"] != w._resume_digest(previous)
                or {k: v for k, v in next_data.items() if k not in mutable} != machine):
            fail("HISTORY_MACHINE_DRIFT")
        previous = value
    if previous != raw:
        fail("HISTORY_CURRENT_DRIFT")
    return observation["checkpoint_sha256"]


def prove_unreserved(repo: Path, raw: bytes, data: dict, local: dict, assignment: dict) -> dict:
    from orchestrator import team_records
    w = _w(); op = data["operation"]; obs = local["operations"].get(CANCEL_ID)
    if (op["id"] != CANCEL_ID or op["kind"] != "ASSIGN" or op["command"] != "agent-launch"
            or op["state"] != "INTENT" or op["evidence"]
            or not isinstance(obs, dict) or set(obs) != OBSERVATION_FIELDS
            or obs["schema"] != "q3_team_remote_observation.v1" or obs["state"] != "OBSERVED"
            or obs["operation_id"] != CANCEL_ID or obs["evidence"] != {}):
        fail("NEVER_RESERVED_OBSERVATION_REQUIRED")
    for key in ("checkpoint_sha256", "remote_resume_sha256", "installation_ref"):
        if not w._team_hex(obs[key]): fail("OBSERVATION_HASH")
    if (obs["actor"] != data["owner_thread_id"] or obs["epoch"] != data["ownership"]["epoch"]
            or obs["installation_ref"] != data["ownership"]["installation_ref"]
            or obs["remote_ownership"] != data["ownership"]
            or obs["remote_thread"] != data["owner_thread_id"] or obs["local_head"] != BASE_HEAD
            or not w._team_hex(obs["remote_commit"], 40)):
        fail("OBSERVATION_BINDING")
    assignment = team_records._validate_assignment(assignment)
    context = team_records.TrustedTeamContext(data["owner_thread_id"], data["owner_host_id"],
        data["ownership"]["installation_ref"], data["ownership"]["epoch"], data["owner_thread_id"], {})
    team_records._validate_assignment_owner(assignment, context)
    if (assignment["assignment_id"] != ASSIGNMENT_ID or assignment["role"] != "implementation"
            or assignment["status"] != "ASSIGNED" or assignment["resolved_model"] is not None
            or op["subject"] != {"kind": "ASSIGNMENT", "id": ASSIGNMENT_ID,
                                  "sha256": team_records._assignment_binding_sha(assignment)}):
        fail("ORIGINAL_IMPLEMENTATION_BINDING")
    for item in local["operations"].values():
        if not isinstance(item, dict): fail("CORRUPT_OPERATION")
        if item.get("state") in {"RESERVED", "UNKNOWN"}: fail("OUTSTANDING_EFFECT")
        if item.get("state") not in {"OBSERVED", "CONFIRMED", "NOT_EXECUTED"}: fail("UNCLASSIFIED_OPERATION_STATE")
        observed = item.get("observation", {}); binding = item.get("launch_binding", {})
        if not isinstance(observed, dict) or not isinstance(binding, dict): fail("CORRUPT_OPERATION")
        bound_op = binding.get("operation", {})
        if not isinstance(bound_op, dict): fail("CORRUPT_OPERATION")
        bound_subject = bound_op.get("subject", {})
        if not isinstance(bound_subject, dict): fail("CORRUPT_OPERATION")
        if (observed.get("assignment_id") == ASSIGNMENT_ID or bound_op.get("id") == CANCEL_ID
                or bound_subject.get("id") == ASSIGNMENT_ID):
            fail("NATIVE_OR_LAUNCH_BINDING_PRESENT")
    origin = _history_origin(repo, raw, data, obs)
    return {"schema": "q3_unreserved_launch_proof.v1", "operation": copy.deepcopy(op),
            "assignment_sha256": team_records._assignment_binding_sha(assignment),
            "observation": copy.deepcopy(obs), "origin_sha256": origin,
            "scope": "CURRENT_INSTALLATION_REGISTERED_EFFECTS_ONLY"}


def _preimages(repo: Path, m: dict, *, recovering: bool) -> dict:
    w = _w(); source = Path(w.REPO)
    files = {}
    for row in m["files"]:
        after, mode = w._team_integration_blob(source, m["engine_commit"], row["path"])
        if after is None or w._resume_digest(after) != row["sha256"] or mode != row["mode"]:
            fail("CANDIDATE_BLOB:" + row["path"])
        now = _file(repo, row["path"])
        before = {"sha256": row["before_sha256"], "mode": row["before_mode"]}
        target = {"sha256": row["sha256"], "mode": row["mode"]}
        if now != before and not (recovering and now == target):
            fail("DESTINATION_THIRD_STATE:" + row["path"])
        files[row["path"]] = after
    return files


def _static_snapshot(repo: Path, raw: bytes, data: dict, local: dict) -> dict:
    w = _w()
    return {"checkpoint_sha256": w._resume_digest(raw),
            "history_sha256": w._resume_digest(w._resume_file(repo, w.RESUME_HISTORY_PATH)),
            "local_sha256": digest(local),
            "assignments_sha256": w._resume_digest(w._resume_file(repo, w.TEAM_ASSIGNMENTS)),
            "issues_sha256": w._resume_digest(w._resume_file(repo, w.TEAM_ISSUES)),
            "index_sha256": _index_hash(repo), "foreign_sha256": _foreign_hash(repo),
            "head": w._team_git(repo, "rev-parse", "HEAD").decode().strip(), "owner": owner(data)}


def prepare_manifest(repo: Path, *, extra_authors: tuple[str, ...] = ()) -> dict:
    """Read-only proposal. Does not produce OWNER_SIGNOFF or reserve anything."""
    w = _w()
    from orchestrator import team_records
    with w._execution_writer_epoch(repo):
        raw, data, _ = w._team_current(repo); w._team_actor(repo, data)
        if w._team_private_read(repo, w.TEAM_LOCAL) is None: fail("PRIVATE_STATE_MISSING")
        local = w._team_local(repo); engine = w._team_integration_engine(repo)
        assignment = w._team_assignments(repo)["assignments"][ASSIGNMENT_ID]["assignment"]
        prove_unreserved(repo, raw, data, local, assignment)
        files = []
        for path, before_hash in sorted(BASE_HASHES.items()):
            before = _file(repo, path)
            if before["sha256"] != before_hash: fail("BASE_SOURCE_DRIFT:" + path)
            content, mode = w._team_integration_blob(Path(engine["root"]), engine["commit"], path)
            if content is None: fail("ENGINE_FILE_MISSING:" + path)
            files.append({"path": path, "before_sha256": before_hash, "before_mode": before["mode"],
                          "sha256": w._resume_digest(content), "mode": mode})
        m = {"schema": SCHEMA, "operation_id": CANCEL_ID + ":control13", "cancel_operation_id": CANCEL_ID,
             "author_id": "Proshka", "author_ids": sorted({"Proshka", data["owner_thread_id"], *extra_authors}),
             "engine_commit": engine["commit"], "files": files,
             "assignment_sha256": team_records._assignment_binding_sha(assignment),
             **_static_snapshot(repo, raw, data, local)}
        validate_manifest(m)
        return m


def _saved_check(saved: dict, operation_id: str) -> dict:
    w = _w(); m = saved.get("manifest", {})
    validate_manifest(m)
    if (m["operation_id"] != operation_id or saved.get("manifest_sha256") != digest(m)
            or saved.get("schema") != INSTALLATION_SCHEMA
            or set(saved) != {"schema", "state", "manifest", "manifest_sha256", "engine", "activation_record",
                             "activation_record_sha256", "proof"}
            or saved["state"] not in {"PENDING", "COMPLETE"}):
        fail("SAVED_RECORD_INVALID")
    validate_activation_record(saved["activation_record"], m, saved["activation_record_sha256"])
    return m


def _same_engine(saved: dict, current: dict) -> bool:
    """Module import order is not source drift; every saved/current byte stays at C."""
    w = _w()
    fields = {"root", "commit", "source_sha256", "python", "pyyaml"}
    if (not isinstance(saved, dict) or set(saved) != fields or set(current) != fields
            or any(saved[k] != current[k] for k in fields - {"source_sha256"})):
        return False
    w._team_path_hashes(saved["source_sha256"])
    for path, sha in saved["source_sha256"].items():
        body, _ = w._team_integration_blob(Path(current["root"]), current["commit"], path)
        if w._resume_digest(body) != sha or w._resume_file(Path(current["root"]), Path(path)) != body:
            return False
    return True  # _team_integration_engine already checked EVERY currently imported module.


def recovery_plan(repo: Path, operation_id: str, saved: dict) -> dict:
    m = _saved_check(saved, operation_id)
    return {"schema": "q3_workflow_plan.v3", "mode": "PRODUCTION_V10", "status": "HOLD",
            "holds": ["CONTROL13_RECOVERY_PENDING", "NODE_REGISTRY_EXACT_EDGE_REQUIRED"],
            "selected_goal": _w()._team_current(repo)[1]["pins"]["physical_goal"],
            "run_authorized": False, "writes_performed": False, "PX_RH_CLAIM": "NOT_MADE",
            "continuation": {"status": "RECOVERY_ONLY", "owner": m["owner"],
                "recovery": {"engine": {"root": saved["engine"]["root"], "commit": saved["engine"]["commit"],
                                      "saved_metadata_sha256": digest(saved["engine"])},
                             "command": "team-recover-unreserved",
                             "recover_operation": operation_id, "manifest_sha256": digest(m)},
                "cancel_operation_id": CANCEL_ID, "outcome": "NOT_YET_RECONCILED"}}


def reject_recovered_launch(repo: Path, operation_id: str) -> None:
    if operation_id != CANCEL_ID: return
    w = _w(); local = w._team_private_read(repo, w.TEAM_LOCAL)
    if local is not None:
        row = local.get("operations", {}).get(CANCEL_ID, {})
        if isinstance(row, dict) and row.get("control13_recovery"):
            fail("TERMINAL_LAUNCH_CANNOT_REPLAY")
    from orchestrator.startup_runtime import validate_battle_v10_control
    if validate_battle_v10_control(repo).version >= 13:
        fail("TERMINAL_LAUNCH_CANNOT_REPLAY")
    # Cross-installation/after receipt archival, a confirmed checkpoint also tombstones ID.
    history = w._resume_file(repo, w.RESUME_HISTORY_PATH)
    if history:
        for kind, _, raw in w._resume_history(history).values():
            if kind in {"resume", "intent"}:
                d, _ = w._resume_document(raw)
                if d["operation"]["id"] == CANCEL_ID and d["operation"]["state"] == "CONFIRMED":
                    fail("TERMINAL_LAUNCH_CANNOT_REPLAY")


def recover_unreserved(repo: Path, *, candidate: Path | None = None, recover_operation: str | None = None,
                      expected_sha256: str | None = None, owner_signoff: Path | None = None,
                      approved_signoff_sha256: str | None = None, execute: bool = False,
                      activation_record: Path | None = None,
                      expected_activation_sha256: str | None = None) -> dict:
    """Durable closed-scope installation + NOT_EXECUTED; never a native effect.

    The distinct PENDING record is deliberately recognizable by the OLD all-
    writer integration fence. Normal integration refuses its different schema.
    """
    w = _w()
    from orchestrator.startup_runtime import validate_battle_v10_control
    from orchestrator import team_records  # preload the same strict parser on fresh-process recovery
    if (candidate is None) == (recover_operation is None): fail("CANDIDATE_OR_RECOVERY_REQUIRED")
    if owner_signoff is not None and activation_record is not None: fail("AUTHORIZATION_ROUTES_CONFLICT")
    if (activation_record is None) != (expected_activation_sha256 is None): fail("SCOPED_AUTHORIZATION_INPUT_REQUIRED")
    if candidate is not None:
        _, m = _read_json(candidate, expected_sha256); validate_manifest(m)
        approval = None
        if owner_signoff is not None:
            _, approval = _read_json(owner_signoff, approved_signoff_sha256)
            validate_signoff(approval, m, approved_signoff_sha256)
        if activation_record is not None:
            _, approval = _read_json(activation_record, expected_activation_sha256)
            validate_activation_record(approval, m, expected_activation_sha256)
        if execute and approval is None:
            fail("SCOPED_REVIEW_OR_EXACT_OWNER_SIGNOFF_REQUIRED")
    else:
        local = w._team_private_read(repo, w.TEAM_LOCAL)
        saved = (local or {}).get("operations", {}).get(recover_operation, {}).get("integration", {})
        m = _saved_check(saved, recover_operation)
        approval = saved["activation_record"]
        if any(x is not None for x in (expected_sha256, owner_signoff, approved_signoff_sha256,
                                            activation_record, expected_activation_sha256)):
            fail("RECOVERY_ARGUMENT_SUBSTITUTION")
    operation_id = m["operation_id"]
    with w._execution_writer_epoch(repo, integration_operation=operation_id) as epoch:
        raw, data, _ = w._team_current(repo); w._team_actor(repo, data)
        if (owner(data) != m["owner"] or data["ownership"]["state"] != "ACTIVE"
                or data["ownership"]["transfer"] is not None or data["reconciliation_pending"]
                or os.environ.get("Q3_OWNER_EPOCH") != str(m["owner"]["epoch"])):
            fail("OWNER_OR_EPOCH")
        if w._team_private_read(repo, w.TEAM_LOCAL) is None: fail("PRIVATE_STATE_MISSING")
        local = w._team_local(repo)
        if local["epoch_floor"] > m["owner"]["epoch"]: fail("RETIRED_EPOCH")
        prior = local["operations"].get(operation_id)
        saved = prior.get("integration") if isinstance(prior, dict) else None
        if prior is not None and not isinstance(saved, dict): fail("OPERATION_ID_COLLISION")
        engine = w._team_integration_engine(repo)
        if engine["commit"] != m["engine_commit"]: fail("ENGINE_COMMIT_CHANGED")
        if saved is not None:
            _saved_check(saved, operation_id)
            if saved["manifest"] != m or not _same_engine(saved["engine"], engine) or saved["activation_record"] != approval:
                fail("SAVED_IDENTITY_CHANGED")
        elif recover_operation is not None: fail("ORIGINAL_RESERVATION_REQUIRED")
        # Recreate the exact pre-migration private snapshot, NEVER write it back.
        original_local = copy.deepcopy(local)
        original_local["operations"].pop(operation_id, None)
        if approval is not None and approval.get("schema") == SCOPED_ACTIVATION_SCHEMA:
            _check_completed_operational_review(repo, m, approval, local)
            original_local["operations"].pop(review_operation_id(m))
        if saved is not None and saved["state"] == "COMPLETE":
            terminal = original_local["operations"].get(CANCEL_ID, {})
            if (terminal.get("state") != "NOT_EXECUTED"
                    or terminal.get("control13_recovery") != operation_id): fail("TERMINAL_RECORD_CHANGED")
            original_local["operations"][CANCEL_ID] = saved["proof"]["observation"]
        snapshot = _static_snapshot(repo, raw, data, original_local)
        if any(m[k] != v for k, v in snapshot.items()): fail("PREIMAGE_CHANGED")
        assignment = w._team_assignments(repo)["assignments"].get(ASSIGNMENT_ID, {}).get("assignment")
        if not isinstance(assignment, dict): fail("ASSIGNMENT_MISSING")
        proof = prove_unreserved(repo, raw, data, original_local, assignment)
        if proof["assignment_sha256"] != m["assignment_sha256"]: fail("ASSIGNMENT_CHANGED")
        if saved is not None and saved["proof"] != proof: fail("PROOF_PREIMAGE_CHANGED")
        w._team_verify_paths(repo, data["source_manifest"])
        w._team_verify_paths(repo, data["operation"]["inputs"])
        if (set(data["source_manifest"]) | set(data["operation"]["inputs"])) & set(BASE_HASHES):
            fail("MATHEMATICAL_OR_OPERATION_INPUT_OVERWRITE")
        if approval is not None and approval.get("schema") == SCOPED_ACTIVATION_SCHEMA:
            _selector_regression_check(repo, m)
        files = _preimages(repo, m, recovering=saved is not None)
        if saved is not None and saved["state"] == "COMPLETE":
            if any(_file(repo, r["path"]) != {"sha256": r["sha256"], "mode": r["mode"]} for r in m["files"]):
                fail("COMPLETED_DESTINATION_DRIFT")
            return {"status": "NOOP", "operation_id": operation_id, "writes_performed": False,
                    "old_launch_outcome": "NOT_EXECUTED", "independent_acceptance": False}
        if saved is None:
            if validate_battle_v10_control(repo).version != 12: fail("OLD_CONTROL_12_REQUIRED")
            if validate_battle_v10_control(Path(engine["root"])).version != 13: fail("ENGINE_CONTROL_13_REQUIRED")
            w._team_writer_inventory(Path(engine["root"]))
        if not execute:
            return {"status": "DRY_RUN", "operation_id": operation_id, "manifest_sha256": digest(m),
                    "owner_signoff_present": approval is not None and approval.get("schema") == SIGNOFF_SCHEMA,
                    "scoped_activation_present": approval is not None and approval.get("schema") == SCOPED_ACTIVATION_SCHEMA,
                    "writes_performed": False,
                    "independent_acceptance": False, "mathematical_acceptance": False}
        if saved is None:
            validate_activation_record(approval, m, expected_activation_sha256 if activation_record is not None else approved_signoff_sha256)
            saved = {"schema": INSTALLATION_SCHEMA, "state": "PENDING", "manifest": m,
                     "manifest_sha256": digest(m), "engine": engine, "activation_record": approval,
                     "activation_record_sha256": digest(approval), "proof": proof}
            reservation = {"schema": "q3_control13_reservation.v1", "state": "RESERVED",
                           "actor": data["owner_thread_id"], "epoch": m["owner"]["epoch"],
                           "installation_ref": m["owner"]["installation_ref"], "integration": saved}
            after = {**local, "operations": {**local["operations"], operation_id: reservation}}
            w._team_local_save(repo, local, after, epoch); local = after
        # Import content-addressed objects from the pinned LOCAL engine only.
        # No network endpoint, FETCH_HEAD, tracking ref, branch, index or commit.
        try:
            w._team_git(repo, "cat-file", "-e", m["engine_commit"] + "^{commit}")
        except w.WorkflowRuntimeError:
            w._team_git(repo, "fetch", "--no-tags", "--no-write-fetch-head", "--no-auto-maintenance",
                        engine["root"], m["engine_commit"])
        w._team_git(repo, "cat-file", "-e", m["engine_commit"] + "^{commit}")
        # Old code fences us already. Install the imported module before its caller;
        # install the new control last. Every interruption stays fail-closed.
        sequence = ["orchestrator/control13_recovery.py", "orchestrator/startup_runtime.py",
                    "orchestrator/team_records.py", "orchestrator/tests/test_control13_recovery.py",
                    SELECTOR_TEST_PATH,
                    "docs/cartographer/TOOLS.yaml", "orchestrator/workflow_runtime.py", "docs/CODEX_CONTROL.md"]
        order = sorted(m["files"], key=lambda r: sequence.index(r["path"]))
        for r in order:
            current = w._resume_file(repo, Path(r["path"]))
            _preimages(repo, m, recovering=True)  # rejects a foreign third state before another write
            if current != files[r["path"]] or _file(repo, r["path"])["mode"] != r["mode"]:
                w._resume_cas_bytes(repo, Path(r["path"]), current, files[r["path"]], epoch, mode=r["mode"])
            w._resume_sync(repo / r["path"])
        if not _same_engine(engine, w._team_integration_engine(repo)): fail("ENGINE_DRIFT")
        if validate_battle_v10_control(repo).version != 13: fail("CONTROL_NOT_ACTIVATED")
        w._team_writer_inventory(repo)
        if any(m[k] != v for k, v in _static_snapshot(repo, raw, data, original_local).items()):
            fail("FINAL_PREIMAGE_CHANGED")
        if w._resume_file(repo, w.RESUME_PATH) != raw or w._team_local(repo) != local:
            fail("FINAL_CAS_CHANGED")
        for r in m["files"]:
            if _file(repo, r["path"]) != {"sha256": r["sha256"], "mode": r["mode"]}: fail("FINAL_FILE_CHANGED")
        observation = {"schema": "q3_team_effect_observation.v1", "operation_id": CANCEL_ID,
                       "outcome": "NOT_EXECUTED", "evidence": {"orchestrator/control13_recovery.py":
                           next(r["sha256"] for r in m["files"] if r["path"] == "orchestrator/control13_recovery.py")}}
        # Evidence here is a private typed manifest reference, not a fabricated provider receipt.
        dead = {**proof["observation"], "state": "NOT_EXECUTED", "evidence": observation,
                "control13_recovery": operation_id}
        completed = {**local["operations"][operation_id], "state": "CONFIRMED",
                     "integration": {**saved, "state": "COMPLETE"}}
        after = {**local, "operations": {**local["operations"], CANCEL_ID: dead, operation_id: completed}}
        w._team_local_save(repo, local, after, epoch)
        return {"status": "RECOVERED", "operation_id": operation_id, "old_launch_outcome": "NOT_EXECUTED",
                "files": [{"path": r["path"], "sha256": r["sha256"]} for r in m["files"]],
                "writes_performed": True, "checkpoint_written": False, "commit_push_performed": False,
                "independent_acceptance": False, "mathematical_acceptance": False, "PX_RH_CLAIM": "NOT_MADE"}


def completed_checkpoint_allowed(repo: Path, proposed: dict, plan: dict, integration_candidate: Path | None = None) -> bool:
    """Only exact known installation drift may pass the ordinary observation gate."""
    w = _w(); startup = plan.get("startup", {})
    if startup.get("control_version") != 13 or startup.get("fatal_errors_omitted", 0): return False
    fatal = set(startup.get("fatal_errors", []))
    if not fatal or set(plan.get("holds", [])) - fatal - {"NODE_REGISTRY_EXACT_EDGE_REQUIRED"}: return False
    local = w._team_private_read(repo, w.TEAM_LOCAL)
    if local is None: return False
    record = local.get("operations", {}).get(CANCEL_ID + ":control13", {})
    saved = record.get("integration", {})
    if record.get("state") != "CONFIRMED" or saved.get("state") != "COMPLETE": return False
    m = _saved_check(saved, CANCEL_ID + ":control13")
    _, current, _ = w._team_current(repo)
    if owner(current) != m["owner"] or w._team_git(repo, "rev-parse", "HEAD").decode().strip() != m["head"]: return False
    if not _same_engine(saved["engine"], w._team_integration_engine(repo)): return False
    for r in m["files"]:
        if _file(repo, r["path"]) != {"sha256": r["sha256"], "mode": r["mode"]}: return False
    for err in fatal:
        if err == "STARTUP_CONTROL_BLOB_DRIFT": continue
        if err.startswith("STARTUP_DECLARED_SURFACE_BLOB_DRIFT:"):
            if err.split(":", 1)[1] in BASE_HASHES: continue
        if err.startswith("STARTUP_RELEVANT_DIRTY_PATHS:"):
            if set(err.split(":", 1)[1].split(",")).issubset(BASE_HASHES): continue
        return False
    immutable = {"owner_thread_id", "owner_host_id", "ownership", "stages", "source_manifest",
                 "reconciliation_pending", "recovery_from"}
    if any(proposed[k] != current[k] for k in immutable): return False
    op = proposed["operation"]
    pins = dict(current["pins"])
    if op["command"] == "publication" and op["state"] == "INTENT":
        pins["head"] = m["head"]
    if proposed["pins"] != pins: return False
    same_operation = all(op[k] == current["operation"][k]
                         for k in ("id", "kind", "subject", "command", "inputs"))
    if op == current["operation"]: return True
    if (op["id"] == CANCEL_ID and same_operation and op["state"] == "CONFIRMED"):
        return (local["operations"].get(CANCEL_ID, {}).get("state") == "NOT_EXECUTED"
                and op["evidence"] == ["control13_recovery:" + m["operation_id"] + ":" + digest(m)])
    if not same_operation and current["operation"]["state"] not in {"CONFIRMED", "NONE"}: return False
    if op["command"] == "agent-launch":
        assignment = w._team_assignments(repo)["assignments"].get(op["subject"]["id"], {}).get("assignment", {})
        return ((assignment.get("role") == "independent-checker" and assignment.get("schema") == "q3_assignment.v2")
                or (assignment.get("schema") == "q3_assignment.v3" and assignment.get("role") in {"implementation", "independent-checker"}
                    and assignment.get("review_binding", {}).get("candidate_manifest") ==
                        [{"path": p, "sha256": h} for p,h in sorted(combined_source_manifest(m).items())]))
    if op["command"] == "workflow-team-integrate-candidate":
        if integration_candidate is not None:
            intake = w._team_integration_manifest(integration_candidate.read_bytes())
        else:
            intake = local["operations"].get(op["id"], {}).get("integration", {}).get("manifest", {})
        return intake.get("mode") == "EVIDENCE_INTAKE" and intake.get("operation_id") == op["id"]
    return op["command"] == "publication"


# One pre-activation, read-only native reviewer; a different transaction from
# the blocked implementation launch and from downstream repair acceptance.
REVIEW_SCHEMA = "q3_control13_operational_dispatch.v1"
REVIEW_RESULT_SCHEMA = "q3_control13_operational_review.v1"
REVIEW_ID_PREFIX = CANCEL_ID + ":operational-review:"


def review_operation_id(m: dict) -> str:
    return REVIEW_ID_PREFIX + digest(m)[:24]


def _validate_grant(grant: dict, m: dict) -> None:
    w = _w()
    required = {"recorded_by", "source_locator", "source_text", "source_sha256", "instruction",
                "scope", "cancel_operation_id", "plan_max_bytes", "exact_manifest_human_approved"}
    if (not isinstance(grant, dict) or set(grant) != required
            or grant["recorded_by"] != m["owner"]["task"] or grant["scope"] != SCOPED_WORK
            or grant["cancel_operation_id"] != CANCEL_ID or type(grant["plan_max_bytes"]) is not int
            or grant["plan_max_bytes"] != 16384 or grant["exact_manifest_human_approved"] is not False):
        fail("SCOPED_GRANT_SCOPE_INVALID")
    for key, limit in (("instruction", 4096), ("source_text", 65536), ("source_locator", 2048)):
        if not isinstance(grant[key], str) or not grant[key].strip() or len(grant[key].encode()) > limit:
            fail("SCOPED_GRANT_SOURCE_INVALID")
    if (grant["instruction"] not in grant["source_text"]
            or w._resume_digest(grant["source_text"].encode()) != grant["source_sha256"]):
        fail("SCOPED_GRANT_SOURCE_INVALID")


def _review_request(request: dict) -> dict:
    from orchestrator import team_records as tr
    if (not isinstance(request, dict) or set(request) != {"schema", "manifest", "grant", "assignment", "read_only"}
            or request["schema"] != REVIEW_SCHEMA or request["read_only"] is not True):
        fail("REVIEW_REQUEST_INVALID")
    m = request["manifest"]; validate_manifest(m); _validate_grant(request["grant"], m)
    a = tr._validate_assignment(request["assignment"])
    if (a["schema"] != tr.ASSIGNMENT_SCHEMA or a["role"] != "independent-checker"
            or a["assignee"] in {*m["author_ids"], "HUMAN_OWNER"}
            or a["assignment_id"] != review_operation_id(m)
            or a["subject"] != digest(m) or a["base_commit"] != m["engine_commit"]
            or a["owner_task"] != m["owner"]["task"] or a["owner_host"] != m["owner"]["host"]
            or a["owner_installation_ref"] != m["owner"]["installation_ref"]
            or a["owner_epoch"] != m["owner"]["epoch"]
            or a["operation"] != "CREATE" or a["status"] != "ASSIGNED"
            or a["resolved_model"] is not None or a["resolved_effort"] is not None
            or a["requested_model"] != "gpt-5.6-terra" or a["requested_effort"] != "medium"
            or a["input_hashes"] != [{"path": p, "sha256": h} for p,h in sorted(combined_source_manifest(m).items())]
            or a["permitted_paths"] != sorted(BASE_HASHES)
            or a["previous_assignment_sha256"] != "ABSENT" or a["previous_assignment_event_sha256"] != "ABSENT"):
        fail("REVIEW_NOT_DISTINCT_READONLY_EXACT_CANDIDATE")
    return m


def _review_preimages(repo: Path, m: dict, local: dict, *, remove_review: bool) -> dict:
    w = _w()
    raw, data, _ = w._team_current(repo); w._team_actor(repo, data)
    if (owner(data) != m["owner"] or data["ownership"]["state"] != "ACTIVE"
            or data["ownership"]["transfer"] is not None or data["reconciliation_pending"]
            or os.environ.get("Q3_OWNER_EPOCH") != str(m["owner"]["epoch"])
            or local["epoch_floor"] > m["owner"]["epoch"]):
        fail("OWNER_OR_EPOCH")
    original = copy.deepcopy(local)
    if remove_review: original["operations"].pop(review_operation_id(m), None)
    if any(m[k] != v for k,v in _static_snapshot(repo, raw, data, original).items()):
        fail("REVIEW_PREIMAGE_CHANGED")
    assignment = w._team_assignments(repo)["assignments"][ASSIGNMENT_ID]["assignment"]
    prove_unreserved(repo, raw, data, original, assignment)
    w._team_verify_paths(repo, data["source_manifest"])
    w._team_verify_paths(repo, data["operation"]["inputs"])
    _preimages(repo, m, recovering=False)
    _selector_regression_check(repo, m)
    if w._team_integration_engine(repo)["commit"] != m["engine_commit"]:
        fail("ENGINE_COMMIT_CHANGED")
    return data


def reserve_operational_review(repo: Path, *, candidate: Path, expected_sha256: str) -> dict:
    """Reserve ONLY a read-only native review. Never launch from this function.

    The explicit bounded owner instruction authorizes this pre-activation
    reservation. The old integration fence recognizes it without installing code.
    A retry after a lost response NEVER issues a second execution permit.
    """
    w = _w()
    from orchestrator.startup_runtime import validate_battle_v10_control
    _, request = _read_json(candidate, expected_sha256); m = _review_request(request)
    oid = review_operation_id(m)
    # Read/fetch remote objects outside the lock, just as team-observe-remote.
    # No tracking refs or checkpoint modifications and no paid call occur here.
    prior = w._team_private_read(repo, w.TEAM_LOCAL)
    if prior is None: fail("PRIVATE_STATE_MISSING")
    existing = prior["operations"].get(oid)
    if existing is not None:
        if existing.get("integration", {}).get("request") != request: fail("REVIEW_ID_COLLISION")
        return {"status": "RECONCILE_ORIGINAL", "operation_id": oid, "execute_once": False}
    remote_commit, remote_raw, remote = w._team_remote(repo)
    with w._execution_writer_epoch(repo) as epoch:
        local = w._team_local(repo)
        if oid in local["operations"]: fail("REVIEW_ID_COLLISION")
        data = _review_preimages(repo, m, local, remove_review=False)
        if (validate_battle_v10_control(repo).version != 12
                or remote["ownership"] != data["ownership"] or remote["owner_thread_id"] != data["owner_thread_id"]):
            fail("REVIEW_REMOTE_OWNER_OR_CONTROL_CHANGED")
        engine = w._team_integration_engine(repo)
        w._team_writer_inventory(Path(engine["root"]))
        saved = {"schema": REVIEW_SCHEMA, "state": "PENDING", "manifest": m,
                 "manifest_sha256": digest(m), "request": request, "engine": engine,
                 "remote_commit": remote_commit, "remote_resume_sha256": w._resume_digest(remote_raw),
                 "origin_sha256": w._team_bootstrap_endpoint(repo),
                 "native": [], "artifacts": {}, "outcome": None, "launch_attempted": False}
        record = {"schema": REVIEW_SCHEMA, "state": "RESERVED", "actor": data["owner_thread_id"],
                  "epoch": m["owner"]["epoch"], "installation_ref": m["owner"]["installation_ref"], "integration": saved}
        w._team_local_save(repo, local, {**local, "operations": {**local["operations"], oid: record}}, epoch)
    return {"status": "RESERVED", "operation_id": oid, "execute_once": False,
            "next": "team-recovery-review launch-permit",
            "native_request": {"assignment": request["assignment"], "engine_commit": m["engine_commit"],
                               "manifest_sha256": digest(m), "sandbox": "read-only", "descendants": 0},
            "old_launch_changed": False, "native_launch_performed": False,
            "FIX_VERIFIED": False, "PX_RH_CLAIM": "NOT_MADE"}


def _review_artifacts(saved: dict) -> dict[str, bytes]:
    import base64
    from orchestrator import team_records as tr
    artifacts = {}
    for locator, encoded in saved["artifacts"].items():
        tr._locator(locator, "operational evidence")
        try: artifacts[locator] = base64.b64decode(encoded, validate=True)
        except (ValueError, TypeError): fail("REVIEW_ARTIFACT_ENCODING")
    for o in saved["native"]:
        tr._validate_native_observation(saved["request"]["assignment"], o, phase=o["phase"])
        for prefix in ("output", "provider_receipt"):
            if _w()._resume_digest(artifacts.get(o[prefix + "_locator"])) != o[prefix + "_sha256"]:
                fail("REVIEW_ARTIFACT_HASH_CHANGED")
    return artifacts


def _review_result(saved: dict) -> dict:
    from orchestrator import team_records as tr
    m = _review_request(saved["request"])
    if saved["manifest"] != m or saved["manifest_sha256"] != digest(m): fail("REVIEW_SAVED_BINDING")
    if saved.get("launch_attempted") is not True: fail("REVIEW_LAUNCH_PERMIT_REQUIRED")
    a = saved["request"]["assignment"]; artifacts = _review_artifacts(saved)
    context = tr.TrustedTeamContext(m["owner"]["task"], m["owner"]["host"], m["owner"]["installation_ref"],
                                   m["owner"]["epoch"], m["owner"]["task"], {a["assignment_id"]: saved["native"]}, artifacts)
    launch, result = tr._validated_assignment_observation(a, context)
    if (result["state"] != "COMPLETED" or launch["operation_id"] != a["assignment_id"] + ":launch"
            or result["operation_id"] != a["assignment_id"] + ":result"
            or launch["native_agent_id"] in {*m["author_ids"], "HUMAN_OWNER"}):
        fail("REAL_DISTINCT_OPERATIONAL_REVIEW_REQUIRED")
    out = tr.load_payload(artifacts[result["output_locator"]])
    expected = {"schema": REVIEW_RESULT_SCHEMA, "reviewer_id": a["assignee"], "author_ids": m["author_ids"],
                "manifest_sha256": digest(m), "engine_commit": m["engine_commit"],
                "combined_source_manifest": combined_source_manifest(m), "read_only": True,
                "checks": sorted(REQUIRED_CHECKS), "verdict": out.get("verdict")}
    if out != expected or out["verdict"] not in {"ACTIVATION_CANDIDATE_APPROVED", "ACTIVATION_CANDIDATE_REJECTED"}:
        fail("REVIEW_OUTPUT_NOT_EXACT")
    return out


def operational_activation(saved: dict) -> dict:
    """Serialize checked nonauthor evidence, never a human signature or native FIX."""
    m = saved["manifest"]; out = _review_result(saved)
    if saved["state"] != "COMPLETE" or out["verdict"] != "ACTIVATION_CANDIDATE_APPROVED":
        fail("POSITIVE_OPERATIONAL_REVIEW_REQUIRED")
    native_hash = digest({"native": saved["native"], "artifacts": saved["artifacts"]})
    return {"schema": SCOPED_ACTIVATION_SCHEMA, "authority_basis": "EXISTING_SCOPED_OWNER_INSTRUCTION",
            "owner": m["owner"], "grant": saved["request"]["grant"],
            "operational_review": {"class": "NONAUTHOR_OPERATIONAL_REVIEW", "author_id": m["author_id"],
                 "author_ids": m["author_ids"], "reviewer_id": out["reviewer_id"],
                 "dispatch_id": review_operation_id(m), "native_evidence_sha256": native_hash,
                 "manifest_sha256": digest(m), "engine_commit": m["engine_commit"],
                 "combined_source_manifest": combined_source_manifest(m), "checks": sorted(REQUIRED_CHECKS),
                 "evidence": [{"locator": "private-operational-review:" + review_operation_id(m), "sha256": native_hash}],
                 "verdict": "ACTIVATION_CANDIDATE_APPROVED"},
            "mathematical_acceptance": False, "native_repair_acceptance": False, "publication_authorized": False}


def observe_operational_review(repo: Path, *, operation_id: str, candidate: Path, expected_sha256: str) -> dict:
    """Ingest ACTUAL host-observed provider bytes. Fixtures are only used in tests."""
    import base64
    w = _w()
    from orchestrator import team_records as tr
    _, bundle = _read_json(candidate, expected_sha256)
    if set(bundle) != {"observation", "artifacts"} or not isinstance(bundle["artifacts"], dict): fail("REVIEW_EVIDENCE_SCHEMA")
    with w._execution_writer_epoch(repo, integration_operation=operation_id) as epoch:
        local = w._team_local(repo); record = local["operations"].get(operation_id, {})
        saved = copy.deepcopy(record.get("integration", {}))
        if saved.get("schema") != REVIEW_SCHEMA or operation_id != review_operation_id(saved.get("manifest", {})):
            fail("REVIEW_RESERVATION_REQUIRED")
        m = _review_request(saved["request"])
        if saved.get("launch_attempted") is not True: fail("REVIEW_LAUNCH_PERMIT_REQUIRED")
        _review_preimages(repo, m, local, remove_review=True)
        if not _same_engine(saved["engine"], w._team_integration_engine(repo)): fail("ENGINE_COMMIT_CHANGED")
        if saved.get("origin_sha256") != w._team_bootstrap_endpoint(repo): fail("REVIEW_ENDPOINT_CHANGED")
        o = tr._validate_native_observation(saved["request"]["assignment"], bundle["observation"], phase=bundle["observation"].get("phase"))
        if o["phase"] not in {"LAUNCH", "RESULT"}: fail("REVIEW_PHASE_INVALID")
        if o["operation_id"] != operation_id + ":" + o["phase"].lower(): fail("REVIEW_PHASE_ID")
        expected_locators = {o[p + "_locator"] for p in ("output", "provider_receipt")}
        if set(bundle["artifacts"]) != expected_locators: fail("REVIEW_EVIDENCE_SCOPE")
        for locator, encoded in bundle["artifacts"].items():
            try: value = base64.b64decode(encoded, validate=True)
            except (ValueError, TypeError): fail("REVIEW_ARTIFACT_ENCODING")
            if locator in saved["artifacts"] and saved["artifacts"][locator] != encoded: fail("REVIEW_ARTIFACT_CONFLICT")
            for p in ("output", "provider_receipt"):
                if locator == o[p + "_locator"] and w._resume_digest(value) != o[p + "_sha256"]:
                    fail("REVIEW_ARTIFACT_HASH_CHANGED")
        same = [x for x in saved["native"] if x["phase"] == o["phase"]]
        if same:
            if same != [o] or any(saved["artifacts"].get(k) != v for k,v in bundle["artifacts"].items()): fail("REVIEW_CONFLICTING_REPLAY")
            out = {"status": "NOOP", "execute_once": False, "native_launch_performed": False}
            if saved["state"] == "COMPLETE" and saved["outcome"] == "ACTIVATION_CANDIDATE_APPROVED":
                out["activation_record"] = operational_activation(saved)
            return out
        if saved["state"] != "PENDING" or (o["phase"] == "RESULT" and len(saved["native"]) != 1): fail("REVIEW_ORDER")
        saved["native"].append(o); saved["artifacts"].update(bundle["artifacts"])
        _review_artifacts(saved)
        if o["phase"] == "RESULT":
            result = _review_result(saved)
            saved.update(state="COMPLETE", outcome=result["verdict"])
        updated = {**record, "state": "CONFIRMED" if saved["state"] == "COMPLETE" else "RESERVED", "integration": saved}
        w._team_local_save(repo, local, {**local, "operations": {**local["operations"], operation_id: updated}}, epoch)
        out = {"status": "REVIEW_COMPLETE" if saved["state"] == "COMPLETE" else "LAUNCH_OBSERVED",
               "execute_once": False, "old_launch_changed": False, "FIX_VERIFIED": False}
        if saved["state"] == "COMPLETE" and saved["outcome"] == "ACTIVATION_CANDIDATE_APPROVED":
            out["activation_record"] = operational_activation(saved)
        return out


def _check_completed_operational_review(repo: Path, m: dict, approval: dict, local: dict) -> None:
    row = local["operations"].get(review_operation_id(m), {})
    saved = row.get("integration", {})
    if (row.get("schema") != REVIEW_SCHEMA or row.get("state") != "CONFIRMED"
            or row.get("actor") != m["owner"]["task"] or row.get("epoch") != m["owner"]["epoch"]
            or row.get("installation_ref") != m["owner"]["installation_ref"]
            or saved.get("manifest") != m or saved.get("state") != "COMPLETE"
            or operational_activation(saved) != approval):
        fail("CHECKED_NATIVE_OPERATIONAL_REVIEW_REQUIRED")
    if not _same_engine(saved["engine"], _w()._team_integration_engine(repo)): fail("ENGINE_COMMIT_CHANGED")
    if saved.get("origin_sha256") != _w()._team_bootstrap_endpoint(repo): fail("REVIEW_ENDPOINT_CHANGED")


def operational_review_plan(repo: Path, oid: str, saved: dict) -> dict:
    m = _review_request(saved["request"])
    if oid != review_operation_id(m): fail("REVIEW_SAVED_BINDING")
    return {"schema": "q3_workflow_plan.v3", "mode": "PRODUCTION_V10", "status": "HOLD",
            "holds": ["CONTROL13_OPERATIONAL_REVIEW_PENDING", "NODE_REGISTRY_EXACT_EDGE_REQUIRED"],
            "run_authorized": False, "writes_performed": False, "PX_RH_CLAIM": "NOT_MADE",
            "selected_goal": _w()._team_current(repo)[1]["pins"]["physical_goal"],
            "continuation": {"owner": m["owner"], "operation_id": oid,
                "manifest_sha256": digest(m), "native_phases": [x["phase"] for x in saved["native"]],
                "recovery": {"command": "team-recovery-review observe", "engine_commit": m["engine_commit"],
                             "no_relaunch": True, "old_launch": CANCEL_ID}}}

# The exact committed historical set in the controlling request. Not an
# expandable wildcard, not owned worktree writes, and not mathematical admission.
HISTORICAL_REMOTE = "82bd8329be545b18597119cb1da7eefb12b87cb3"
HISTORY_PATHS = (
    "docs/Codex/GOAL_HISTORY.md",
    "docs/Codex/REPORT_2026-09-22_FOKAS_RMINUS_CROSSWALK.md",
    "docs/Codex/RESUME.md",
    "docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_ZINGER_NEEDLE_2026-09-21.txt",
    "docs/session_protocols/HMODE_QUASIMODE_REVIEW_PLAN_20260922.json",
    "docs/session_protocols/PROSHKA_REQUEST_HMODE_QUASIMODE_20260922.txt",
    "docs/session_protocols/ferrers_endpoint_flux_candidate_20260922.lean",
    "docs/session_protocols/ferrers_endpoint_flux_candidate_20260922_check.txt",
    "docs/session_protocols/ferrers_form_approx_candidate_20260922.lean",
    "docs/session_protocols/ferrers_form_approx_candidate_20260922_check.txt",
    "docs/session_protocols/fokas_euler_rational_check_20260922.py",
    "docs/session_protocols/fourier_overlap_candidate_20260922.lean",
    "docs/session_protocols/fourier_overlap_candidate_20260922_check.txt",
    "docs/session_protocols/quasimode_correction_candidate_20260922.lean",
    "docs/session_protocols/quasimode_correction_candidate_20260922_check.txt",
    "docs/session_protocols/quasimode_first_correction_20260922.py",
    "docs/session_protocols/selector_repair_62ebafa8.bundle",
    "docs/session_protocols/selector_repair_candidate_20260922.patch",
    "docs/session_protocols/selector_repair_checks_20260922.txt",
    "docs/session_protocols/selector_repair_plan_20260922.md",
    "docs/session_protocols/selector_repair_test_runner_20260922.py",
    "docs/session_protocols/selector_reproduce_20260922.log",
    "docs/session_protocols/selector_reproduce_20260922.py",
)
PREFIX_SCHEMA = "q3_control13_immutable_delivery_prefix.v1"


def delivery_prefix_manifest(repo: Path, *, remote_base: str, head: str) -> dict:
    """Read exact O..H Git objects; no network observation or publication grant."""
    w = _w()
    if head != BASE_HEAD or remote_base != HISTORICAL_REMOTE:
        fail("DELIVERY_BASE_NOT_NAMED")
    w._team_git(repo, "merge-base", "--is-ancestor", remote_base, head)
    paths = set(w._team_git(repo, "diff", "--name-only", "--no-renames", "-z", remote_base, head, "--").decode().split("\0")[:-1])
    if paths != set(HISTORY_PATHS) or paths.intersection(BASE_HASHES):
        fail("HISTORICAL_EXACT_23_PATHS_REQUIRED")
    commits = []
    # A historical add-and-delete of an undeclared file is still publication.
    # Check every traversed edge, not only the two endpoint trees.
    lines = w._team_git(repo, "rev-list", "--reverse", "--topo-order", "--parents", remote_base + ".." + head).decode().splitlines()
    for line in lines:
        bits = line.split(); commit, parents = bits[0], bits[1:]
        if not parents: fail("HISTORICAL_ROOT_INSERTION")
        for parent in parents:
            touched = set(w._team_git(repo, "diff", "--name-only", "--no-renames", "-z", parent, commit, "--").decode().split("\0")[:-1])
            if not touched.issubset(paths): fail("HISTORICAL_TRANSIENT_OUTSIDE_SCOPE")
        commits.append({"commit": commit, "parents": parents})
    if not commits or len(commits) > 256: fail("HISTORICAL_COMMIT_BOUND")
    files = {}
    for path in sorted(paths):
        raw, mode = w._team_integration_blob(repo, head, path)
        old, old_mode = w._team_integration_blob(repo, remote_base, path)
        if (raw is None or mode not in {0o644,0o755}
                or old is not None and old_mode not in {0o644,0o755}):
            fail("HISTORICAL_REGULAR_BLOBS_REQUIRED")
        files[path] = {"sha256": w._resume_digest(raw), "mode": mode,
                       "remote_sha256": w._resume_digest(old), "remote_mode": old_mode}
    return {"schema": PREFIX_SCHEMA, "remote_base": remote_base, "base_head": head,
            "commits": commits, "files": files, "interpretation": "UNCHANGED_COMMITTED_EVIDENCE_NOT_PROOF"}


def validate_delivery_prefix(repo: Path, prefix: dict) -> None:
    from orchestrator import team_records as tr
    tr._validate_delivery_prefix_shape(prefix)
    if prefix != delivery_prefix_manifest(repo, remote_base=prefix["remote_base"], head=prefix["base_head"]):
        fail("HISTORICAL_PREFIX_CHANGED")


def validate_combined_assignment(repo: Path, assignment: dict) -> None:
    """R inputs, H execution, C8 fixed candidate, immutable O..H carried evidence."""
    w = _w(); binding = assignment["review_binding"]
    if (assignment["base_commit"] != BASE_HEAD or binding["delivery_prefix"]["base_head"] != BASE_HEAD
            or set(x["path"] for x in binding["candidate_manifest"]) != set(BASE_HASHES)
            or {x["path"] for x in assignment["input_hashes"]} != {"orchestrator/team_records.py", SELECTOR_TEST_PATH}
            or not {"Proshka", assignment["owner_task"]}.issubset(binding["author_ids"])):
        fail("COMBINED_ASSIGNMENT_SCOPE")
    validate_delivery_prefix(repo, binding["delivery_prefix"])
    w._team_validate_repair_candidate(repo, binding, base_commit=binding["report_base_commit"])
    parents = w._team_git(repo, "show", "-s", "--format=%P", binding["candidate_commit"]).decode().split()
    if parents != [assignment["base_commit"]]: fail("COMBINED_CANDIDATE_PARENT")


def reviewed_delivery_prefix(repo: Path, data: dict, inputs: dict[str,str]) -> dict | None:
    """Only the ACTUAL native FIX_VERIFIED result supplies the prefix permission.

    This is not a second acceptance primitive. Reuse the existing framed issue,
    assignment and exact native artifacts, including frozen R source inputs.
    """
    from orchestrator import team_records as tr
    w = _w()
    registry = tr.read_registry(w._resume_file(repo, w.TEAM_ISSUES), "issues",
                               archive_loader=lambda p: w._resume_file(repo,Path(p)))
    for issue in registry["issues"].values():
        if data["operation"]["id"] != str(issue.get("repair_subject_id")) + ":publication": continue
        if issue["state"] not in {"FIX_VERIFIED","FIX_COMMITTED"}: fail("NATIVE_FIX_VERIFIED_REQUIRED")
        events = [e["payload"] for e in registry["events"] if e["issue_id"] == issue["issue_id"]
                  and e["payload"].get("transition") == "FIX_VERIFIED"]
        if len(events) != 1: fail("UNIQUE_NATIVE_FIX_VERIFIED_REQUIRED")
        event = events[0]; assignments = w._team_assignments(repo)
        ids = [k for k,row in assignments["assignments"].items() if row["assignment"]["assignee"] == event["actor_id"]
               and row["assignment"]["subject"] in {issue["repair_subject_id"],issue["issue_id"]}]
        context = w._team_assignment_context(repo,data,assignments,ids,{r["sha256"] for r in event["evidence"]})
        checked = tr.validate_issue_event_actor(event,assignments,context,expected_base_commit=issue["report"]["base_commit"])
        a = assignments["assignments"][checked["assignment_id"]]["assignment"]
        if a["schema"] != tr.DELIVERY_ASSIGNMENT_SCHEMA: return None
        if ({x["path"]:x["sha256"] for x in a["input_hashes"]} != issue["repair_sources"]
                or {x["path"]:x["sha256"] for x in event["candidate_manifest"]} != inputs):
            fail("FROZEN_R_OR_REPAIR_MANIFEST_CHANGED")
        validate_combined_assignment(repo,a)
        return a["review_binding"]["delivery_prefix"]
    return None


def check_carried_history(repo: Path, prefix: dict, published_head: str) -> None:
    """Preserve all original commits and H tree blobs, including dirty metadata.

    The CURRENT worktree copies of historical metadata are deliberately NOT
    staged in source repair delivery. Their dirty bytes remain foreign-protected.
    """
    w = _w(); validate_delivery_prefix(repo,prefix)
    w._team_git(repo,"merge-base","--is-ancestor",prefix["base_head"],published_head)
    parents=w._team_git(repo,"show","-s","--format=%P",published_head).decode().split()
    if parents != [prefix["base_head"]]: fail("DELIVERY_NOT_SINGLE_CHILD_OF_H")
    for path,row in prefix["files"].items():
        body,mode = w._team_integration_blob(repo,published_head,path)
        if w._resume_digest(body) != row["sha256"] or mode != row["mode"]:
            fail("CARRIED_HISTORY_REWRITTEN:"+path)


def combined_delivery_plan(repo: Path, *, candidate_commit: str, implementer: str, reviewer: str,
                           next_check: str) -> dict:
    """Prepare exact new assignments/result shapes. Does not create native evidence."""
    from orchestrator import team_records as tr
    w = _w(); _,data,_ = w._team_current(repo);w._team_actor(repo,data)
    local=w._team_local(repo);saved=local["operations"].get(CANCEL_ID+":control13",{}).get("integration",{})
    m=_saved_check(saved,CANCEL_ID+":control13")
    if saved["state"]!="COMPLETE":fail("COMPLETED_MIGRATION_REQUIRED")
    issues=tr.read_registry(w._resume_file(repo,w.TEAM_ISSUES),"issues",archive_loader=lambda p:w._resume_file(repo,Path(p)))
    original=w._team_assignments(repo)["assignments"][ASSIGNMENT_ID]["assignment"]
    matches=[i for i in issues["issues"].values() if original["subject"] in {i.get("repair_subject_id"),i["issue_id"]}]
    if len(matches)!=1:fail("EXACT_SELECTOR_ISSUE_REQUIRED")
    issue=matches[0]
    if (reviewer in {*m["author_ids"],implementer,issue["report"]["reporter_task"],"HUMAN_OWNER"}
            or implementer==reviewer or not reviewer or not implementer):fail("DISTINCT_NATIVE_REVIEWER_REQUIRED")
    files=[{"path":p,"sha256":sha} for p,sha in sorted(combined_source_manifest(m).items())]
    prefix=delivery_prefix_manifest(repo,remote_base=HISTORICAL_REMOTE,head=BASE_HEAD)
    binding={"report_base_commit":issue["report"]["base_commit"],"candidate_commit":candidate_commit,
             "candidate_manifest":files,"delivery_prefix":prefix,"author_ids":m["author_ids"]}
    assignments=[]
    for role,person,suffix in (("implementation",implementer,"producer"),("independent-checker",reviewer,"reviewer")):
        a=copy.deepcopy(original)
        a.update(schema=tr.DELIVERY_ASSIGNMENT_SCHEMA,assignment_id="CONTROL13_"+candidate_commit[:16]+"_"+suffix,
                 assignee=person,role=role,base_commit=BASE_HEAD,
                 input_hashes=[{"path":p,"sha256":sha} for p,sha in sorted(issue["repair_sources"].items())],
                 permitted_paths=sorted(BASE_HASHES),review_binding=binding,operation="CREATE",status="ASSIGNED",
                 previous_assignment_sha256="ABSENT",previous_assignment_event_sha256="ABSENT",
                 resolved_model=None,resolved_effort=None,next_check=next_check,
                 requested_model="gpt-5.6-terra" if role=="independent-checker" else original["requested_model"],
                 requested_effort="medium" if role=="independent-checker" else original["requested_effort"],
                 stopping_condition="Fixed C8 only; no candidate editing, descendants or canonical writes. Preserve R2 and reviewed O..H. Return actual native output.",
                 output_locator="docs/session_protocols/control13_"+candidate_commit[:16]+"_"+suffix+".json")
        tr._validate_assignment(a);validate_combined_assignment(repo,a);assignments.append(a)
    return {"schema":"q3_control13_delivery_plan.v1","assignments":assignments,"issue_id":issue["issue_id"],
            "candidate_manifest":files,"delivery_prefix":prefix,"writes_performed":False,
            "native_results":False,"FIX_VERIFIED":False,"publication_authorized":False}


def operational_launch_permit(repo: Path, *, operation_id: str) -> dict:
    """Final same-epoch native launch gate. Unknown/lost permit is never renewed."""
    w = _w()
    with w._execution_writer_epoch(repo, integration_operation=operation_id) as epoch:
        local = w._team_local(repo);record=local["operations"].get(operation_id,{})
        saved=copy.deepcopy(record.get("integration",{}))
        if saved.get("schema") != REVIEW_SCHEMA:fail("REVIEW_RESERVATION_REQUIRED")
        m=_review_request(saved["request"])
        if operation_id != review_operation_id(m):fail("REVIEW_SAVED_BINDING")
        _review_preimages(repo,m,local,remove_review=True)
        if not _same_engine(saved["engine"],w._team_integration_engine(repo)):fail("ENGINE_COMMIT_CHANGED")
        if saved.get("origin_sha256") != w._team_bootstrap_endpoint(repo):fail("REVIEW_ENDPOINT_CHANGED")
        if saved["state"] != "PENDING" or saved["launch_attempted"]:
            return {"status":"RECONCILE_ORIGINAL","execute_once":False,"operation_id":operation_id}
        saved["launch_attempted"]=True
        w._team_local_save(repo,local,{**local,"operations":{**local["operations"],operation_id:{**record,"integration":saved}}},epoch)
        return {"status":"LAUNCH_PERMIT_CONSUMED","execute_once":True,"operation_id":operation_id,
                "native_request":{"assignment":saved["request"]["assignment"],"sandbox":"read-only","descendants":0,
                                  "engine_commit":m["engine_commit"],"manifest_sha256":digest(m)},
                "native_launch_performed":False,"old_launch_changed":False}


def check_delivery_intent(repo: Path, data: dict) -> None:
    """Reject a known-impossible composed publication BEFORE persisting its INTENT.

    Narrow to this installed recovery and this original repair subject. Other
    operations retain existing guards. This is local proof checking, not fresh
    remote observation and never an effect reservation.
    """
    w = _w(); op=data['operation']
    if op.get('command')!='publication' or op.get('state')!='INTENT': return
    local=w._team_local(repo)
    saved=local['operations'].get(CANCEL_ID+':control13',{}).get('integration',{})
    if saved.get('state')!='COMPLETE': return
    original=w._team_assignments(repo)['assignments'].get(ASSIGNMENT_ID,{}).get('assignment',{})
    if op.get('id')!=str(original.get('subject'))+':publication': return
    m=_saved_check(saved,CANCEL_ID+':control13')
    inputs=combined_source_manifest(m)
    if (owner(data)!=m['owner'] or op.get('kind')!='PUBLISH' or op.get('inputs')!=inputs
            or op.get('subject')!={'kind':'REPAIR','id':original['subject'],'sha256':digest(inputs)}
            or data['pins']['head']!=m['head'] or w._team_git(repo,'rev-parse','HEAD').decode().strip()!=m['head']):
        fail('COMPOSED_PUBLICATION_INTENT_BINDING')
    prefix=reviewed_delivery_prefix(repo,data,inputs)
    if prefix is None:fail('REVIEWED_COMPOSED_PREFIX_REQUIRED')
    validate_delivery_prefix(repo,prefix)


def prepare_operational_review_request(repo: Path, m: dict, grant: dict, *, reviewer_id: str, next_check: str) -> dict:
    """Build a request only. It contains no review, no native receipt and no approval."""
    from orchestrator import team_records as tr
    w=_w();validate_manifest(m);_validate_grant(grant,m)
    with w._execution_writer_epoch(repo):
        local=w._team_local(repo);_review_preimages(repo,m,local,remove_review=False)
        a=copy.deepcopy(w._team_assignments(repo)['assignments'][ASSIGNMENT_ID]['assignment'])
        oid=review_operation_id(m)
        a.update(schema=tr.ASSIGNMENT_SCHEMA,assignment_id=oid,assignee=reviewer_id,role='independent-checker',
            owner_task=m['owner']['task'],owner_host=m['owner']['host'],owner_epoch=m['owner']['epoch'],
            owner_installation_ref=m['owner']['installation_ref'],base_commit=m['engine_commit'],subject=digest(m),
            input_hashes=[{'path':p,'sha256':h} for p,h in sorted(combined_source_manifest(m).items())],
            permitted_paths=sorted(BASE_HASHES),requested_model='gpt-5.6-terra',requested_effort='medium',
            resolved_model=None,resolved_effort=None,operation='CREATE',status='ASSIGNED',
            previous_assignment_sha256='ABSENT',previous_assignment_event_sha256='ABSENT',prerequisites=[],
            output_locator='docs/session_protocols/control13-operational-review-'+digest(m)+'.json',
            next_check=next_check,stopping_condition='Read-only exact C8 activation and full chain review; no edits, descendants, canonical writes or claimed native FIX. Return bound approval or rejection and actual evidence.')
        request={'schema':REVIEW_SCHEMA,'manifest':m,'grant':grant,'assignment':a,'read_only':True}
        _review_request(request)
        return request
