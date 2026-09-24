"""Fail-closed activation of one reviewed v13 -> v14 source candidate.

This is a source activation path only. It never edits RESUME/HISTORY, creates
an intake receipt, changes the owner, or clears a publication operation. Its
review records preserve the owner's exact instruction and root-observed
reports; they do not claim provider-verified provenance.
"""
from __future__ import annotations

import argparse
import base64
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import tempfile
from typing import Any


SCHEMA = "q3_control14_activation.v1"
REVIEW_SCHEMA = "q3_control14_native_review_report.v1"
RESERVATION_NAME = "q3-control14-activation.json"
LOCK_NAME = "q3-three-body.writer.lock"
BRANCH = "refs/heads/rh_clean"
FATAL = "TEAM_PUBLICATION_INTAKE_RECEIPT_REQUIRED"
CONTROL_PATH = "docs/CODEX_CONTROL.md"
ACTIVATION_PATH = "orchestrator/control14_activation.py"
ACTIVATION_TEST_PATH = "orchestrator/tests/test_control14_activation.py"
ADDED_PATHS = frozenset({ACTIVATION_PATH, ACTIVATION_TEST_PATH})
SOURCE_PATHS = tuple(sorted((
    CONTROL_PATH,
    ACTIVATION_PATH,
    "orchestrator/startup_runtime.py",
    "orchestrator/workflow_runtime.py",
    "orchestrator/tests/test_workflow_runtime.py",
    ACTIVATION_TEST_PATH,
)))
COPY_ORDER = tuple(p for p in SOURCE_PATHS if p != CONTROL_PATH) + (CONTROL_PATH,)
REVIEW_CHECKS = (
    "candidate_source_and_before_hashes_exact",
    "control_copied_last_and_crash_recovery_bounded",
    "fatal_is_only_publication_intake_receipt_required",
    "foreign_index_and_worktree_state_preserved",
    "no_receipt_or_old_publication_recreated_or_cleared",
    "one_exact_six_path_commit_nonforce_push_and_remote_readback",
    "remote_checkpoint_history_and_owner_pinned",
)
MAX_SOURCE_BYTES = 8 * 1024 * 1024
MAX_INSTRUCTION_BYTES = 1024 * 1024
MAX_REPORT_BYTES = 4 * 1024 * 1024
MAX_RESERVATION_BYTES = 64 * 1024 * 1024
REVIEW_PROVENANCE = "ROOT_OBSERVED_NATIVE_REVIEW"
REVIEW_MODEL = "gpt-6-astra"
REVIEW_EFFORT = "low"
REVIEWER_COUNT = 2
REVIEW_SEVERITIES = frozenset({"CRITICAL", "HIGH", "MEDIUM", "LOW", "WORDING",
                               "OFF-TARGET", "TOOL-FAILURE"})
FINDING_DISPOSITIONS = frozenset({"FIXED", "WITHDRAWN", "ACCEPTED", "DEFERRED", "OPEN"})
ACTIVATION_STATES = frozenset({"PENDING", "UNKNOWN", "PUSH_RESERVED", "PUSH_ATTEMPTED",
                               "CONFIRMED"})
RETIRED_ASSIGNMENT_PREFIX = "Retired assignment (outcome UNKNOWN): "


def _w():
    from orchestrator import workflow_runtime
    return workflow_runtime


def _fail(code: str) -> None:
    raise _w().WorkflowRuntimeError("CONTROL14_ACTIVATION_" + code)


def _digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _json(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                        separators=(",", ":")) + "\n").encode("utf-8")


def _git(repo: Path, *args: str, check: bool = True) -> bytes:
    result = subprocess.run(["git", *args], cwd=repo, capture_output=True,
                            timeout=45, check=False)
    if check and result.returncode:
        _fail("GIT_OBSERVATION_FAILED:" + (args[0] if args else "unknown"))
    return result.stdout


def _common(repo: Path) -> Path:
    value = Path(_git(repo, "rev-parse", "--git-common-dir").decode().strip())
    return (repo / value).resolve() if not value.is_absolute() else value.resolve()


def _mode(path: Path) -> int | None:
    try:
        st = os.lstat(path)
    except FileNotFoundError:
        return None
    if stat.S_ISLNK(st.st_mode) or not stat.S_ISREG(st.st_mode):
        _fail("DESTINATION_NOT_REGULAR:" + str(path.name))
    return 0o755 if st.st_mode & 0o111 else 0o644


def _read(path: Path) -> bytes | None:
    if _mode(path) is None:
        return None
    return path.read_bytes()


def _write_atomic(path: Path, payload: bytes, mode: int = 0o600) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.is_symlink():
        _fail("PRIVATE_STATE_SYMLINK")
    fd, tmp_name = tempfile.mkstemp(prefix="." + path.name + ".", dir=path.parent)
    tmp = Path(tmp_name)
    try:
        os.fchmod(fd, mode)
        with os.fdopen(fd, "wb", closefd=True) as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(tmp, path)
        dfd = os.open(path.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
        try:
            os.fsync(dfd)
        finally:
            os.close(dfd)
    finally:
        try:
            tmp.unlink()
        except FileNotFoundError:
            pass


def _lock(repo: Path):
    """Use the existing common-dir writer lock, without the publication gate."""
    common = _common(repo)
    path = common / LOCK_NAME
    flags = os.O_RDWR | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        fd = os.open(path, flags)
    except OSError:
        _fail("WRITER_LOCK_UNAVAILABLE")
    st = os.fstat(fd)
    if not stat.S_ISREG(st.st_mode) or os.lstat(path).st_ino != st.st_ino:
        os.close(fd)
        _fail("WRITER_LOCK_INVALID")
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        os.close(fd)
        _fail("WRITER_LOCK_COLLISION")
    return fd


def _unlock(fd: int) -> None:
    try:
        fcntl.flock(fd, fcntl.LOCK_UN)
    finally:
        os.close(fd)


def _blob(repo: Path, commit: str, path: str) -> tuple[bytes | None, int | None]:
    entries = [row for row in _git(repo, "ls-tree", "-z", commit, "--", path).split(b"\0") if row]
    if not entries:
        return None, None
    if len(entries) != 1:
        _fail("GIT_PATH_AMBIGUOUS:" + path)
    meta, found = entries[0].split(b"\t", 1)
    mode, kind, oid = meta.decode().split()
    if found.decode() != path or kind != "blob" or mode not in {"100644", "100755"}:
        _fail("GIT_MODE_INVALID:" + path)
    size = int(_git(repo, "cat-file", "-s", oid))
    if size > MAX_SOURCE_BYTES:
        _fail("SOURCE_LIMIT:" + path)
    return _git(repo, "cat-file", "blob", oid), (0o755 if mode == "100755" else 0o644)


def _index_path(repo: Path) -> Path:
    path = Path(_git(repo, "rev-parse", "--git-path", "index").decode().strip())
    return path if path.is_absolute() else repo / path


def _index_snapshot(repo: Path) -> dict[str, str]:
    path = _index_path(repo)
    if path.is_symlink() or not path.is_file():
        _fail("INDEX_UNAVAILABLE")
    raw = path.read_bytes()
    entries = _git(repo, "ls-files", "--stage", "-z")
    foreign = []
    for row in entries.split(b"\0"):
        if not row:
            continue
        _, name = row.split(b"\t", 1)
        if name.decode("utf-8") not in SOURCE_PATHS:
            foreign.append(row)
    return {"index_sha256": _digest(raw), "foreign_index_sha256": _digest(b"\0".join(foreign))}


def _foreign_snapshot(repo: Path, exclusions: list[dict[str, Any]] | None = None) -> str:
    """Hash foreign state, omitting only verified native review evidence files."""
    excluded: dict[str, dict[str, Any]] = {}
    for item in exclusions or []:
        if (not isinstance(item, dict) or set(item) != {"path", "sha256", "mode"}
                or not isinstance(item["path"], str) or item["path"] in SOURCE_PATHS
                or item["path"].startswith("/") or ".." in Path(item["path"]).parts
                or not re.fullmatch(r"[0-9a-f]{64}", item["sha256"])
                or item["mode"] not in {0o644, 0o755}
                or item["path"] in excluded):
            _fail("FOREIGN_EXCLUSIONS_INVALID")
        excluded[item["path"]] = item
        current_mode = _mode(repo / item["path"])
        current = _read(repo / item["path"])
        if current is None or current_mode != item["mode"] or _digest(current) != item["sha256"]:
            _fail("REVIEW_EVIDENCE_CHANGED:" + item["path"])
    rows = _git(repo, "--no-optional-locks", "status", "--porcelain=v1", "-z",
                "--untracked-files=all").split(b"\0")
    result: list[dict[str, Any]] = []
    i = 0
    while i < len(rows) and rows[i]:
        raw = rows[i]
        i += 1
        status, path_raw = raw[:2], raw[3:]
        paths = [path_raw]
        if b"R" in status or b"C" in status:
            if i >= len(rows) or not rows[i]:
                _fail("STATUS_TRUNCATED")
            paths.append(rows[i])
            i += 1
        for path_raw in paths:
            relative = path_raw.decode("utf-8")
            if relative in SOURCE_PATHS or relative in excluded:
                continue
            absolute = repo / relative
            try:
                st = os.lstat(absolute)
            except FileNotFoundError:
                item = {"path": relative, "status": status.decode(), "missing": True}
            else:
                if stat.S_ISLNK(st.st_mode):
                    content = os.readlink(absolute).encode()
                    mode = "symlink"
                elif stat.S_ISREG(st.st_mode):
                    content = absolute.read_bytes()
                    mode = 0o755 if st.st_mode & 0o111 else 0o644
                elif stat.S_ISDIR(st.st_mode):
                    content, mode = b"", "directory"
                else:
                    _fail("FOREIGN_PATH_TYPE_UNSUPPORTED")
                item = {"path": relative, "status": status.decode(), "mode": mode,
                        "sha256": _digest(content)}
            result.append(item)
    return _digest(_json(result))


def _remote_tip(repo: Path) -> str:
    lines = _git(repo, "ls-remote", "--exit-code", "origin", BRANCH).decode().splitlines()
    if len(lines) != 1:
        _fail("REMOTE_BRANCH_AMBIGUOUS")
    commit, ref = lines[0].split("\t")
    if ref != BRANCH or not re.fullmatch(r"[0-9a-f]{40}", commit):
        _fail("REMOTE_REF_INVALID")
    return commit


def _verify_environment_pins(repo: Path, *, origin_sha256: str | None = None) -> None:
    branch = _git(repo, "symbolic-ref", "-q", "HEAD", check=False).decode().strip()
    if branch != BRANCH:
        _fail("ACTIVE_BRANCH_CHANGED")
    if origin_sha256 is not None and _endpoint_hash(repo) != origin_sha256:
        _fail("ORIGIN_ENDPOINT_CHANGED")


def _pinned_remote_tip(repo: Path, manifest: dict[str, Any]) -> str:
    _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
    tip = _remote_tip(repo)
    _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
    return tip


def _observe_remote(repo: Path, expected: str | None = None,
                    origin_sha256: str | None = None) -> dict[str, Any]:
    _verify_environment_pins(repo, origin_sha256=origin_sha256)
    tip = _remote_tip(repo)
    _git(repo, "fetch", "--no-tags", "--no-write-fetch-head", "origin", tip)
    resume_path = str(_w().RESUME_PATH)
    history_path = str(_w().RESUME_HISTORY_PATH)
    resume, _ = _blob(repo, tip, resume_path)
    history, _ = _blob(repo, tip, history_path)
    if resume is None or history is None:
        _fail("REMOTE_CHECKPOINT_OR_HISTORY_MISSING")
    if _remote_tip(repo) != tip or (expected is not None and tip != expected):
        _fail("REMOTE_CHANGED_DURING_OBSERVATION")
    _verify_environment_pins(repo, origin_sha256=origin_sha256)
    data, _ = _w()._resume_document(resume)
    return {"head": tip, "resume_sha256": _digest(resume),
            "history_sha256": _digest(history), "owner": _owner(data),
            "resume": resume, "history": history}


def _owner(data: dict[str, Any]) -> dict[str, Any]:
    return {"task": data["owner_thread_id"], "host": data["owner_host_id"],
            "ownership": data["ownership"], "operation": data["operation"]}


def _retired_assignment_markers(repo: Path) -> dict[str, dict[str, Any]]:
    w = _w()
    raws: list[bytes] = []
    current = _read(repo / str(w.RESUME_PATH))
    if current is None:
        _fail("LOCAL_CHECKPOINT_OR_HISTORY_MISSING")
    raws.append(current)
    history = _read(repo / str(w.RESUME_HISTORY_PATH))
    if history is None:
        _fail("LOCAL_CHECKPOINT_OR_HISTORY_MISSING")
    for kind, _revision, raw in w._resume_history(history).values():
        if kind in {"resume", "intent"}:
            raws.append(raw)

    result: dict[str, dict[str, Any]] = {}
    for raw in raws:
        _data, body = w._resume_document(raw)
        for line in body.splitlines():
            if not line.startswith(RETIRED_ASSIGNMENT_PREFIX):
                continue
            encoded = line[len(RETIRED_ASSIGNMENT_PREFIX):]
            try:
                operation = json.loads(encoded)
            except json.JSONDecodeError:
                _fail("LOCAL_ASSIGNMENT_RETIREMENT_INVALID")
            subject = operation.get("subject") if isinstance(operation, dict) else None
            if (not isinstance(operation, dict)
                    or json.dumps(operation, ensure_ascii=False, sort_keys=True) != encoded
                    or operation.get("kind") != "ASSIGN"
                    or operation.get("command") != "agent-launch"
                    or operation.get("state") != "UNKNOWN"
                    or not isinstance(operation.get("id"), str)
                    or not operation["id"]
                    or not isinstance(subject, dict)
                    or not isinstance(subject.get("id"), str)
                    or not subject.get("id")):
                _fail("LOCAL_ASSIGNMENT_RETIREMENT_INVALID")
            operation_id = operation["id"]
            if operation_id in result and result[operation_id] != operation:
                _fail("LOCAL_ASSIGNMENT_RETIREMENT_INVALID")
            result[operation_id] = operation
    return result


def _local_team_snapshot(repo: Path, owner: dict[str, Any] | None = None) -> dict[str, Any]:
    w = _w()
    local = w._team_local(repo)
    checkpoint = _read(repo / str(w.RESUME_PATH))
    if checkpoint is None:
        _fail("LOCAL_CHECKPOINT_OR_HISTORY_MISSING")
    checkpoint_data, _ = w._resume_document(checkpoint)
    current_owner = _owner(checkpoint_data)
    if owner is not None and owner != current_owner:
        _fail("LOCAL_OWNER_CHANGED")
    owner = current_owner
    owner_operation_id = owner["operation"].get("id")
    owner_epoch = owner["ownership"].get("epoch")
    retired_assignment_markers = _retired_assignment_markers(repo)
    for operation_id, receipt in local["operations"].items():
        if not isinstance(receipt, dict):
            _fail("LOCAL_EFFECT_STATE_INVALID:" + str(operation_id))
        if receipt.get("state") in {"RESERVED", "UNKNOWN"}:
            marker = retired_assignment_markers.get(operation_id)
            binding = receipt.get("launch_binding")
            bound_operation = binding.get("operation") if isinstance(binding, dict) else None
            expected_marker = dict(bound_operation) if isinstance(bound_operation, dict) else None
            if expected_marker is not None:
                expected_marker.update(state="UNKNOWN", evidence=[])
            historical_assignment = (
                marker is not None
                and expected_marker == marker
                and operation_id != owner_operation_id
                and receipt.get("schema") == "q3_team_remote_observation.v1"
                and receipt.get("operation_id") == operation_id
                and isinstance(binding, dict)
                and marker.get("kind") == "ASSIGN"
                and marker.get("command") == "agent-launch"
                and marker.get("subject", {}).get("kind") == "ASSIGNMENT"
                and marker.get("subject", {}).get("sha256") == binding.get("assignment_sha256")
                and type(receipt.get("epoch")) is int
                and type(owner_epoch) is int
                and receipt["epoch"] < owner_epoch)
            if not historical_assignment:
                _fail("LOCAL_RESERVED_OR_UNKNOWN_EFFECT:" + str(operation_id))
        for name in ("bootstrap", "integration", "publication"):
            effect = receipt.get(name)
            if isinstance(effect, dict) and effect.get("state") in {
                    "RESERVED", "UNKNOWN", "PUSH_RESERVED"}:
                _fail("LOCAL_RESERVED_OR_UNKNOWN_EFFECT:" + str(operation_id) + ":" + name)
    watch = local.get("watch")
    if isinstance(watch, dict) and watch.get("state") == "UNKNOWN":
        _fail("LOCAL_RESERVED_OR_UNKNOWN_EFFECT:watch")

    private = w._team_private_read(repo, w.TEAM_LOCAL)
    if private is None:
        mode = None
        private_sha = None
    else:
        path = _common(repo) / w.TEAM_LOCAL
        st = os.lstat(path)
        mode = stat.S_IMODE(st.st_mode)
        if mode != 0o600:
            _fail("LOCAL_PRIVATE_STATE_MODE_INVALID")
        raw = path.read_bytes()
        private_sha = _digest(raw)
    return {"team_local_sha256": private_sha, "team_local_mode": mode,
            "team_local_installation_ref": local["installation_ref"],
            "team_local_epoch_floor": local["epoch_floor"]}


def _verify_local_team_snapshot(repo: Path, manifest: dict[str, Any]) -> None:
    actual = _local_team_snapshot(repo, manifest["owner"])
    expected = {key: value for key, value in manifest["local"].items()
                if key.startswith("team_local_")}
    if actual != expected:
        _fail("LOCAL_PRIVATE_STATE_CHANGED")


def _control_version(raw: bytes) -> int:
    from orchestrator.startup_runtime import _control_identity
    import tempfile as _tempfile
    fd, name = _tempfile.mkstemp(prefix="q3-control14-header-")
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(raw)
        return _control_identity(Path(name)).version
    finally:
        Path(name).unlink(missing_ok=True)


def _validate_v13_publication(repo: Path, raw: bytes, data: dict[str, Any]) -> dict[str, Any]:
    operation = data["operation"]
    if (_control_version(_read(repo / CONTROL_PATH) or b"") != 13
            or data.get("schema") != "q3_resume.v2"
            or data["ownership"].get("state") != "ACTIVE"
            or data["ownership"].get("transfer") is not None
            or data["reconciliation_pending"]
            or operation.get("kind") != "PUBLISH"
            or operation.get("command") != "publication"
            or operation.get("state") not in {"INTENT", "UNKNOWN"}
            or operation.get("subject", {}).get("kind") != "REPAIR"):
        _fail("V13_COMPACT_PUBLICATION_PREIMAGE_REQUIRED")
    try:
        plan = _w().live_plan_v10(repo, owned_paths=[])
    except _w().WorkflowRuntimeError as exc:
        if str(exc).split(":", 1)[0] != FATAL:
            raise
        plan = {"status": "FATAL", "holds": [FATAL]}
    startup_fatal = plan.get("startup", {}).get("fatal_errors", [])
    holds = plan.get("holds", [])
    fatal = startup_fatal if startup_fatal else holds
    if (plan.get("status") != "FATAL" or fatal != [FATAL]
            or any(item != FATAL for item in holds if isinstance(item, str) and item.startswith("FATAL:"))):
        _fail("OTHER_FATAL_BLOCKED")
    return {"status": "FATAL", "fatal": [FATAL]}


def _endpoint_hash(repo: Path) -> str:
    fetch = _git(repo, "remote", "get-url", "--all", "origin").splitlines()
    push = _git(repo, "remote", "get-url", "--push", "--all", "origin").splitlines()
    mirror = _git(repo, "config", "--type=bool", "--default=false", "--get",
                  "remote.origin.mirror").strip()
    if len(fetch) != 1 or push != fetch or mirror != b"false":
        _fail("SINGLE_ORIGIN_ENDPOINT_REQUIRED")
    return _digest(fetch[0])


def _candidate_engine(engine: Path, expected_commit: str | None = None) -> dict[str, Any]:
    engine = engine.resolve()
    commit = _git(engine, "rev-parse", "HEAD").decode().strip()
    if expected_commit is not None and commit != expected_commit:
        _fail("ENGINE_COMMIT_CHANGED")
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        _fail("ENGINE_COMMIT_INVALID")
    modules = ("orchestrator/workflow_runtime.py", "orchestrator/startup_runtime.py",
               "orchestrator/control14_activation.py")
    sources = {}
    for relative in modules:
        current = _read(engine / relative)
        committed, _ = _blob(engine, commit, relative)
        if current is None or current != committed:
            _fail("ENGINE_SOURCE_CHANGED:" + relative)
        sources[relative] = _digest(current)
    return {"root": str(engine), "commit": commit, "source_sha256": sources}


def _manifest_snapshot(repo: Path, engine: Path, candidate_commit: str,
                       foreign_exclusions: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    w = _w()
    repo = repo.resolve()
    engine = engine.resolve()
    _verify_environment_pins(repo)
    if repo == engine:
        _fail("ISOLATED_ENGINE_REQUIRED")
    head = _git(repo, "rev-parse", "HEAD").decode().strip()
    branch = _git(repo, "symbolic-ref", "-q", "HEAD", check=False).decode().strip()
    if branch != BRANCH:
        _fail("CANONICAL_BRANCH_REQUIRED")
    origin_sha256 = _endpoint_hash(repo)
    if _git(repo, "status", "--porcelain=v1", "--", *SOURCE_PATHS):
        _fail("SOURCE_DESTINATION_DIRTY")
    index = _index_snapshot(repo)
    local_raw = _read(repo / str(w.RESUME_PATH))
    local_history = _read(repo / str(w.RESUME_HISTORY_PATH))
    if local_raw is None or local_history is None:
        _fail("LOCAL_CHECKPOINT_OR_HISTORY_MISSING")
    local_data, _ = w._resume_document(local_raw)
    local_team = _local_team_snapshot(repo)
    gate = _validate_v13_publication(repo, local_raw, local_data)
    remote = _observe_remote(repo, expected=head, origin_sha256=origin_sha256)
    if (remote["resume"] != local_raw or remote["history"] != local_history
            or remote["owner"] != _owner(local_data)):
        _fail("REMOTE_CHECKPOINT_HISTORY_OR_OWNER_CHANGED")
    files = []
    total = 0
    for path in SOURCE_PATHS:
        before, before_mode = _blob(repo, head, path)
        after, after_mode = _blob(engine, candidate_commit, path)
        if (after is None
                or (path in ADDED_PATHS and before is not None)
                or (path not in ADDED_PATHS and before is None)
                or (before is not None and before_mode not in {0o644, 0o755})):
            _fail("CANDIDATE_SOURCE_MISSING:" + path)
        total += len(before or b"") + len(after)
        if total > MAX_SOURCE_BYTES:
            _fail("SOURCE_LIMIT")
        files.append({"path": path, "before_sha256": None if before is None else _digest(before),
                      "before_mode": before_mode, "sha256": _digest(after), "mode": after_mode})
    files.sort(key=lambda row: row["path"])
    if _control_version(_blob(engine, candidate_commit, CONTROL_PATH)[0]) != 14:
        _fail("CANDIDATE_CONTROL_NOT_V14")
    authors = _git(engine, "log", "--format=%an", head + ".." + candidate_commit,
                   "--", *SOURCE_PATHS).decode().splitlines()
    author_ids = sorted({name.strip() for name in authors if name.strip()})
    if not author_ids:
        _fail("CANDIDATE_AUTHOR_UNAVAILABLE")
    _verify_environment_pins(repo, origin_sha256=origin_sha256)
    return {"schema": SCHEMA, "base_head": head, "branch": BRANCH,
            "preactivation_gate": gate,
            "origin_sha256": origin_sha256, "candidate_engine": _candidate_engine(engine, candidate_commit),
            "files": files, "owner": remote["owner"],
            "remote": {"head": remote["head"], "resume_sha256": remote["resume_sha256"],
                       "history_sha256": remote["history_sha256"]},
            "local": {"resume_sha256": _digest(local_raw),
                      "history_sha256": _digest(local_history), **local_team},
            "index": index, "foreign_sha256": _foreign_snapshot(repo, foreign_exclusions),
            "author_ids": author_ids}


def prepare_manifest(repo: Path, *, candidate_commit: str, engine_root: Path | None = None,
                     foreign_exclusions: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    engine = (engine_root or Path(__file__).resolve().parents[1]).resolve()
    if not re.fullmatch(r"[0-9a-f]{40}", candidate_commit):
        _fail("CANDIDATE_COMMIT_INVALID")
    _git(engine, "merge-base", "--is-ancestor", candidate_commit, candidate_commit)
    return _manifest_snapshot(repo, engine, candidate_commit, foreign_exclusions)


def _validate_manifest(manifest: dict[str, Any]) -> None:
    if (not isinstance(manifest, dict) or set(manifest) != {
            "schema", "base_head", "branch", "preactivation_gate", "origin_sha256",
            "candidate_engine", "files", "owner", "remote", "local", "index",
            "foreign_sha256", "author_ids"}
            or manifest["schema"] != SCHEMA or manifest["branch"] != BRANCH
            or manifest["preactivation_gate"] != {"status": "FATAL", "fatal": [FATAL]}
            or not isinstance(manifest["files"], list)
            or [row.get("path") for row in manifest["files"] if isinstance(row, dict)] != list(SOURCE_PATHS)
            or not isinstance(manifest["candidate_engine"], dict)
            or set(manifest["candidate_engine"]) != {"root", "commit", "source_sha256"}
            or not isinstance(manifest["author_ids"], list)
            or manifest["author_ids"] != sorted(set(manifest["author_ids"]))):
        _fail("MANIFEST_INVALID")
    for field in ("base_head", "origin_sha256", "foreign_sha256"):
        if not isinstance(manifest[field], str) or not re.fullmatch(r"[0-9a-f]{40,64}", manifest[field]):
            _fail("MANIFEST_INVALID")
    if (not isinstance(manifest["remote"], dict)
            or set(manifest["remote"]) != {"head", "resume_sha256", "history_sha256"}
            or not isinstance(manifest["local"], dict)
            or set(manifest["local"]) != {"resume_sha256", "history_sha256", "team_local_sha256",
                                           "team_local_mode", "team_local_installation_ref",
                                           "team_local_epoch_floor"}
            or not isinstance(manifest["index"], dict)
            or set(manifest["index"]) != {"index_sha256", "foreign_index_sha256"}
            or not isinstance(manifest["owner"], dict)
            or not isinstance(manifest["candidate_engine"].get("source_sha256"), dict)
            or set(manifest["candidate_engine"]["source_sha256"]) != {
                "orchestrator/workflow_runtime.py", "orchestrator/startup_runtime.py",
                "orchestrator/control14_activation.py"}):
        _fail("MANIFEST_BINDING_INVALID")
    local = manifest["local"]
    if (not re.fullmatch(r"[0-9a-f]{64}", local["resume_sha256"])
            or not re.fullmatch(r"[0-9a-f]{64}", local["history_sha256"])
            or ((local["team_local_sha256"] is None) != (local["team_local_mode"] is None))
            or (local["team_local_sha256"] is not None
                and (not re.fullmatch(r"[0-9a-f]{64}", local["team_local_sha256"])
                     or local["team_local_mode"] != 0o600))
            or not isinstance(local["team_local_installation_ref"], str)
            or not re.fullmatch(r"[0-9a-f]{64}", local["team_local_installation_ref"])
            or type(local["team_local_epoch_floor"]) is not int
            or local["team_local_epoch_floor"] < 0):
        _fail("MANIFEST_LOCAL_BINDING_INVALID")
    for row in manifest["files"]:
        added = row.get("path") in ADDED_PATHS
        before_valid = ((row.get("before_sha256") is None and row.get("before_mode") is None)
                        if added else
                        (isinstance(row.get("before_sha256"), str)
                         and re.fullmatch(r"[0-9a-f]{64}", row["before_sha256"]) is not None
                         and row.get("before_mode") in {0o644, 0o755}))
        if (set(row) != {"path", "before_sha256", "before_mode", "sha256", "mode"}
                or not before_valid
                or not re.fullmatch(r"[0-9a-f]{64}", row["sha256"])
                or row["mode"] not in {0o644, 0o755}):
            _fail("MANIFEST_FILE_INVALID")


def _loads_unique_json(raw: bytes, error_code: str) -> Any:
    def object_pairs(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate JSON key")
            result[key] = value
        return result

    try:
        return json.loads(raw.decode("utf-8"), object_pairs_hook=object_pairs)
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError):
        _fail(error_code)


def _validate_review_report(raw: bytes, report: Any, manifest: dict[str, Any],
                            reviewer_id: str) -> bool:
    """Validate one verbatim root-observed review, without provider claims."""
    fields = {"schema", "reviewer_id", "manifest_sha256", "candidate_commit", "files",
              "checks", "verdict", "findings", "original_finding_dispositions"}
    if (not isinstance(report, dict) or set(report) != fields
            or report["schema"] != REVIEW_SCHEMA
            or report["reviewer_id"] != reviewer_id
            or not isinstance(reviewer_id, str) or not reviewer_id.strip()
            or reviewer_id in {*manifest["author_ids"], manifest["owner"].get("task")}
            or report["manifest_sha256"] != _digest(_json(manifest))
            or report["candidate_commit"] != manifest["candidate_engine"]["commit"]
            or report["files"] != [{"path": row["path"], "sha256": row["sha256"]}
                                    for row in manifest["files"]]
            or report["checks"] != list(REVIEW_CHECKS)
            or not isinstance(report["verdict"], str)
            or report["verdict"] not in {"APPROVED", "REJECTED"}
            or not isinstance(report["findings"], list)
            or not isinstance(report["original_finding_dispositions"], list)
            or len(raw) > MAX_REPORT_BYTES):
        _fail("NATIVE_REVIEW_REPORT_INVALID")

    finding_ids = set()
    findings_are_clean = True
    for finding in report["findings"]:
        if (not isinstance(finding, dict) or set(finding) != {"id", "severity", "summary"}
                or not isinstance(finding["id"], str) or not finding["id"].strip()
                or finding["id"] in finding_ids
                or not isinstance(finding["severity"], str)
                or finding["severity"] not in REVIEW_SEVERITIES
                or not isinstance(finding["summary"], str) or not finding["summary"].strip()):
            _fail("NATIVE_REVIEW_FINDING_INVALID")
        finding_ids.add(finding["id"])
        if finding["severity"] != "WORDING":
            findings_are_clean = False

    disposition_ids = set()
    dispositions_are_clean = True
    for item in report["original_finding_dispositions"]:
        if (not isinstance(item, dict)
                or set(item) != {"id", "severity", "disposition", "reason"}
                or not isinstance(item["id"], str) or not item["id"].strip()
                or item["id"] in disposition_ids
                or not isinstance(item["severity"], str)
                or item["severity"] not in REVIEW_SEVERITIES
                or not isinstance(item["disposition"], str)
                or item["disposition"] not in FINDING_DISPOSITIONS
                or not isinstance(item["reason"], str) or not item["reason"].strip()):
            _fail("NATIVE_REVIEW_DISPOSITION_INVALID")
        disposition_ids.add(item["id"])
        if (item["severity"] in {"CRITICAL", "HIGH", "MEDIUM", "LOW"}
                and item["disposition"] not in {"FIXED", "WITHDRAWN"}):
            dispositions_are_clean = False
        if item["severity"] == "WORDING" and item["disposition"] == "OPEN":
            continue
        if item["disposition"] == "OPEN":
            dispositions_are_clean = False

    if not raw:
        _fail("NATIVE_REVIEW_REPORT_EMPTY")
    # A contradictory APPROVED verdict remains durable negative evidence.
    return (report["verdict"] == "APPROVED" and findings_are_clean
            and dispositions_are_clean)


def _review_exclusions(repo: Path, reservation: dict[str, Any]) -> list[dict[str, Any]]:
    exclusions: dict[str, dict[str, Any]] = {}
    root = repo.resolve()
    base = reservation.get("foreign_exclusions", [])
    if not isinstance(base, list):
        _fail("REVIEW_EXCLUSION_INVALID")
    items = list(base)
    items.extend(observation.get("foreign_exclusion")
                 for observation in reservation.get("review_observations", [])
                 if observation.get("foreign_exclusion") is not None)
    for item in items:
        if not isinstance(item, dict) or set(item) != {"path", "sha256", "mode"}:
            _fail("REVIEW_EXCLUSION_INVALID")
        if (not isinstance(item["path"], str) or not item["path"]
                or item["path"] in SOURCE_PATHS or item["path"].startswith("/")
                or ".." in Path(item["path"]).parts
                or not isinstance(item["sha256"], str)
                or not re.fullmatch(r"[0-9a-f]{64}", item["sha256"])
                or item["mode"] not in {0o644, 0o755}):
            _fail("REVIEW_EXCLUSION_INVALID")
        current = _read(repo / item["path"])
        if (_mode(repo / item["path"]) != item["mode"] or current is None
                or _digest(current) != item["sha256"]):
            _fail("REVIEW_EVIDENCE_CHANGED:" + str(item["path"]))
        absolute = (repo / item["path"]).resolve()
        if root not in absolute.parents or item["path"] in SOURCE_PATHS:
            _fail("REVIEW_EXCLUSION_INVALID")
        prior_item = exclusions.get(item["path"])
        if prior_item is not None and prior_item != item:
            _fail("REVIEW_EVIDENCE_PATH_CONFLICT:" + item["path"])
        exclusions[item["path"]] = item
    return [exclusions[path] for path in sorted(exclusions)]


def _reservation_path(repo: Path) -> Path:
    return _common(repo) / RESERVATION_NAME


def _read_reservation(repo: Path) -> dict[str, Any] | None:
    path = _reservation_path(repo)
    try:
        before = os.lstat(path)
    except FileNotFoundError:
        return None
    if not stat.S_ISREG(before.st_mode) or stat.S_IMODE(before.st_mode) != 0o600:
        _fail("RESERVATION_PRIVATE_FILE_REQUIRED")
    if before.st_size > MAX_RESERVATION_BYTES:
        _fail("RESERVATION_LIMIT")
    raw = path.read_bytes()
    try:
        after = os.lstat(path)
    except FileNotFoundError:
        _fail("RESERVATION_CHANGED_DURING_READ")
    if ((before.st_dev, before.st_ino, before.st_mode, before.st_size, before.st_mtime_ns)
            != (after.st_dev, after.st_ino, after.st_mode, after.st_size, after.st_mtime_ns)
            or len(raw) != before.st_size):
        _fail("RESERVATION_CHANGED_DURING_READ")
    if len(raw) > MAX_RESERVATION_BYTES:
        _fail("RESERVATION_LIMIT")
    value = _loads_unique_json(raw, "RESERVATION_CORRUPT")
    if not isinstance(value, dict) or value.get("schema") != SCHEMA or _json(value) != raw:
        _fail("RESERVATION_CORRUPT")
    return value


def _save_reservation(repo: Path, value: dict[str, Any]) -> None:
    _write_atomic(_reservation_path(repo), _json(value))


def _instruction_record(instruction: bytes | str | dict[str, Any]) -> dict[str, Any]:
    locator = None
    expected_sha = None
    if isinstance(instruction, bytes):
        raw = instruction
    elif isinstance(instruction, str):
        raw = instruction.encode("utf-8")
    elif isinstance(instruction, dict) and set(instruction) == {"raw", "locator", "expected_sha256"}:
        raw = instruction["raw"]
        locator = instruction["locator"]
        expected_sha = instruction["expected_sha256"]
        if (not isinstance(locator, str) or not locator
                or not isinstance(expected_sha, str)
                or not re.fullmatch(r"[0-9a-f]{64}", expected_sha)):
            _fail("OWNER_INSTRUCTION_LOCATOR_INVALID")
    else:
        _fail("OWNER_INSTRUCTION_INVALID")
    if not isinstance(raw, bytes) or not raw or len(raw) > MAX_INSTRUCTION_BYTES:
        _fail("OWNER_INSTRUCTION_INVALID")
    digest = _digest(raw)
    if expected_sha is not None and digest != expected_sha:
        _fail("OWNER_INSTRUCTION_HASH_MISMATCH")
    return {"sha256": digest, "raw_base64": base64.b64encode(raw).decode("ascii"),
            "source_locator": locator}


def _review_operation_id(manifest_sha: str, instruction_sha: str,
                         reviewer_ids: list[str]) -> str:
    binding = {"manifest_sha256": manifest_sha, "owner_instruction_sha256": instruction_sha,
               "reviewer_ids": reviewer_ids}
    return "control14-review-" + _digest(_json(binding))[:24]


def _review_record(repo: Path, report_raw: bytes, report: Any, manifest: dict[str, Any],
                   reviewer_id: str, report_path: Path) -> dict[str, Any]:
    clean = _validate_review_report(report_raw, report, manifest, reviewer_id)
    locator = str(report_path.resolve())
    exclusion = None
    try:
        relative = report_path.resolve().relative_to(repo.resolve()).as_posix()
    except ValueError:
        relative = None
    if relative is not None and relative not in SOURCE_PATHS:
        if _git(repo, "ls-files", "--error-unmatch", "--", relative, check=False).strip():
            _fail("REVIEW_REPORT_PATH_TRACKED:" + relative)
        mode = _mode(repo / relative)
        if mode is None:
            _fail("REVIEW_EVIDENCE_CHANGED:" + relative)
        exclusion = {"path": relative, "sha256": _digest(report_raw), "mode": mode}
    return {"reviewer_id": reviewer_id, "provenance": REVIEW_PROVENANCE,
            "requested_model": REVIEW_MODEL, "requested_effort": REVIEW_EFFORT,
            "provider_verified": False, "report_locator": locator,
            "report_sha256": _digest(report_raw),
            "report_base64": base64.b64encode(report_raw).decode("ascii"),
            "foreign_exclusion": exclusion, "clean_pass": clean}


def _validate_review_reservation(repo: Path, reservation: dict[str, Any]) -> list[dict[str, Any]]:
    manifest = reservation.get("manifest")
    _validate_manifest(manifest)
    if (reservation.get("manifest_sha256") != _digest(_json(manifest))
            or not isinstance(reservation.get("reviewer_ids"), list)
            or len(reservation["reviewer_ids"]) != REVIEWER_COUNT
            or any(not isinstance(item, str) for item in reservation["reviewer_ids"])
            or len(set(reservation["reviewer_ids"])) != REVIEWER_COUNT
            or not isinstance(reservation.get("review_observations"), list)
            or len(reservation["review_observations"]) > REVIEWER_COUNT
            or not isinstance(reservation.get("foreign_exclusions"), list)
            or not isinstance(reservation.get("owner_instruction"), dict)
            or set(reservation["owner_instruction"]) != {"sha256", "raw_base64", "source_locator"}
            or not isinstance(reservation["launch_intent"], dict)
            or set(reservation["launch_intent"]) != {
                "operation_id", "status", "manifest_sha256", "owner_instruction_sha256",
                "reviewer_ids", "preactivation_gate", "owner_sha256", "base_head",
                "requested_model", "requested_effort"}
            or reservation["launch_intent"].get("operation_id") != reservation.get("operation_id")
            or reservation["launch_intent"].get("status") != "RECORDED_BEFORE_SPAWN"
            or reservation["launch_intent"].get("manifest_sha256") != reservation.get("manifest_sha256")
            or reservation["launch_intent"].get("owner_instruction_sha256")
                != reservation["owner_instruction"].get("sha256")
            or reservation["launch_intent"].get("reviewer_ids") != reservation.get("reviewer_ids")
            or reservation["launch_intent"].get("preactivation_gate") != manifest.get("preactivation_gate")
            or reservation["launch_intent"].get("owner_sha256") != _digest(_json(manifest.get("owner")))
            or reservation["launch_intent"].get("base_head") != manifest.get("base_head")
            or reservation["launch_intent"].get("requested_model") != REVIEW_MODEL
            or reservation["launch_intent"].get("requested_effort") != REVIEW_EFFORT):
        _fail("REVIEW_RESERVATION_INVALID")
    try:
        instruction_raw = base64.b64decode(reservation["owner_instruction"]["raw_base64"], validate=True)
    except (ValueError, TypeError):
        _fail("OWNER_INSTRUCTION_CORRUPT")
    if (_digest(instruction_raw) != reservation["owner_instruction"]["sha256"]
            or not instruction_raw or len(instruction_raw) > MAX_INSTRUCTION_BYTES):
        _fail("OWNER_INSTRUCTION_CORRUPT")

    observations = reservation["review_observations"]
    observed_ids = []
    clean_passes = []
    for observation in observations:
        fields = {"reviewer_id", "provenance", "requested_model", "requested_effort",
                  "provider_verified", "report_locator", "report_sha256", "report_base64",
                  "foreign_exclusion", "clean_pass"}
        if (not isinstance(observation, dict) or set(observation) != fields
                or observation["reviewer_id"] not in reservation["reviewer_ids"]
                or observation["reviewer_id"] in observed_ids
                or observation["provenance"] != REVIEW_PROVENANCE
                or observation["requested_model"] != REVIEW_MODEL
                or observation["requested_effort"] != REVIEW_EFFORT
                or observation["provider_verified"] is not False
                or not isinstance(observation["report_locator"], str)
                or not re.fullmatch(r"[0-9a-f]{64}", observation["report_sha256"])):
            _fail("REVIEW_OBSERVATION_INVALID")
        try:
            report_raw = base64.b64decode(observation["report_base64"], validate=True)
        except (ValueError, TypeError):
            _fail("REVIEW_OBSERVATION_CORRUPT")
        if _digest(report_raw) != observation["report_sha256"]:
            _fail("REVIEW_OBSERVATION_CORRUPT")
        report = _loads_unique_json(report_raw, "NATIVE_REVIEW_REPORT_INVALID")
        clean = _validate_review_report(report_raw, report, manifest, observation["reviewer_id"])
        if observation["clean_pass"] is not clean:
            _fail("REVIEW_OBSERVATION_CORRUPT")
        observed_ids.append(observation["reviewer_id"])
        clean_passes.append(clean)

    has_rejection = any(not item for item in clean_passes)
    expected_review_state = ("REJECTED" if has_rejection else
                             "REVIEW_CONFIRMED" if len(clean_passes) == REVIEWER_COUNT else
                             "REVIEW_PENDING")
    if reservation.get("review_state") != expected_review_state:
        _fail("REVIEW_STATE_CORRUPT")
    if reservation.get("foreign_exclusions") != _review_exclusions(repo, reservation):
        _fail("REVIEW_EXCLUSION_BINDING_CHANGED")
    return observations


def prepare_review(repo: Path, *, candidate_commit: str, engine_root: Path,
                   instruction: bytes | str | dict[str, Any],
                   reviewer_ids: list[str]) -> dict[str, Any]:
    """Persist the exact owner intent and launch-ready review pins before dispatch."""
    owner_instruction = _instruction_record(instruction)
    if (not isinstance(reviewer_ids, list) or len(reviewer_ids) != REVIEWER_COUNT
            or any(not isinstance(item, str) or not item or item != item.strip()
                   for item in reviewer_ids)
            or len(set(reviewer_ids)) != REVIEWER_COUNT):
        _fail("TWO_DISTINCT_NATIVE_REVIEWERS_REQUIRED")
    engine = engine_root.resolve()
    prior = _read_reservation(repo)
    prior_exclusions: list[dict[str, Any]] = []
    if prior is not None:
        _validate_review_reservation(repo, prior)
        if prior.get("state") != "REJECTED":
            prior_manifest = prior.get("manifest", {})
            if (prior_manifest.get("candidate_engine", {}).get("commit") == candidate_commit
                    and Path(prior_manifest.get("candidate_engine", {}).get("root", "/invalid")).resolve() == engine
                    and prior.get("owner_instruction", {}).get("sha256") == owner_instruction["sha256"]
                    and prior.get("owner_instruction", {}).get("raw_base64") == owner_instruction["raw_base64"]
                    and prior.get("reviewer_ids") == reviewer_ids):
                _candidate_engine(engine, candidate_commit)
                return {"status": prior["review_state"], "operation_id": prior["operation_id"],
                        "manifest": prior["manifest"],
                        "manifest_sha256": prior["manifest_sha256"],
                        "owner_instruction_sha256": owner_instruction["sha256"],
                        "reviewer_ids": reviewer_ids, "launch_intent_recorded": True,
                        "launches_permitted": False, "writes_performed": False}
            _fail("OTHER_ACTIVATION_PENDING")
        if prior.get("manifest", {}).get("candidate_engine", {}).get("commit") == candidate_commit:
            _fail("REJECTED_CANDIDATE_CANNOT_BE_REVIEWED_AGAIN")
        prior_exclusions = _review_exclusions(repo, prior)

    # Network snapshots run outside the common writer lock. The local CAS below
    # ensures the pinned target state is still current before intent is saved.
    manifest = prepare_manifest(repo, candidate_commit=candidate_commit, engine_root=engine,
                                foreign_exclusions=prior_exclusions)
    for reviewer_id in reviewer_ids:
        if reviewer_id in {*manifest["author_ids"], manifest["owner"].get("task")}:
            _fail("REVIEWER_NOT_INDEPENDENT")
    reviewer_ids = list(reviewer_ids)
    manifest_sha = _digest(_json(manifest))
    operation_id = _review_operation_id(manifest_sha, owner_instruction["sha256"], reviewer_ids)
    fd = _lock(repo)
    try:
        if _read_reservation(repo) != prior:
            _fail("RESERVATION_CHANGED")
        _verify_target_snapshot(repo, manifest, allow_copied=False,
                                foreign_exclusions=prior_exclusions)
        history = []
        if prior is not None:
            if prior.get("operation_id") == operation_id:
                _validate_review_reservation(repo, prior)
                if (prior.get("manifest") != manifest
                        or prior.get("owner_instruction") != owner_instruction
                        or prior.get("reviewer_ids") != reviewer_ids):
                    _fail("REVIEW_OPERATION_BINDING_CHANGED")
                return {"status": prior["review_state"], "operation_id": operation_id,
                        "manifest": manifest, "manifest_sha256": manifest_sha,
                        "owner_instruction_sha256": owner_instruction["sha256"],
                        "reviewer_ids": reviewer_ids, "launch_intent_recorded": True,
                        "launches_permitted": False, "writes_performed": False}
            if prior.get("state") != "REJECTED" or prior.get("review_state") != "REJECTED":
                _fail("OTHER_ACTIVATION_PENDING")
            _validate_review_reservation(repo, prior)
            if prior.get("manifest_sha256") == manifest_sha:
                _fail("REJECTED_CANDIDATE_CANNOT_BE_REVIEWED_AGAIN")
            history = list(prior.get("history", []))
            history.append({key: value for key, value in prior.items() if key != "history"})
        reservation = {
            "schema": SCHEMA,
            "operation_id": operation_id,
            "state": "REVIEW_PENDING",
            "review_state": "REVIEW_PENDING",
            "manifest": manifest,
            "manifest_sha256": manifest_sha,
            "owner_instruction": owner_instruction,
            "reviewer_ids": reviewer_ids,
            "launch_intent": {"operation_id": operation_id,
                              "status": "RECORDED_BEFORE_SPAWN",
                              "manifest_sha256": manifest_sha,
                              "owner_instruction_sha256": owner_instruction["sha256"],
                              "reviewer_ids": reviewer_ids,
                              "preactivation_gate": manifest["preactivation_gate"],
                              "owner_sha256": _digest(_json(manifest["owner"])),
                              "base_head": manifest["base_head"],
                              "requested_model": REVIEW_MODEL,
                              "requested_effort": REVIEW_EFFORT},
            "review_observations": [],
            "history": history,
            "foreign_exclusions": prior_exclusions,
            "candidate_commit": None,
            "push_attempted": False,
        }
        _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
        _save_reservation(repo, reservation)
    finally:
        _unlock(fd)
    return {"status": "PREPARED_NOT_DISPATCHED", "operation_id": operation_id,
            "manifest": manifest, "manifest_sha256": manifest_sha,
            "owner_instruction_sha256": owner_instruction["sha256"],
            "owner_instruction_source": owner_instruction["source_locator"],
            "reviewer_ids": reviewer_ids, "launch_intent_recorded": True,
            "launches_permitted": True, "writes_performed": True}


def observe_review(repo: Path, *, operation_id: str, reviewer_id: str,
                   report_path: Path, expected_report_sha256: str) -> dict[str, Any]:
    """Store one exact reviewer report as root-observed, without provider attestation."""
    if not re.fullmatch(r"[0-9a-f]{64}", expected_report_sha256):
        _fail("REVIEW_HASH_INVALID")
    report_raw = report_path.read_bytes()
    if len(report_raw) > MAX_REPORT_BYTES or _digest(report_raw) != expected_report_sha256:
        _fail("REVIEW_HASH_MISMATCH")
    report = _loads_unique_json(report_raw, "NATIVE_REVIEW_REPORT_INVALID")
    fd = _lock(repo)
    try:
        reservation = _read_reservation(repo)
        if reservation is None or reservation.get("operation_id") != operation_id:
            _fail("REVIEW_RESERVATION_REQUIRED")
        _validate_review_reservation(repo, reservation)
        if reservation.get("review_state") != "REVIEW_PENDING":
            _fail("REVIEW_NOT_PENDING")
        if reviewer_id not in reservation["reviewer_ids"]:
            _fail("REVIEWER_NOT_RESERVED")
        _verify_environment_pins(
            repo, origin_sha256=reservation["manifest"]["origin_sha256"])
        for item in reservation["review_observations"]:
            if item["reviewer_id"] == reviewer_id:
                if item["report_sha256"] == expected_report_sha256:
                    return {"status": reservation["review_state"],
                            "operation_id": operation_id,
                            "reviewer_id": reviewer_id,
                            "report_sha256": expected_report_sha256,
                            "writes_performed": False}
                _fail("REVIEWER_ALREADY_OBSERVED")
        observation = _review_record(repo, report_raw, report, reservation["manifest"],
                                     reviewer_id, report_path)
        reservation["review_observations"].append(observation)
        reservation["foreign_exclusions"] = _review_exclusions(repo, reservation)
        if not observation["clean_pass"]:
            reservation["review_state"] = "REJECTED"
            reservation["state"] = "REJECTED"
        elif len(reservation["review_observations"]) == REVIEWER_COUNT:
            reservation["review_state"] = "REVIEW_CONFIRMED"
            reservation["state"] = "REVIEW_CONFIRMED"
        _validate_review_reservation(repo, reservation)
        _verify_environment_pins(repo, origin_sha256=reservation["manifest"]["origin_sha256"])
        _save_reservation(repo, reservation)
    finally:
        _unlock(fd)
    return {"status": reservation["review_state"], "operation_id": operation_id,
            "reviewer_id": reviewer_id, "report_sha256": expected_report_sha256,
            "observed_reviewers": [item["reviewer_id"] for item in reservation["review_observations"]],
            "provenance": REVIEW_PROVENANCE, "requested_model": REVIEW_MODEL,
            "requested_effort": REVIEW_EFFORT, "provider_verified": False,
            "writes_performed": True}


def _verify_target_snapshot(repo: Path, manifest: dict[str, Any], *, allow_copied: bool,
                            foreign_exclusions: list[dict[str, Any]] | None = None) -> None:
    _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
    head = _git(repo, "rev-parse", "HEAD").decode().strip()
    if head != manifest["base_head"]:
        _fail("LOCAL_HEAD_CHANGED")
    index = _index_snapshot(repo)
    if index != manifest["index"]:
        _fail("INDEX_CHANGED")
    if _foreign_snapshot(repo, foreign_exclusions) != manifest["foreign_sha256"]:
        _fail("FOREIGN_STATE_CHANGED")
    for row in manifest["files"]:
        path = repo / row["path"]
        actual = _read(path)
        mode = _mode(path)
        before = row["before_sha256"]
        after = row["sha256"]
        digest = None if actual is None else _digest(actual)
        mode_ok = ((digest is None and mode is None)
                   if before is None else
                   (digest == before and mode == row["before_mode"]))
        copied_ok = (digest == after and mode == row["mode"])
        if not mode_ok and not (allow_copied and copied_ok):
            _fail("DESTINATION_THIRD_STATE:" + row["path"])
    w = _w()
    raw = _read(repo / str(w.RESUME_PATH))
    history = _read(repo / str(w.RESUME_HISTORY_PATH))
    if (_digest(raw or b"") != manifest["local"]["resume_sha256"]
            or _digest(history or b"") != manifest["local"]["history_sha256"]):
        _fail("CHECKPOINT_OR_HISTORY_CHANGED")
    _verify_local_team_snapshot(repo, manifest)


def _tree_entry(repo: Path, commit: str, path: str) -> tuple[str, str] | None:
    entries = [entry for entry in _git(repo, "ls-tree", "-z", commit, "--", path).split(b"\0") if entry]
    if not entries:
        return None
    if len(entries) != 1:
        _fail("GIT_PATH_AMBIGUOUS:" + path)
    meta, found = entries[0].split(b"\t", 1)
    mode, kind, oid = meta.decode().split()
    if found.decode() != path or kind != "blob" or mode not in {"100644", "100755"}:
        _fail("GIT_MODE_INVALID:" + path)
    return mode, oid


def _verify_owned_index_recovery_state(repo: Path, manifest: dict[str, Any],
                                       candidate_commit: str) -> None:
    """Refuse to overwrite any non-baseline/non-candidate owned index stage."""
    for row in manifest["files"]:
        path = row["path"]
        worktree = _read(repo / path)
        if (worktree is None or _digest(worktree) != row["sha256"]
                or _mode(repo / path) != row["mode"]):
            _fail("COMMIT_WORKTREE_CANDIDATE_MISMATCH:" + path)

        allowed: set[tuple[str, str]] = set()
        candidate = _tree_entry(repo, candidate_commit, path)
        candidate_body, candidate_mode = _blob(repo, candidate_commit, path)
        if (candidate is None or candidate_body is None
                or _digest(candidate_body) != row["sha256"]
                or candidate_mode != row["mode"]):
            _fail("COMMIT_BLOB_MISMATCH:" + path)
        allowed.add(candidate)
        before = _tree_entry(repo, manifest["base_head"], path)
        if row["before_sha256"] is None:
            if before is not None:
                _fail("BASE_BLOB_MISMATCH:" + path)
        else:
            before_body, before_mode = _blob(repo, manifest["base_head"], path)
            if (before is None or before_body is None
                    or _digest(before_body) != row["before_sha256"]
                    or before_mode != row["before_mode"]):
                _fail("BASE_BLOB_MISMATCH:" + path)
            allowed.add(before)

        entries = []
        for entry in _git(repo, "ls-files", "--stage", "-z", "--", path).split(b"\0"):
            if not entry:
                continue
            metadata, found = entry.split(b"\t", 1)
            mode, oid, stage = metadata.decode().split()
            if found.decode() != path:
                _fail("OWNED_INDEX_STAGE_INVALID:" + path)
            entries.append((mode, oid, stage))
        if row["before_sha256"] is None and not entries:
            continue
        if (len(entries) != 1 or entries[0][2] != "0"
                or (entries[0][0], entries[0][1]) not in allowed):
            _fail("OWNED_INDEX_STAGE_INVALID:" + path)


def _recognized_commit(repo: Path, manifest: dict[str, Any],
                       foreign_exclusions: list[dict[str, Any]] | None = None) -> str | None:
    """Recognize the exact local commit if a crash preceded reservation update."""
    _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
    current = _git(repo, "rev-parse", "HEAD").decode().strip()
    if current == manifest["base_head"]:
        return None
    parent = _git(repo, "rev-parse", current + "^", check=False).decode().strip()
    if parent != manifest["base_head"]:
        _fail("COMMIT_RECOVERY_UNKNOWN")
    changed = _git(repo, "diff-tree", "--no-commit-id", "--name-only", "--no-renames", "-r", current).decode().splitlines()
    if changed != list(SOURCE_PATHS):
        _fail("COMMIT_SCOPE_MISMATCH")
    for row in manifest["files"]:
        body, mode = _blob(repo, current, row["path"])
        if body is None or _digest(body) != row["sha256"] or mode != row["mode"]:
            _fail("COMMIT_BLOB_MISMATCH:" + row["path"])
    _verify_owned_index_recovery_state(repo, manifest, current)
    if _index_snapshot(repo)["foreign_index_sha256"] != manifest["index"]["foreign_index_sha256"]:
        _fail("FOREIGN_INDEX_CHANGED")
    if _foreign_snapshot(repo, foreign_exclusions) != manifest["foreign_sha256"]:
        _fail("FOREIGN_STATE_CHANGED")
    _verify_local_team_snapshot(repo, manifest)
    w = _w()
    for relative, key in ((str(w.RESUME_PATH), "resume_sha256"),
                          (str(w.RESUME_HISTORY_PATH), "history_sha256")):
        body, _ = _blob(repo, current, relative)
        if body is None or _digest(body) != manifest["local"][key]:
            _fail("COMMIT_CHANGED_CHECKPOINT_OR_HISTORY")
    return current


def _copy_sources(repo: Path, reservation: dict[str, Any]) -> None:
    manifest = reservation["manifest"]
    engine = Path(manifest["candidate_engine"]["root"])
    commit = manifest["candidate_engine"]["commit"]
    _candidate_engine(engine, commit)
    exclusions = reservation.get("foreign_exclusions", [])
    _verify_target_snapshot(repo, manifest, allow_copied=True, foreign_exclusions=exclusions)
    for path in COPY_ORDER:
        _verify_target_snapshot(repo, manifest, allow_copied=True, foreign_exclusions=exclusions)
        row = next(item for item in manifest["files"] if item["path"] == path)
        current = _read(repo / path)
        if current is not None and _digest(current) == row["sha256"] and _mode(repo / path) == row["mode"]:
            if path == CONTROL_PATH:
                non_control = [r for r in manifest["files"] if r["path"] != CONTROL_PATH]
                if any(_digest(_read(repo / r["path"]) or b"") != r["sha256"] for r in non_control):
                    _fail("CONTROL_MUST_BE_COPIED_LAST")
            continue
        source, mode = _blob(engine, commit, path)
        if source is None or _digest(source) != row["sha256"] or mode != row["mode"]:
            _fail("CANDIDATE_SOURCE_CHANGED:" + path)
        _write_atomic(repo / path, source, mode)
        if _read(repo / path) != source or _mode(repo / path) != mode:
            _fail("COPY_READBACK_MISMATCH:" + path)
        if path == CONTROL_PATH:
            non_control = [r for r in manifest["files"] if r["path"] != CONTROL_PATH]
            if any(_digest(_read(repo / r["path"]) or b"") != r["sha256"] for r in non_control):
                _fail("CONTROL_MUST_BE_COPIED_LAST")


def _commit_snapshot(repo: Path, reservation: dict[str, Any]) -> str:
    manifest = reservation["manifest"]
    _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
    base = manifest["base_head"]
    current = _git(repo, "rev-parse", "HEAD").decode().strip()
    exclusions = reservation.get("foreign_exclusions", [])
    if current == base:
        _verify_target_snapshot(repo, manifest, allow_copied=True,
                                foreign_exclusions=exclusions)
        for row in manifest["files"]:
            if _digest(_read(repo / row["path"]) or b"") != row["sha256"]:
                _fail("COPY_INCOMPLETE")
        # Build the operation commit in an isolated index so untracked source
        # files are included without replacing or clearing any foreign stages.
        with tempfile.TemporaryDirectory(prefix="q3-control14-index-", dir=_common(repo)) as temp:
            alternate = Path(temp) / "index"
            env = os.environ.copy()
            env["GIT_INDEX_FILE"] = str(alternate)
            for args in (("read-tree", base), ("add", "--", *SOURCE_PATHS),
                         ("commit", "-m", "Activate reviewed Q3 control v14")):
                result = subprocess.run(["git", *args], cwd=repo, env=env,
                                        capture_output=True, timeout=45, check=False)
                if result.returncode:
                    _fail("GIT_OBSERVATION_FAILED:" + args[0])
        current = _git(repo, "rev-parse", "HEAD").decode().strip()
    if current == base or _git(repo, "rev-parse", current + "^", check=False).decode().strip() != base:
        _fail("COMMIT_RECOVERY_UNKNOWN")
    changed = _git(repo, "diff-tree", "--no-commit-id", "--name-only", "--no-renames", "-r", current).decode().splitlines()
    if changed != sorted(SOURCE_PATHS):
        _fail("COMMIT_SCOPE_MISMATCH")
    for row in manifest["files"]:
        body, mode = _blob(repo, current, row["path"])
        if body is None or _digest(body) != row["sha256"] or mode != row["mode"]:
            _fail("COMMIT_BLOB_MISMATCH:" + row["path"])
    _verify_owned_index_recovery_state(repo, manifest, current)
    if _index_snapshot(repo)["foreign_index_sha256"] != manifest["index"]["foreign_index_sha256"]:
        _fail("FOREIGN_INDEX_CHANGED")
    # If a crash followed commit creation, advance only the six owned index
    # entries on recovery; all foreign staged entries remain byte-for-byte data.
    for row in manifest["files"]:
        entries = [entry for entry in _git(repo, "ls-tree", "-z", current, "--",
                                           row["path"]).split(b"\0") if entry]
        if len(entries) != 1:
            _fail("COMMIT_BLOB_MISMATCH:" + row["path"])
        meta, found = entries[0].split(b"\t", 1)
        mode, kind, oid = meta.decode().split()
        if found.decode() != row["path"] or kind != "blob":
            _fail("COMMIT_BLOB_MISMATCH:" + row["path"])
        update = subprocess.run(["git", "update-index", "--add", "--cacheinfo",
                                 f"{mode},{oid},{row['path']}"], cwd=repo,
                                capture_output=True, timeout=45, check=False)
        if update.returncode:
            _fail("OWNED_INDEX_SYNC_FAILED:" + row["path"])
    if _git(repo, "show", current + ":" + str(_w().RESUME_PATH)) != _read(repo / str(_w().RESUME_PATH)):
        _fail("COMMIT_CHANGED_CHECKPOINT")
    if _git(repo, "show", current + ":" + str(_w().RESUME_HISTORY_PATH)) != _read(repo / str(_w().RESUME_HISTORY_PATH)):
        _fail("COMMIT_CHANGED_HISTORY")
    return current


def _readback(repo: Path, manifest: dict[str, Any], candidate_commit: str) -> bool:
    _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
    remote = _observe_remote(repo, origin_sha256=manifest["origin_sha256"])
    if remote["head"] != candidate_commit:
        return False
    if remote["resume_sha256"] != manifest["local"]["resume_sha256"] or remote["history_sha256"] != manifest["local"]["history_sha256"]:
        _fail("REMOTE_CHECKPOINT_OR_HISTORY_CHANGED")
    for row in manifest["files"]:
        body, mode = _blob(repo, candidate_commit, row["path"])
        if body is None or _digest(body) != row["sha256"] or mode != row["mode"]:
            _fail("REMOTE_BLOB_READBACK_MISMATCH:" + row["path"])
    return _pinned_remote_tip(repo, manifest) == candidate_commit


def activate(repo: Path, *, operation_id: str) -> dict[str, Any]:
    fd = _lock(repo)
    try:
        reservation = _read_reservation(repo)
        if reservation is None or reservation.get("operation_id") != operation_id:
            _fail("ACTIVATION_RESERVATION_REQUIRED")
        _validate_review_reservation(repo, reservation)
        if reservation.get("review_state") != "REVIEW_CONFIRMED":
            _fail("TWO_CLEAN_NATIVE_REVIEW_PASSES_REQUIRED")
        if reservation.get("state") == "REVIEW_CONFIRMED":
            manifest = reservation["manifest"]
            exclusions = _review_exclusions(repo, reservation)
            if exclusions != reservation.get("foreign_exclusions", []):
                _fail("REVIEW_RESERVATION_BINDING_CHANGED")
            engine = Path(manifest["candidate_engine"]["root"])
            _candidate_engine(engine, manifest["candidate_engine"]["commit"])
            _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
            if _manifest_snapshot(repo, engine, manifest["candidate_engine"]["commit"],
                                  exclusions) != manifest:
                _fail("PREIMAGE_OR_REMOTE_CHANGED")
            _verify_target_snapshot(repo, manifest, allow_copied=False,
                                    foreign_exclusions=exclusions)
            reservation["state"] = "PENDING"
            _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
            _save_reservation(repo, reservation)
        elif reservation.get("state") not in ACTIVATION_STATES:
            _fail("ACTIVATION_STATE_INVALID")
    finally:
        _unlock(fd)
    return _advance(repo, reservation)


def recover(repo: Path, *, operation_id: str) -> dict[str, Any]:
    fd = _lock(repo)
    try:
        reservation = _read_reservation(repo)
        if (reservation is None or reservation.get("operation_id") != operation_id
                or reservation.get("state") not in ACTIVATION_STATES):
            _fail("RECOVERY_RESERVATION_REQUIRED")
        if reservation.get("review_state") != "REVIEW_CONFIRMED":
            _fail("TWO_CLEAN_NATIVE_REVIEW_PASSES_REQUIRED")
        _validate_review_reservation(repo, reservation)
    finally:
        _unlock(fd)
    return _advance(repo, reservation)


def _advance(repo: Path, reservation: dict[str, Any]) -> dict[str, Any]:
    manifest = reservation["manifest"]
    _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
    _validate_manifest(manifest)
    _validate_review_reservation(repo, reservation)
    if (reservation.get("review_state") != "REVIEW_CONFIRMED"
            or reservation.get("state") not in ACTIVATION_STATES):
        _fail("TWO_CLEAN_NATIVE_REVIEW_PASSES_REQUIRED")
    exclusions = _review_exclusions(repo, reservation)
    if exclusions != reservation.get("foreign_exclusions", []):
        _fail("REVIEW_RESERVATION_BINDING_CHANGED")
    _verify_local_team_snapshot(repo, manifest)
    if reservation.get("state") == "CONFIRMED":
        if not reservation.get("candidate_commit") or not _readback(repo, manifest, reservation["candidate_commit"]):
            _fail("CONFIRMED_REMOTE_CHANGED")
        return {"status": "NOOP", "operation_id": reservation["operation_id"],
                "remote_commit": reservation["candidate_commit"], "writes_performed": False}
    if reservation.get("push_attempted"):
        candidate = reservation.get("candidate_commit")
        if candidate and _readback(repo, manifest, candidate):
            fd = _lock(repo)
            try:
                live = _read_reservation(repo)
                if live != reservation:
                    _fail("RESERVATION_CHANGED")
                _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
                reservation["state"] = "CONFIRMED"
                _save_reservation(repo, reservation)
            finally:
                _unlock(fd)
            return {"status": "CONFIRMED", "operation_id": reservation["operation_id"],
                    "remote_commit": candidate, "writes_performed": True}
        return {"status": "UNKNOWN", "operation_id": reservation["operation_id"],
                "writes_performed": False, "next": "inspect remote; never retry push"}
    if reservation.get("state") == "UNKNOWN":
        return {"status": "UNKNOWN", "operation_id": reservation["operation_id"],
                "writes_performed": False, "next": "inspect the recorded preimage; do not retry"}
    if _pinned_remote_tip(repo, manifest) != manifest["remote"]["head"]:
        fd = _lock(repo)
        try:
            current = _read_reservation(repo)
            if current != reservation:
                _fail("RESERVATION_CHANGED")
            _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
            reservation["state"] = "UNKNOWN"
            _save_reservation(repo, reservation)
        finally:
            _unlock(fd)
        return {"status": "UNKNOWN", "operation_id": reservation["operation_id"],
                "writes_performed": False, "next": "remote drift; inspect before any further action"}
    fd = _lock(repo)
    try:
        live = _read_reservation(repo)
        if live != reservation:
            _fail("RESERVATION_CHANGED")
        recognized = _recognized_commit(repo, manifest, reservation["foreign_exclusions"])
        if recognized is None:
            _copy_sources(repo, reservation)
            candidate = _commit_snapshot(repo, reservation)
        else:
            candidate = _commit_snapshot(repo, reservation)
        _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
        reservation["candidate_commit"] = candidate
        reservation["state"] = "PUSH_RESERVED"
        _save_reservation(repo, reservation)
    finally:
        _unlock(fd)
    # Reobserve before consuming the one push attempt. Non-force push protects
    # a race after this observation; a lost result is reconciled without retry.
    if _pinned_remote_tip(repo, manifest) != manifest["remote"]["head"]:
        return {"status": "UNKNOWN", "operation_id": reservation["operation_id"],
                "candidate_commit": candidate, "writes_performed": True,
                "next": "remote drift; inspect the named commit and remote"}
    fd = _lock(repo)
    try:
        live = _read_reservation(repo)
        if live != reservation:
            _fail("RESERVATION_CHANGED")
        _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
        reservation["push_attempted"] = True
        reservation["state"] = "PUSH_ATTEMPTED"
        _save_reservation(repo, reservation)
    finally:
        _unlock(fd)
    _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
    _git(repo, "push", "origin", candidate + ":" + BRANCH, check=False)
    if _readback(repo, manifest, candidate):
        _verify_local_team_snapshot(repo, manifest)
        fd = _lock(repo)
        try:
            live = _read_reservation(repo)
            if live != reservation:
                _fail("RESERVATION_CHANGED")
            _verify_environment_pins(repo, origin_sha256=manifest["origin_sha256"])
            reservation["state"] = "CONFIRMED"
            _save_reservation(repo, reservation)
        finally:
            _unlock(fd)
        return {"status": "CONFIRMED", "operation_id": reservation["operation_id"],
                "remote_commit": candidate, "writes_performed": True}
    return {"status": "UNKNOWN", "operation_id": reservation["operation_id"],
            "candidate_commit": candidate, "writes_performed": True,
            "next": "inspect remote; never retry push"}


CLI_SCHEMA = "q3_control14_activation_cli.v1"


class _JsonArgumentParser(argparse.ArgumentParser):
    def error(self, message: str) -> None:
        raise ValueError("CLI_ARGUMENTS:" + message)


def _cli_parser() -> argparse.ArgumentParser:
    parser = _JsonArgumentParser(description="Prepare and activate the reviewed Q3 control v14 candidate.")
    parser.add_argument("--root", type=Path, required=True,
                        help="canonical target checkout whose v13 FATAL preimage is pinned")
    commands = parser.add_subparsers(dest="command", required=True)

    prepare = commands.add_parser("prepare-review")
    prepare.add_argument("--candidate-commit", required=True)
    prepare.add_argument("--engine-root", type=Path, required=True)
    prepare.add_argument("--reviewer-id", action="append", required=True,
                         help="repeat exactly twice with distinct native Astra reviewer IDs")
    instruction = prepare.add_mutually_exclusive_group(required=True)
    instruction.add_argument("--owner-instruction")
    instruction.add_argument("--owner-instruction-file", type=Path)
    prepare.add_argument("--owner-instruction-sha256",
                         help="required with --owner-instruction-file; hash of exact file bytes")

    observe = commands.add_parser("observe-review")
    observe.add_argument("--operation-id", required=True)
    observe.add_argument("--reviewer-id", required=True)
    observe.add_argument("--report", type=Path, required=True)
    observe.add_argument("--expected-report-sha256", required=True)

    for name in ("activate", "recover"):
        command = commands.add_parser(name)
        command.add_argument("--operation-id", required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    """Run the durable activation procedure and emit one machine-readable JSON object."""
    command = None
    try:
        parser = _cli_parser()
        args = parser.parse_args(argv)
        command = args.command
        repo = args.root.resolve()
        if command == "prepare-review":
            if args.owner_instruction_file is not None:
                if args.owner_instruction_sha256 is None:
                    raise ValueError("OWNER_INSTRUCTION_FILE_HASH_REQUIRED")
                raw = args.owner_instruction_file.read_bytes()
                instruction: bytes | str | dict[str, Any] = {
                    "raw": raw,
                    "locator": str(args.owner_instruction_file.resolve()),
                    "expected_sha256": args.owner_instruction_sha256,
                }
            else:
                if args.owner_instruction_sha256 is not None:
                    raise ValueError("OWNER_INSTRUCTION_HASH_WITHOUT_FILE")
                # Preserve the exact argument contents. Do not strip or normalize it.
                instruction = args.owner_instruction
            result = prepare_review(repo, candidate_commit=args.candidate_commit,
                                    engine_root=args.engine_root, instruction=instruction,
                                    reviewer_ids=args.reviewer_id)
        elif command == "observe-review":
            result = observe_review(repo, operation_id=args.operation_id,
                                    reviewer_id=args.reviewer_id, report_path=args.report,
                                    expected_report_sha256=args.expected_report_sha256)
        elif command == "activate":
            result = activate(repo, operation_id=args.operation_id)
        elif command == "recover":
            result = recover(repo, operation_id=args.operation_id)
        else:
            raise ValueError("CLI_COMMAND_INVALID")
        payload = {"schema": CLI_SCHEMA, "command": command, **result}
        print(json.dumps(payload, ensure_ascii=False, sort_keys=True))
        return 2 if result.get("status") in {"FATAL", "REJECTED", "UNKNOWN"} else 0
    except SystemExit as exc:
        # argparse owns --help; failed parses are converted below to JSON.
        if exc.code == 0:
            return 0
        payload = {"schema": CLI_SCHEMA, "command": command, "status": "FATAL",
                   "error": "CLI_ARGUMENTS_INVALID", "writes_performed": False}
        print(json.dumps(payload, ensure_ascii=False, sort_keys=True))
        return 2
    except ValueError as exc:
        message = str(exc)
    except OSError as exc:
        message = "CLI_FILE_OR_REPOSITORY_ERROR:" + str(exc)
    except Exception as exc:
        from orchestrator.workflow_runtime import WorkflowRuntimeError
        if not isinstance(exc, WorkflowRuntimeError):
            raise
        message = str(exc)
    payload = {"schema": CLI_SCHEMA, "command": command, "status": "FATAL",
               "error": message, "writes_performed": False}
    print(json.dumps(payload, ensure_ascii=False, sort_keys=True))
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
