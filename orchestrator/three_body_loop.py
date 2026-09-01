#!/usr/bin/env python3
"""Control-v9 three-body runtime: quarantine, request CAS, and pinned launch.

The module deliberately separates three powers:

* source bytes may be written;
* the Lean kernel may accept them;
* an independent semantic auditor may admit them for a named scope.

The canonical tracked state is ``state/SEMANTIC_QUARANTINE.json``.  Mutable
request lifecycle files remain the task-specified ``CODEX_REQ_STATE_*.yaml``
objects.  All state transitions use a stable ``flock`` and atomic replacement.
No function in this module can mint its own semantic attestation or autonomy
lease: both require injected external authority resolvers.
"""

from __future__ import annotations

import argparse
import calendar
import contextlib
import fcntl
import hashlib
import json
import os
import re
import shlex
import socket
import stat
import subprocess
import sys
import tempfile
import time
import unicodedata
from collections.abc import Callable, Iterator, Mapping, Sequence
from pathlib import Path, PurePosixPath
from typing import Any, NoReturn

import yaml

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_STATE = REPO_ROOT / "orchestrator" / "state" / "SEMANTIC_QUARANTINE.json"
DEFAULT_WRITER_LOCK = REPO_ROOT / ".git" / "q3-three-body.writer.lock"
DEFAULT_READ_ONLY_WATCH_LOCK = REPO_ROOT / ".git" / "q3-three-body.watch-read-only.lock"
CONTROL_VERSION = 9

SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
GIT_OBJECT_RE = re.compile(r"^[0-9a-f]{40}$")
TOKEN_RE = re.compile(r"^[A-Z][A-Z0-9_.:-]{2,191}$")
SESSION_RE = re.compile(r"^[0-9a-f]{8}-[0-9a-f-]{27,35}$")

REQUEST_PAYLOAD_BEGIN = b"<!-- REQUEST_PAYLOAD_UTF8_BEGIN -->\n"
REQUEST_PAYLOAD_END = b"<!-- REQUEST_PAYLOAD_UTF8_END -->\n"

STATE_FIELDS = frozenset(
    {
        "schema",
        "control_version",
        "entries",
        "event_ledger",
        "tactical_repairs",
        "active_lease",
    }
)
QUARANTINE_ENTRY_FIELDS = frozenset(
    {
        "entry_id",
        "status",
        "task_path",
        "task_blob",
        "source_path",
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
        "hypothesis_provenance",
        "hypothesis_provenance_sha256",
        "semantic_attestation_id",
    }
)
HYPOTHESIS_COMMON_FIELDS = frozenset(
    {
        "hypothesis_id",
        "class",
        "source_or_supplier",
        "exact_type",
        "consumer",
        "production_inhabitant_or_plant",
    }
)
INHABITANT_OR_PLANT_FIELDS = frozenset(
    {
        "kind",
        "path",
        "blob",
        "declaration",
        "exact_type",
        "verifier",
        "scope",
    }
)
INHABITANT_OR_PLANT_KINDS = frozenset({"PRODUCTION_INHABITANT", "REACHABILITY_PLANT"})
HYPOTHESIS_FIELDS = {
    "SOURCE_FIELD": HYPOTHESIS_COMMON_FIELDS,
    "EXACT_FIT_SUPPLIER": HYPOTHESIS_COMMON_FIELDS | {"supplier_preflight_receipt_sha256"},
    "NEW_OPEN_OBLIGATION": HYPOTHESIS_COMMON_FIELDS | {"open_obligation_id"},
}
ATTESTATION_FIELDS = frozenset(
    {
        "schema",
        "attestation_id",
        "issuer",
        "status",
        "control_version",
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
    }
)
LEASE_FIELDS = frozenset(
    {
        "schema",
        "grant_id",
        "status",
        "control_version",
        "branch",
        "worktree",
        "writer_lock_holder",
        "phase_key_hash",
        "current_task_path",
        "current_task_blob",
        "allowed_paths",
        "activation_commit",
        "expires_at",
        "node_budget",
        "nodes_consumed",
        "revoked",
    }
)
LEASE_FORBIDDEN_PATHS = frozenset(
    {
        "AGENTS.md",
        "docs/CODEX_CONTROL.md",
        "docs/Codex/CURRENT.md",
        "docs/THREE_BODY_LOOP_DESIGN.md",
    }
)
EVENT_FIELDS = frozenset(
    {
        "run_id",
        "trigger_nonce",
        "source_event_commit",
        "answer_blob",
        "status",
        "child_identity",
        "failure",
    }
)
EVENT_STATUSES = frozenset({"RESERVED", "STARTED", "FAILED_BEFORE_LAUNCH"})
LOCK_RECORD_FIELDS = frozenset(
    {
        "schema",
        "worktree",
        "branch",
        "writer_body",
        "pid",
        "process_start_time",
        "boot_id",
        "codex_session_id",
        "task_path",
        "task_blob",
        "phase_key_hash",
        "base_head",
        "run_id",
        "trigger_nonce",
    }
)
CHILD_IDENTITY_FIELDS = frozenset(
    {
        "state",
        "run_id",
        "trigger_nonce",
        "pid",
        "process_start_time",
        "boot_id",
        "task_blob",
        "base_head",
        "lock_inode",
    }
)
TACTICAL_REPAIR_FIELDS = frozenset(
    {"repair_id", "task_blob", "source_commit", "attempts", "baseline"}
)
TACTICAL_BASELINE_FIELDS = frozenset(
    {
        "statement_sha256",
        "hypotheses_sha256",
        "imports_sha256",
        "definitions_sha256",
        "public_surface_sha256",
        "source_object_sha256",
        "consumer_sha256",
        "proof_body_ranges",
    }
)

REQUEST_FIELDS = frozenset(
    {
        "REQUEST_SCHEMA",
        "CODEX_REQ",
        "ELIGIBILITY",
        "CODEX_SESSION_ID",
        "PHASE_KEY_HASH",
        "BLOCKER_FINGERPRINT",
        "SOURCE_OBJECT",
        "TERMINAL_CONSUMER",
        "WALL",
        "TRIED",
        "ASK_SHELF_RECEIPT",
        "CHEAPEST_KILLER_RUN",
        "PROGRESS_DELTAS",
        "NEED",
        "BLOCKS",
        "REQUEST_BLOB",
        "SOURCE_COMMIT",
    }
)
REQUEST_STATE_FIELDS = frozenset(
    {
        "schema",
        "request_id",
        "request_blob",
        "request_git_blob",
        "request_introducing_commit",
        "phase_key_hash",
        "blocker_fingerprint",
        "codex_session_id",
        "status",
        "resolved_locally_after_claim",
        "revision",
        "previous_state_sha256",
    }
)
REQUEST_STATUSES = frozenset({"OPEN", "IN_REVIEW", "ANSWERED", "DROPPED"})
ANSWER_FIELDS = frozenset(
    {
        "ANSWER_SCHEMA_VERSION",
        "ANSWERS_REQ",
        "REQUEST_BLOB",
        "REQUEST_GIT_BLOB",
        "REQUEST_SOURCE_COMMIT",
        "PHASE_KEY_HASH",
        "BLOCKER_FINGERPRINT",
        "VERDICT_PATH",
        "VERDICT_BLOB",
        "DECISION",
        "NEXT_NODE",
        "FORBIDDEN",
    }
)


class ThreeBodyViolation(ValueError):
    """A fail-closed control-v9 violation."""

    def __init__(self, code: str, detail: str = "") -> None:
        super().__init__(f"{code}: {detail}" if detail else code)
        self.code = code
        self.detail = detail


def _fail(code: str, detail: str = "") -> NoReturn:
    raise ThreeBodyViolation(code, detail)


def _unique_json_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


class _UniqueKeyLoader(yaml.SafeLoader):
    pass


def _construct_unique_mapping(
    loader: _UniqueKeyLoader, node: yaml.nodes.MappingNode, deep: bool = False
) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node, deep=deep)
        if not isinstance(key, str) or key in result:
            raise yaml.constructor.ConstructorError(
                "while constructing a mapping",
                node.start_mark,
                f"duplicate or non-string key: {key!r}",
                key_node.start_mark,
            )
        result[key] = loader.construct_object(value_node, deep=deep)
    return result


_UniqueKeyLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, _construct_unique_mapping
)


def _load_unique_json_bytes(raw: bytes, *, code: str) -> dict[str, Any]:
    try:
        data = json.loads(raw.decode("utf-8"), object_pairs_hook=_unique_json_pairs)
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        _fail(code, str(exc))
    if not isinstance(data, dict):
        _fail(code, "top level is not an object")
    return data


def _load_unique_yaml_text(raw: str, *, code: str) -> dict[str, Any]:
    try:
        data = yaml.load(raw, Loader=_UniqueKeyLoader)
    except yaml.YAMLError as exc:
        _fail(code, str(exc))
    if not isinstance(data, dict):
        _fail(code, "top level is not a mapping")
    return data


def _canonical_json_bytes(value: object) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode(
        "utf-8"
    )


def _canonical_state_bytes(value: Mapping[str, Any]) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


SEMANTIC_ATTESTATION_SOCKET = Path("/run/q3-control-v9/semantic-attestation.sock")
SEMANTIC_ATTESTATION_QUERY_SCHEMA = "q3_semantic_attestation_query.v1"
SEMANTIC_ATTESTATION_ISSUER = "LINUX_INDEPENDENT_SEMANTIC_AUDITOR"
_SEMANTIC_ATTESTATION_TIMEOUT = 5.0
_SEMANTIC_ATTESTATION_MAX_BYTES = 262144

SIGNED_OFFLINE_BUNDLE_DIR = REPO_ROOT / "orchestrator" / "attestations" / "control-v9"
SIGNED_OFFLINE_ALLOWED_SIGNERS = Path(
    "/etc/q3-control-v9/semantic_attestation_allowed_signers"
)
SIGNED_OFFLINE_REVOCATIONS = Path(
    "/etc/q3-control-v9/semantic_attestation_revoked_ids.v1.json"
)
SIGNED_OFFLINE_SSH_KEYGEN = Path("/usr/bin/ssh-keygen")
SIGNED_OFFLINE_NAMESPACE = "q3-control-v9-semantic-attestation"
SIGNED_OFFLINE_PRINCIPAL = SEMANTIC_ATTESTATION_ISSUER
SIGNED_OFFLINE_TRUST_OWNER_UID = 0
SIGNED_OFFLINE_REVOCATION_FIELDS = frozenset({"schema", "revoked_attestation_ids"})
TRACKED_REVOCATIONS_FILENAME = "semantic_attestation_revoked_ids.v1.json"
_SIGNED_OFFLINE_SIGNATURE_MAX_BYTES = 65536
MAC_TRACKED_RECEIPT_FALLBACK_ENV = "Q3_CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK"
EXACT_OWNER_WAIVER_ENTRY_ID = (
    "GOAL058_D0PSTAR_SOURCE_EVEN_NONZERO_TAIL_CARRIER_20260831"
)
EXACT_OWNER_WAIVER_ATTESTATION_ID = (
    "OWNER_WAIVER_GOAL058_D0PSTAR_SOURCE_EVEN_NONZERO_TAIL_CARRIER_20260831_V1"
)
LOW_BAND_OWNER_WAIVER_ENTRY_ID = (
    "GOAL058_D0PSTAR_SOURCE_EVEN_NONZERO_LOW_BAND_ASSEMBLY_20260831"
)
LOW_BAND_OWNER_WAIVER_ATTESTATION_ID = (
    "OWNER_WAIVER_GOAL058_D0PSTAR_SOURCE_EVEN_NONZERO_LOW_BAND_ASSEMBLY_20260831_V1"
)
EXACT_OWNER_WAIVER_ISSUER = "OWNER_EXPLICIT_SEMANTIC_WAIVER"
EXACT_OWNER_WAIVERS = frozenset(
    {
        (EXACT_OWNER_WAIVER_ENTRY_ID, EXACT_OWNER_WAIVER_ATTESTATION_ID),
        (LOW_BAND_OWNER_WAIVER_ENTRY_ID, LOW_BAND_OWNER_WAIVER_ATTESTATION_ID),
    }
)
_MAC_TRACKED_RECEIPT_FALLBACK_CODES = frozenset(
    {
        "CONTROL_V9_OFFLINE_ATTESTATION_BUNDLE_MISSING",
        "CONTROL_V9_OFFLINE_ATTESTATION_TRUST_MISSING",
    }
)


def resolve_linux_semantic_attestation(
    attestation_id: str,
    *,
    socket_path: Path = SEMANTIC_ATTESTATION_SOCKET,
) -> dict[str, Any] | None:
    """Resolve one attestation through the fixed external broker socket.

    The transport is a fixed Unix-domain socket.  There is no shell
    invocation, no environment override and no caller-selected path: a caller
    can name an attestation ID and nothing else.  An unavailable broker
    resolves to ``None``, which makes admission fail closed.
    """
    if not isinstance(attestation_id, str) or not attestation_id:
        return None
    query = _canonical_json_bytes(
        {
            "schema": SEMANTIC_ATTESTATION_QUERY_SCHEMA,
            "attestation_id": attestation_id,
        }
    )
    try:
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
            client.settimeout(_SEMANTIC_ATTESTATION_TIMEOUT)
            client.connect(str(socket_path))
            client.sendall(query + b"\n")
            chunks: list[bytes] = []
            size = 0
            while True:
                chunk = client.recv(65536)
                if not chunk:
                    break
                chunks.append(chunk)
                size += len(chunk)
                if size > _SEMANTIC_ATTESTATION_MAX_BYTES:
                    return None
                if chunks[-1].endswith(b"\n"):
                    break
    except OSError:
        return None
    try:
        envelope = json.loads(b"".join(chunks))
    except ValueError:
        return None
    if not isinstance(envelope, dict):
        return None
    receipt = envelope.get("receipt")
    if receipt is None:
        return None
    if not isinstance(receipt, dict):
        return None
    return receipt


def _require_secure_trust_file(path: Path) -> bytes:
    code = "CONTROL_V9_OFFLINE_ATTESTATION_TRUST_INVALID"
    try:
        parent = path.parent.lstat()
        info = path.lstat()
    except FileNotFoundError as exc:
        _fail("CONTROL_V9_OFFLINE_ATTESTATION_TRUST_MISSING", str(exc))
    except OSError as exc:
        _fail(code, str(exc))
    if stat.S_ISLNK(parent.st_mode) or not stat.S_ISDIR(parent.st_mode):
        _fail(code, f"unsafe trust directory: {path.parent}")
    if parent.st_uid != SIGNED_OFFLINE_TRUST_OWNER_UID or parent.st_mode & 0o022:
        _fail(code, f"unsafe trust directory ownership or mode: {path.parent}")
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
        _fail(code, f"trust path is not a regular file: {path}")
    if info.st_uid != SIGNED_OFFLINE_TRUST_OWNER_UID or info.st_mode & 0o022:
        _fail(code, f"unsafe trust file ownership or mode: {path}")
    try:
        return path.read_bytes()
    except OSError as exc:
        _fail(code, str(exc))


def _validate_allowed_signers() -> None:
    code = "CONTROL_V9_OFFLINE_ATTESTATION_TRUST_INVALID"
    raw = _require_secure_trust_file(SIGNED_OFFLINE_ALLOWED_SIGNERS)
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        _fail(code, str(exc))
    active = [line.strip() for line in text.splitlines() if line.strip() and not line.lstrip().startswith("#")]
    if len(active) != 1:
        _fail(code, "allowed-signers must contain exactly one active line")
    try:
        fields = shlex.split(active[0], comments=True, posix=True)
    except ValueError as exc:
        _fail(code, str(exc))
    expected_namespace = f"namespaces={SIGNED_OFFLINE_NAMESPACE}"
    if (
        len(fields) < 4
        or fields[0] != SIGNED_OFFLINE_PRINCIPAL
        or fields[1] != expected_namespace
        or fields[2] != "ssh-ed25519"
        or not fields[3]
    ):
        _fail(code, "allowed-signers principal, namespace, or key type drift")


def _parse_attestation_revocations(
    raw: bytes, *, code: str, require_canonical: bool = False
) -> set[str]:
    data = _load_unique_json_bytes(raw, code=code)
    data = _require_exact_fields(
        data,
        SIGNED_OFFLINE_REVOCATION_FIELDS,
        code=code,
        label="offline attestation revocations",
    )
    if require_canonical and raw != _canonical_json_bytes(data) + b"\n":
        _fail(code, "revocation bytes are not canonical with one final LF")
    if data["schema"] != "q3_semantic_attestation_revocations.v1":
        _fail(code, "unsupported revocation schema")
    revoked = data["revoked_attestation_ids"]
    if not isinstance(revoked, list):
        _fail(code, "revoked_attestation_ids is not a list")
    if len(set(revoked)) != len(revoked):
        _fail(code, "duplicate revoked attestation ID")
    for attestation_id in revoked:
        if not isinstance(attestation_id, str) or TOKEN_RE.fullmatch(attestation_id) is None:
            _fail(code, "invalid revoked attestation ID")
    return set(revoked)


def _load_offline_revocations() -> set[str]:
    code = "CONTROL_V9_OFFLINE_ATTESTATION_TRUST_INVALID"
    raw = _require_secure_trust_file(SIGNED_OFFLINE_REVOCATIONS)
    return _parse_attestation_revocations(raw, code=code)


def _require_tracked_bundle_file(path: Path, *, max_bytes: int) -> bytes:
    missing_code = "CONTROL_V9_OFFLINE_ATTESTATION_BUNDLE_MISSING"
    invalid_code = "CONTROL_V9_OFFLINE_ATTESTATION_BUNDLE_INVALID"
    try:
        relative = path.relative_to(REPO_ROOT)
    except ValueError:
        _fail(invalid_code, f"bundle path escapes repository root: {path}")
    current = REPO_ROOT
    for part in relative.parts[:-1]:
        current /= part
        try:
            directory_info = current.lstat()
        except FileNotFoundError as exc:
            _fail(missing_code, str(exc))
        except OSError as exc:
            _fail(invalid_code, str(exc))
        if stat.S_ISLNK(directory_info.st_mode) or not stat.S_ISDIR(directory_info.st_mode):
            _fail(invalid_code, f"bundle directory is not a real directory: {current}")
    try:
        info = path.lstat()
    except FileNotFoundError as exc:
        _fail(missing_code, str(exc))
    except OSError as exc:
        _fail(invalid_code, str(exc))
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
        _fail(invalid_code, f"bundle path is not a regular file: {path}")
    if info.st_size > max_bytes:
        _fail(invalid_code, f"bundle file is too large: {path}")
    try:
        return path.read_bytes()
    except OSError as exc:
        _fail(invalid_code, str(exc))


def _load_tracked_revocations() -> set[str]:
    code = "CONTROL_V9_TRACKED_ATTESTATION_REVOCATIONS_INVALID"
    path = SIGNED_OFFLINE_BUNDLE_DIR / TRACKED_REVOCATIONS_FILENAME
    raw = _require_tracked_bundle_file(path, max_bytes=_SEMANTIC_ATTESTATION_MAX_BYTES)
    return _parse_attestation_revocations(raw, code=code, require_canonical=True)


def resolve_signed_offline_semantic_attestation(attestation_id: str) -> dict[str, Any]:
    """Resolve one auditor-signed receipt without a live Linux dependency."""
    if not isinstance(attestation_id, str) or TOKEN_RE.fullmatch(attestation_id) is None:
        _fail("CONTROL_V9_OFFLINE_ATTESTATION_RECEIPT_INVALID", "invalid attestation ID")

    receipt_path = SIGNED_OFFLINE_BUNDLE_DIR / f"{attestation_id}.receipt.json"
    signature_path = SIGNED_OFFLINE_BUNDLE_DIR / f"{attestation_id}.receipt.sshsig"
    raw = _require_tracked_bundle_file(
        receipt_path, max_bytes=_SEMANTIC_ATTESTATION_MAX_BYTES
    )
    _require_tracked_bundle_file(
        signature_path, max_bytes=_SIGNED_OFFLINE_SIGNATURE_MAX_BYTES
    )

    _validate_allowed_signers()
    revoked = _load_offline_revocations()
    try:
        verification = subprocess.run(
            [
                str(SIGNED_OFFLINE_SSH_KEYGEN),
                "-Y",
                "verify",
                "-f",
                str(SIGNED_OFFLINE_ALLOWED_SIGNERS),
                "-I",
                SIGNED_OFFLINE_PRINCIPAL,
                "-n",
                SIGNED_OFFLINE_NAMESPACE,
                "-s",
                str(signature_path),
            ],
            input=raw,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
            timeout=5,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        _fail("CONTROL_V9_OFFLINE_ATTESTATION_SIGNATURE_INVALID", str(exc))
    if verification.returncode != 0:
        _fail("CONTROL_V9_OFFLINE_ATTESTATION_SIGNATURE_INVALID", "SSHSIG verify failed")

    receipt = _load_unique_json_bytes(
        raw, code="CONTROL_V9_OFFLINE_ATTESTATION_RECEIPT_INVALID"
    )
    if raw != _canonical_json_bytes(receipt) + b"\n":
        _fail(
            "CONTROL_V9_OFFLINE_ATTESTATION_RECEIPT_INVALID",
            "receipt bytes are not canonical with one final LF",
        )
    if receipt.get("attestation_id") != attestation_id:
        _fail("CONTROL_V9_OFFLINE_ATTESTATION_RECEIPT_INVALID", "attestation ID drift")
    if attestation_id in revoked:
        _fail("CONTROL_V9_OFFLINE_ATTESTATION_ID_REVOKED", attestation_id)
    return receipt


def resolve_tracked_semantic_attestation(attestation_id: str) -> dict[str, Any]:
    """Validate one exact tracked receipt.

    This transport is used only by an explicit exact owner waiver or by the
    Darwin startup fallback for an already-admitted entry.  Merely placing a
    receipt in the tracked bundle never authorizes a transition.
    """
    if not isinstance(attestation_id, str) or TOKEN_RE.fullmatch(attestation_id) is None:
        _fail("SEMANTIC_ATTESTATION_INVALID", "invalid attestation ID")
    receipt_path = SIGNED_OFFLINE_BUNDLE_DIR / f"{attestation_id}.receipt.json"
    raw = _require_tracked_bundle_file(
        receipt_path, max_bytes=_SEMANTIC_ATTESTATION_MAX_BYTES
    )
    receipt = _load_unique_json_bytes(raw, code="SEMANTIC_ATTESTATION_INVALID")
    if raw != _canonical_json_bytes(receipt) + b"\n":
        _fail(
            "SEMANTIC_ATTESTATION_INVALID",
            "receipt bytes are not canonical with one final LF",
        )
    if receipt.get("attestation_id") != attestation_id:
        _fail("SEMANTIC_ATTESTATION_INVALID", "attestation ID drift")
    if attestation_id in _load_tracked_revocations():
        _fail("CONTROL_V9_OFFLINE_ATTESTATION_ID_REVOKED", attestation_id)
    return receipt


def _mac_tracked_receipt_fallback_enabled() -> bool:
    value = os.environ.get(MAC_TRACKED_RECEIPT_FALLBACK_ENV)
    if value in (None, "", "0"):
        return False
    if value == "1":
        return True
    _fail(
        "CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK_INVALID",
        f"{MAC_TRACKED_RECEIPT_FALLBACK_ENV} must be 0 or 1",
    )


def resolve_semantic_attestation(attestation_id: str) -> dict[str, Any] | None:
    """Use the primary host transport, with an explicit Mac startup fallback."""
    if any(attestation_id == waiver_id for _, waiver_id in EXACT_OWNER_WAIVERS):
        return resolve_tracked_semantic_attestation(attestation_id)
    if sys.platform == "darwin":
        try:
            return resolve_signed_offline_semantic_attestation(attestation_id)
        except ThreeBodyViolation as exc:
            if exc.code not in _MAC_TRACKED_RECEIPT_FALLBACK_CODES:
                raise
            if not _mac_tracked_receipt_fallback_enabled():
                raise
            return resolve_tracked_semantic_attestation(attestation_id)
    if sys.platform.startswith("linux"):
        return resolve_linux_semantic_attestation(attestation_id)
    _fail(
        "CONTROL_V9_OFFLINE_ATTESTATION_ALL_ENTRY_VALIDATION_FAILED",
        f"unsupported platform: {sys.platform}",
    )


def _require_semantic_attestation_issuer(
    *, entry: Mapping[str, Any], receipt: Mapping[str, Any], attestation_id: str, code: str
) -> str:
    issuer = receipt.get("issuer")
    reserved_owner_waiver_id = any(
        attestation_id == waiver_id for _, waiver_id in EXACT_OWNER_WAIVERS
    )
    if reserved_owner_waiver_id:
        if (
            issuer == EXACT_OWNER_WAIVER_ISSUER
            and (entry.get("entry_id"), attestation_id) in EXACT_OWNER_WAIVERS
        ):
            return issuer
        _fail(code, "reserved owner-waiver attestation ID is not bound to its exact pair")
    if issuer == SEMANTIC_ATTESTATION_ISSUER:
        return issuer
    _fail(code, "receipt issuer is not an allowed independent authority or exact owner waiver")


def _canonical_yaml_bytes(value: Mapping[str, Any]) -> bytes:
    return yaml.safe_dump(
        dict(value), allow_unicode=True, sort_keys=True, default_flow_style=False
    ).encode("utf-8")


def _git_blob_id(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw).hexdigest()


def _atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    tmp = Path(tmp_name)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(tmp, path)
        dir_fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(dir_fd)
        finally:
            os.close(dir_fd)
    finally:
        if tmp.exists():
            tmp.unlink()


def _require_exact_fields(
    value: object, fields: frozenset[str], *, code: str, label: str
) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != set(fields):
        actual = sorted(value) if isinstance(value, dict) else type(value).__name__
        _fail(code, f"{label} closed fields differ: {actual}")
    return value


def _require_token(value: object, *, code: str, field: str) -> str:
    if not isinstance(value, str) or TOKEN_RE.fullmatch(value) is None:
        _fail(code, f"invalid {field}")
    return value


def _require_hash(value: object, pattern: re.Pattern[str], *, code: str, field: str) -> str:
    if not isinstance(value, str) or pattern.fullmatch(value) is None:
        _fail(code, f"invalid {field}")
    return value


def _require_nfc_string(value: object, *, code: str, field: str) -> str:
    if (
        not isinstance(value, str)
        or not value.strip()
        or unicodedata.normalize("NFC", value) != value
    ):
        _fail(code, f"{field} must be nonempty NFC text")
    return value


def _require_string_list(
    value: object, *, code: str, field: str, allow_empty: bool = True
) -> list[str]:
    if (
        not isinstance(value, list)
        or (not allow_empty and not value)
        or any(not isinstance(item, str) or not item for item in value)
        or len(value) != len(set(value))
    ):
        _fail(code, f"invalid {field}")
    return value


def _canonical_repo_path(value: object, *, code: str, field: str) -> str:
    if not isinstance(value, str) or not value:
        _fail(code, f"invalid {field}")
    path = PurePosixPath(value)
    if (
        value == "."
        or path.is_absolute()
        or ".." in path.parts
        or "\\" in value
        or path.as_posix() != value
        or value.startswith("./")
    ):
        _fail(code, f"{field} is not canonical repo-relative path")
    return value


def canonical_hypothesis_provenance(
    records: object, *, opens: Sequence[str]
) -> tuple[list[dict[str, Any]], str]:
    """Validate and hash the closed hypothesis tagged union.

    Canonical form is UTF-8 JSON, no trailing newline, sorted object keys,
    compact separators, and entries sorted by immutable ASCII hypothesis ID.
    Non-NFC strings and duplicate IDs fail instead of being normalized silently.
    """
    code = "HYPOTHESIS_PROVENANCE_INVALID"
    if not isinstance(records, list):
        _fail(code, "hypothesis_provenance is not a list")
    validated: list[dict[str, Any]] = []
    ids: set[str] = set()
    for index, raw in enumerate(records):
        if not isinstance(raw, dict):
            _fail(code, f"entry {index} is not an object")
        class_name = raw.get("class")
        expected = HYPOTHESIS_FIELDS.get(class_name)
        if expected is None or set(raw) != set(expected):
            _fail(code, f"entry {index} is not a closed tagged-union variant")
        hypothesis_id = _require_token(
            raw.get("hypothesis_id"), code=code, field=f"entry {index} hypothesis_id"
        )
        if hypothesis_id in ids:
            _fail(code, f"duplicate hypothesis_id: {hypothesis_id}")
        ids.add(hypothesis_id)
        for field in HYPOTHESIS_COMMON_FIELDS - {
            "class",
            "hypothesis_id",
            "production_inhabitant_or_plant",
        }:
            _require_nfc_string(raw.get(field), code=code, field=f"{hypothesis_id}.{field}")
        inhabitant = _require_exact_fields(
            raw.get("production_inhabitant_or_plant"),
            INHABITANT_OR_PLANT_FIELDS,
            code=code,
            label=f"{hypothesis_id}.production_inhabitant_or_plant",
        )
        if inhabitant["kind"] not in INHABITANT_OR_PLANT_KINDS:
            _fail(code, f"{hypothesis_id}.production_inhabitant_or_plant has unknown kind")
        _canonical_repo_path(
            inhabitant["path"],
            code=code,
            field=f"{hypothesis_id}.production_inhabitant_or_plant.path",
        )
        _require_hash(
            inhabitant["blob"],
            GIT_OBJECT_RE,
            code=code,
            field=f"{hypothesis_id}.production_inhabitant_or_plant.blob",
        )
        for field in ("declaration", "exact_type", "verifier", "scope"):
            _require_nfc_string(
                inhabitant[field],
                code=code,
                field=f"{hypothesis_id}.production_inhabitant_or_plant.{field}",
            )
        if class_name == "EXACT_FIT_SUPPLIER":
            _require_hash(
                raw.get("supplier_preflight_receipt_sha256"),
                SHA256_RE,
                code=code,
                field=f"{hypothesis_id}.supplier_preflight_receipt_sha256",
            )
        if class_name == "NEW_OPEN_OBLIGATION":
            obligation = _require_token(
                raw.get("open_obligation_id"),
                code=code,
                field=f"{hypothesis_id}.open_obligation_id",
            )
            if obligation not in opens:
                _fail(code, f"{obligation} is absent from OPENS")
        record = dict(raw)
        record["production_inhabitant_or_plant"] = dict(inhabitant)
        validated.append(record)
    validated.sort(key=lambda item: item["hypothesis_id"])
    digest = hashlib.sha256(_canonical_json_bytes(validated)).hexdigest()
    return validated, digest


def _git_output(repo_root: Path, *args: str, code: str) -> bytes:
    result = subprocess.run(
        ["git", *args], cwd=repo_root, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    if result.returncode != 0:
        _fail(code, result.stderr.decode("utf-8", errors="replace").strip())
    return result.stdout


def _verify_committed_blob(
    *, repo_root: Path, commit: str, path: str, expected_blob: str, code: str
) -> None:
    actual = _git_output(repo_root, "rev-parse", f"{commit}:{path}", code=code)
    if actual.decode("ascii", errors="replace").strip() != expected_blob:
        _fail(code, f"{commit}:{path} blob mismatch")


def _require_ancestor(repo_root: Path, commit: str, *, code: str, field: str) -> None:
    result = subprocess.run(
        ["git", "merge-base", "--is-ancestor", commit, "HEAD"],
        cwd=repo_root,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    if result.returncode != 0:
        _fail(code, f"{field} is not an ancestor of HEAD")


def _validate_semantic_attestation(
    entry: dict[str, Any],
    *,
    resolver: Callable[[str], dict[str, Any] | None] | None,
    supplier_preflight_resolver: Callable[[str], str | None] | None,
) -> None:
    code = "SEMANTIC_ATTESTATION_INVALID"
    attestation_id = entry.get("semantic_attestation_id")
    if not isinstance(attestation_id, str) or not attestation_id:
        _fail(code, "SEMANTICALLY_ADMITTED entry lacks attestation ID")
    if resolver is None:
        _fail(code, "no independent semantic attestation resolver")
    try:
        receipt = resolver(attestation_id)
    except ThreeBodyViolation:
        raise
    except Exception as exc:
        _fail(code, f"semantic resolver failed: {exc}")
    receipt = _require_exact_fields(
        receipt, ATTESTATION_FIELDS, code=code, label="semantic attestation"
    )
    issuer = _require_semantic_attestation_issuer(
        entry=entry,
        receipt=receipt,
        attestation_id=attestation_id,
        code=code,
    )
    expected = {
        "schema": "q3_semantic_attestation.v1",
        "attestation_id": attestation_id,
        "issuer": issuer,
        "status": "ADMITTED",
        "control_version": CONTROL_VERSION,
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
    if receipt != expected:
        _fail(code, "semantic receipt is not byte-for-field bound to the entry")
    exact_suppliers = [
        row for row in entry["hypothesis_provenance"] if row["class"] == "EXACT_FIT_SUPPLIER"
    ]
    if exact_suppliers and supplier_preflight_resolver is None:
        _fail(code, "EXACT_FIT_SUPPLIER lacks supplier_preflight resolver")
    for row in exact_suppliers:
        try:
            resolved = supplier_preflight_resolver(row["source_or_supplier"])
        except Exception as exc:
            _fail(code, f"supplier_preflight resolver failed: {exc}")
        if resolved != row["supplier_preflight_receipt_sha256"]:
            _fail(code, f"supplier receipt mismatch for {row['hypothesis_id']}")


def _validate_quarantine_entry(
    raw: object,
    *,
    repo_root: Path,
    semantic_attestation_resolver: Callable[[str], dict[str, Any] | None] | None,
    supplier_preflight_resolver: Callable[[str], str | None] | None,
) -> dict[str, Any]:
    code = "SEMANTIC_QUARANTINE_STATE_INVALID"
    entry = _require_exact_fields(raw, QUARANTINE_ENTRY_FIELDS, code=code, label="quarantine entry")
    _require_token(entry["entry_id"], code=code, field="entry_id")
    if entry["status"] not in {"SOURCE_WRITTEN", "KERNEL_GREEN", "SEMANTICALLY_ADMITTED"}:
        _fail(code, "unknown admission status")
    for field in ("task_path", "source_path"):
        _canonical_repo_path(entry[field], code=code, field=field)
    for field in ("task_blob", "source_commit", "source_git_blob"):
        _require_hash(entry[field], GIT_OBJECT_RE, code=code, field=field)
    _require_ancestor(repo_root, entry["source_commit"], code=code, field="source_commit")
    _verify_committed_blob(
        repo_root=repo_root,
        commit=entry["source_commit"],
        path=entry["task_path"],
        expected_blob=entry["task_blob"],
        code=code,
    )
    _verify_committed_blob(
        repo_root=repo_root,
        commit=entry["source_commit"],
        path=entry["source_path"],
        expected_blob=entry["source_git_blob"],
        code=code,
    )
    for field in ("theorem_ids", "admitted_scope", "closes", "opens"):
        _require_string_list(
            entry[field],
            code=code,
            field=field,
            allow_empty=field in {"admitted_scope", "closes", "opens"},
        )
    for field in ("terminal_consumer", "normalization", "domain", "quantifiers"):
        _require_nfc_string(entry[field], code=code, field=field)
    canonical, digest = canonical_hypothesis_provenance(
        entry["hypothesis_provenance"], opens=entry["opens"]
    )
    if canonical != entry["hypothesis_provenance"]:
        _fail(code, "hypothesis_provenance is not in canonical ID order")
    if digest != entry["hypothesis_provenance_sha256"]:
        _fail(code, "hypothesis provenance digest mismatch")
    for row in canonical:
        inhabitant = row["production_inhabitant_or_plant"]
        _verify_committed_blob(
            repo_root=repo_root,
            commit=entry["source_commit"],
            path=inhabitant["path"],
            expected_blob=inhabitant["blob"],
            code="HYPOTHESIS_PROVENANCE_INVALID",
        )
    if entry["status"] == "SEMANTICALLY_ADMITTED":
        if not entry["admitted_scope"]:
            _fail(code, "semantic admission has empty scope")
        _validate_semantic_attestation(
            entry,
            resolver=semantic_attestation_resolver,
            supplier_preflight_resolver=supplier_preflight_resolver,
        )
    elif entry["semantic_attestation_id"] is not None:
        _fail(code, "pre-admission entry smuggles an attestation ID")
    return entry


def _validate_event(raw: object) -> dict[str, Any]:
    code = "THREE_BODY_EVENT_LEDGER_INVALID"
    event = _require_exact_fields(raw, EVENT_FIELDS, code=code, label="event")
    _require_token(event["run_id"], code=code, field="run_id")
    _require_token(event["trigger_nonce"], code=code, field="trigger_nonce")
    _require_hash(
        event["source_event_commit"],
        GIT_OBJECT_RE,
        code=code,
        field="source_event_commit",
    )
    _require_hash(event["answer_blob"], SHA256_RE, code=code, field="answer_blob")
    if event["status"] not in EVENT_STATUSES:
        _fail(code, "unknown event status")
    if event["status"] == "STARTED":
        _validate_child_identity(event["child_identity"], code=code)
    if event["status"] != "STARTED" and event["child_identity"] is not None:
        _fail(code, "non-STARTED event carries child identity")
    if event["failure"] is not None and not isinstance(event["failure"], str):
        _fail(code, "failure is not text or null")
    return event


def _validate_tactical_repair(raw: object) -> dict[str, Any]:
    code = "TACTICAL_REPAIR_STATE_INVALID"
    repair = _require_exact_fields(raw, TACTICAL_REPAIR_FIELDS, code=code, label="tactical repair")
    _require_token(repair["repair_id"], code=code, field="repair_id")
    _require_hash(repair["task_blob"], GIT_OBJECT_RE, code=code, field="task_blob")
    _require_hash(repair["source_commit"], GIT_OBJECT_RE, code=code, field="source_commit")
    if not isinstance(repair["attempts"], int) or isinstance(repair["attempts"], bool):
        _fail(code, "attempts is not an integer")
    if not 0 <= repair["attempts"] <= 2:
        _fail(code, "more than two tactical repair attempts")
    baseline = _require_exact_fields(
        repair["baseline"], TACTICAL_BASELINE_FIELDS, code=code, label="repair baseline"
    )
    for field in TACTICAL_BASELINE_FIELDS - {"proof_body_ranges"}:
        _require_hash(baseline[field], SHA256_RE, code=code, field=field)
    ranges = baseline["proof_body_ranges"]
    if (
        not isinstance(ranges, list)
        or not ranges
        or any(
            not isinstance(pair, list)
            or len(pair) != 2
            or any(not isinstance(value, int) or isinstance(value, bool) for value in pair)
            or pair[0] < 0
            or pair[1] <= pair[0]
            for pair in ranges
        )
    ):
        _fail(code, "invalid proof_body_ranges")
    return repair


def _validate_active_lease(
    raw: object,
    *,
    resolver: Callable[[str], dict[str, Any] | None] | None,
    repo_root: Path,
) -> dict[str, Any]:
    code = "CODEX_AUTONOMY_LEASE_INVALID"
    lease = _require_exact_fields(raw, LEASE_FIELDS, code=code, label="autonomy lease")
    grant_id = _require_token(lease["grant_id"], code=code, field="grant_id")
    if resolver is None:
        _fail(code, "active lease lacks external authority resolver")
    try:
        resolved = resolver(grant_id)
    except Exception as exc:
        _fail(code, f"lease resolver failed: {exc}")
    if resolved != lease:
        _fail(code, "lease is not identical to external authority record")
    if (
        lease["schema"] != "q3_codex_autonomy_lease.v1"
        or lease["status"] != "ACTIVE"
        or lease["control_version"] != CONTROL_VERSION
        or lease["writer_lock_holder"] != "CODEX"
        or lease["revoked"] is not False
    ):
        _fail(code, "inactive or misbound lease")
    for field in ("phase_key_hash",):
        _require_hash(lease[field], SHA256_RE, code=code, field=field)
    for field in ("current_task_blob", "activation_commit"):
        _require_hash(lease[field], GIT_OBJECT_RE, code=code, field=field)
    _canonical_repo_path(lease["current_task_path"], code=code, field="current_task_path")
    paths = _require_string_list(
        lease["allowed_paths"], code=code, field="allowed_paths", allow_empty=False
    )
    for path in paths:
        _canonical_repo_path(path, code=code, field="allowed_paths")
        if path == ".git" or path.startswith(".git/"):
            _fail(code, "lease includes git internals")
        if any(
            forbidden == path or forbidden.startswith(f"{path.rstrip('/')}/")
            for forbidden in LEASE_FORBIDDEN_PATHS
        ):
            _fail(code, "lease path contains a permanently forbidden path")
    if lease["worktree"] != str(repo_root.resolve()):
        _fail(code, "lease worktree mismatch")
    if not isinstance(lease["branch"], str) or not lease["branch"]:
        _fail(code, "lease branch missing")
    if (
        not isinstance(lease["node_budget"], int)
        or isinstance(lease["node_budget"], bool)
        or not isinstance(lease["nodes_consumed"], int)
        or isinstance(lease["nodes_consumed"], bool)
        or lease["node_budget"] <= 0
        or not 0 <= lease["nodes_consumed"] < lease["node_budget"]
    ):
        _fail(code, "lease node budget exhausted or invalid")
    try:
        expires = time.strptime(lease["expires_at"], "%Y-%m-%dT%H:%M:%SZ")
    except (TypeError, ValueError):
        _fail(code, "lease expiry is not UTC RFC3339 seconds")
    if calendar.timegm(expires) <= time.time():
        _fail(code, "lease expired")
    if _control_version(repo_root) != CONTROL_VERSION:
        _fail(code, "active control version changed")
    if _current_branch(repo_root) != lease["branch"]:
        _fail(code, "lease branch changed")
    if (
        _git_blob_for_worktree_path(repo_root, lease["current_task_path"])
        != lease["current_task_blob"]
    ):
        _fail(code, "lease current task pin changed")
    if _canonical_phase_hash(repo_root) != lease["phase_key_hash"]:
        _fail(code, "lease phase key changed")
    ancestor = subprocess.run(
        ["git", "merge-base", "--is-ancestor", lease["activation_commit"], "HEAD"],
        cwd=repo_root,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    if ancestor.returncode != 0:
        _fail(code, "lease activation commit is not an ancestor of HEAD")
    return lease


def validate_state(
    state: object,
    *,
    repo_root: Path = REPO_ROOT,
    semantic_attestation_resolver: Callable[[str], dict[str, Any] | None] | None = None,
    supplier_preflight_resolver: Callable[[str], str | None] | None = None,
    autonomy_lease_resolver: Callable[[str], dict[str, Any] | None] | None = None,
) -> dict[str, Any]:
    code = "SEMANTIC_QUARANTINE_STATE_INVALID"
    state = _require_exact_fields(state, STATE_FIELDS, code=code, label="quarantine state")
    if state["schema"] != "q3_semantic_quarantine.v1" or state["control_version"] != 9:
        _fail(code, "schema or control version mismatch")
    for field in ("entries", "event_ledger", "tactical_repairs"):
        if not isinstance(state[field], list):
            _fail(code, f"{field} is not a list")
    entries = []
    for row in state["entries"]:
        try:
            entries.append(
                _validate_quarantine_entry(
                    row,
                    repo_root=repo_root,
                    semantic_attestation_resolver=semantic_attestation_resolver,
                    supplier_preflight_resolver=supplier_preflight_resolver,
                )
            )
        except ThreeBodyViolation as exc:
            if (
                exc.code.startswith("CONTROL_V9_OFFLINE_ATTESTATION_")
                and exc.code
                != "CONTROL_V9_OFFLINE_ATTESTATION_ALL_ENTRY_VALIDATION_FAILED"
            ):
                entry_id = row.get("entry_id") if isinstance(row, dict) else "UNKNOWN"
                _fail(
                    "CONTROL_V9_OFFLINE_ATTESTATION_ALL_ENTRY_VALIDATION_FAILED",
                    f"{entry_id}: {exc.code}",
                )
            raise
    if len({row["entry_id"] for row in entries}) != len(entries):
        _fail(code, "duplicate quarantine entry ID")
    pending = [row for row in entries if row["status"] in {"SOURCE_WRITTEN", "KERNEL_GREEN"}]
    if len(pending) > 1:
        _fail("SEMANTIC_QUARANTINE_CAP_EXCEEDED", "more than one pending entry")
    events = [_validate_event(row) for row in state["event_ledger"]]
    event_keys = [(row["run_id"], row["trigger_nonce"]) for row in events]
    if len(event_keys) != len(set(event_keys)):
        _fail("THREE_BODY_EVENT_LEDGER_INVALID", "duplicate run/nonce event")
    repairs = [_validate_tactical_repair(row) for row in state["tactical_repairs"]]
    if len({row["repair_id"] for row in repairs}) != len(repairs):
        _fail("TACTICAL_REPAIR_STATE_INVALID", "duplicate repair ID")
    if state["active_lease"] is not None:
        _validate_active_lease(
            state["active_lease"], resolver=autonomy_lease_resolver, repo_root=repo_root
        )
    return state


def load_state(
    path: Path = DEFAULT_STATE,
    *,
    repo_root: Path = REPO_ROOT,
    semantic_attestation_resolver: Callable[[str], dict[str, Any] | None] | None = None,
    supplier_preflight_resolver: Callable[[str], str | None] | None = None,
    autonomy_lease_resolver: Callable[[str], dict[str, Any] | None] | None = None,
) -> dict[str, Any]:
    if not path.is_file():
        _fail("SEMANTIC_QUARANTINE_STATE_INVALID", f"missing state: {path}")
    state = _load_unique_json_bytes(path.read_bytes(), code="SEMANTIC_QUARANTINE_STATE_INVALID")
    return validate_state(
        state,
        repo_root=repo_root,
        semantic_attestation_resolver=semantic_attestation_resolver,
        supplier_preflight_resolver=supplier_preflight_resolver,
        autonomy_lease_resolver=autonomy_lease_resolver,
    )


def assert_no_quarantine_barrier(state: Mapping[str, Any]) -> None:
    pending = [
        row["entry_id"]
        for row in state["entries"]
        if row["status"] in {"SOURCE_WRITTEN", "KERNEL_GREEN"}
    ]
    if pending:
        _fail("SEMANTIC_QUARANTINE_ACTIVE", ",".join(pending))


def validate_repository_gate(
    *,
    repo_root: Path = REPO_ROOT,
    state_path: Path | None = None,
    require_dispatch_clear: bool = False,
    semantic_attestation_resolver: Callable[[str], dict[str, Any] | None] | None = (
        resolve_semantic_attestation
    ),
    supplier_preflight_resolver: Callable[[str], str | None] | None = None,
    autonomy_lease_resolver: Callable[[str], dict[str, Any] | None] | None = None,
) -> dict[str, Any]:
    path = state_path or repo_root / "orchestrator/state/SEMANTIC_QUARANTINE.json"
    state = load_state(
        path,
        repo_root=repo_root,
        semantic_attestation_resolver=semantic_attestation_resolver,
        supplier_preflight_resolver=supplier_preflight_resolver,
        autonomy_lease_resolver=autonomy_lease_resolver,
    )
    request_states: list[dict[str, Any]] = []
    request_root = repo_root / "docs" / "routeB_bus"
    if request_root.is_dir():
        request_state_paths = sorted(request_root.rglob("CODEX_REQ_STATE_*.yaml"))
        first_parent_commits = (
            _first_parent_commits(repo_root, code="CODEX_REQUEST_STATE_INVALID")
            if request_state_paths
            else ()
        )
        for request_state_path in request_state_paths:
            suffix = request_state_path.name.removeprefix("CODEX_REQ_STATE_").removesuffix(".yaml")
            request_path = request_state_path.with_name(f"CODEX_REQ_{suffix}.md")
            request_states.append(
                validate_request_file_binding(
                    request_path,
                    request_state_path,
                    repo_root=repo_root,
                    first_parent_commits=first_parent_commits,
                )
            )
    validate_request_open_set(request_states)
    if require_dispatch_clear:
        assert_no_quarantine_barrier(state)
    return state


def parse_request_body(raw: bytes) -> tuple[dict[str, Any], bytes]:
    code = "CODEX_REQUEST_INVALID"
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        _fail(code, str(exc))
    match = re.search(r"```yaml\s*\n(.*?)\n```", text, re.DOTALL)
    if match is None:
        _fail(code, "missing request YAML envelope")
    envelope = _load_unique_yaml_text(match.group(1), code=code)
    _require_exact_fields(envelope, REQUEST_FIELDS, code=code, label="request envelope")
    start = raw.find(REQUEST_PAYLOAD_BEGIN)
    end = raw.find(REQUEST_PAYLOAD_END)
    if start < 0 or end < 0 or end <= start:
        _fail(code, "missing exact REQUEST_PAYLOAD markers")
    payload_start = start + len(REQUEST_PAYLOAD_BEGIN)
    payload = raw[payload_start:end]
    if not payload or not payload.endswith(b"\n"):
        _fail(code, "REQUEST_PAYLOAD must be nonempty and end with one newline")
    if (
        raw.find(REQUEST_PAYLOAD_BEGIN, payload_start) >= 0
        or raw.find(REQUEST_PAYLOAD_END, end + len(REQUEST_PAYLOAD_END)) >= 0
    ):
        _fail(code, "multiple REQUEST_PAYLOAD blocks")
    expected_digest = hashlib.sha256(payload).hexdigest()
    if envelope["REQUEST_BLOB"] != expected_digest:
        _fail(code, "REQUEST_BLOB does not hash the exact payload preimage")
    if envelope["REQUEST_SCHEMA"] != "q3_codex_request.v1":
        _fail(code, "unsupported request schema")
    _require_token(envelope["CODEX_REQ"], code=code, field="CODEX_REQ")
    if (
        not isinstance(envelope["CODEX_SESSION_ID"], str)
        or SESSION_RE.fullmatch(envelope["CODEX_SESSION_ID"]) is None
    ):
        _fail(code, "invalid CODEX_SESSION_ID")
    for field in ("PHASE_KEY_HASH", "BLOCKER_FINGERPRINT", "REQUEST_BLOB"):
        _require_hash(envelope[field], SHA256_RE, code=code, field=field)
    _require_hash(envelope["SOURCE_COMMIT"], GIT_OBJECT_RE, code=code, field="SOURCE_COMMIT")
    for field in ("SOURCE_OBJECT", "TERMINAL_CONSUMER", "WALL", "NEED", "BLOCKS"):
        _require_nfc_string(envelope[field], code=code, field=field)
    if not isinstance(envelope["TRIED"], list) or not envelope["TRIED"]:
        _fail(code, "TRIED must be a nonempty list")
    if not isinstance(envelope["PROGRESS_DELTAS"], list):
        _fail(code, "PROGRESS_DELTAS must be a list")
    if not envelope["ASK_SHELF_RECEIPT"] or not envelope["CHEAPEST_KILLER_RUN"]:
        _fail(code, "shelf receipt and cheapest killer are mandatory")
    eligibility = envelope["ELIGIBILITY"]
    if eligibility not in {"FATAL", "HARD_STALL", "OPERATIVE_REVIEW_GATE"}:
        _fail(code, "request is outside the closed eligibility classes")
    if eligibility == "HARD_STALL":
        deltas = envelope["PROGRESS_DELTAS"]
        if len(deltas) != 6 or any(
            not isinstance(row, dict)
            or row.get("result") != "NO_VALIDATED_DELTA"
            or row.get("blocker_fingerprint") != envelope["BLOCKER_FINGERPRINT"]
            for row in deltas
        ):
            _fail(code, "HARD_STALL lacks six same-fingerprint no-delta cycles")
    return envelope, payload


def validate_request_state(raw: object) -> dict[str, Any]:
    code = "CODEX_REQUEST_STATE_INVALID"
    state = _require_exact_fields(raw, REQUEST_STATE_FIELDS, code=code, label="request state")
    if state["schema"] != "q3_codex_request_state.v1":
        _fail(code, "unsupported request state schema")
    _require_token(state["request_id"], code=code, field="request_id")
    for field in ("request_blob", "phase_key_hash", "blocker_fingerprint"):
        _require_hash(state[field], SHA256_RE, code=code, field=field)
    for field in ("request_git_blob", "request_introducing_commit"):
        _require_hash(state[field], GIT_OBJECT_RE, code=code, field=field)
    if (
        not isinstance(state["codex_session_id"], str)
        or SESSION_RE.fullmatch(state["codex_session_id"]) is None
    ):
        _fail(code, "invalid codex_session_id")
    if state["status"] not in REQUEST_STATUSES:
        _fail(code, "unknown request status")
    if not isinstance(state["resolved_locally_after_claim"], bool):
        _fail(code, "resolved_locally_after_claim is not boolean")
    if state["status"] not in {"IN_REVIEW", "ANSWERED"} and state["resolved_locally_after_claim"]:
        _fail(code, "local-after-claim flag outside IN_REVIEW")
    if (
        not isinstance(state["revision"], int)
        or isinstance(state["revision"], bool)
        or state["revision"] < 0
    ):
        _fail(code, "invalid revision")
    previous = state["previous_state_sha256"]
    if previous is not None:
        _require_hash(previous, SHA256_RE, code=code, field="previous_state_sha256")
    return state


def validate_request_state_binding(request: Mapping[str, Any], state: Mapping[str, Any]) -> None:
    code = "CODEX_REQUEST_STATE_INVALID"
    expected = {
        "request_id": request["CODEX_REQ"],
        "request_blob": request["REQUEST_BLOB"],
        "phase_key_hash": request["PHASE_KEY_HASH"],
        "blocker_fingerprint": request["BLOCKER_FINGERPRINT"],
        "codex_session_id": request["CODEX_SESSION_ID"],
    }
    drift = sorted(field for field, value in expected.items() if state[field] != value)
    if drift:
        _fail(code, f"request/state identity drift: {','.join(drift)}")


def validate_request_open_set(states: Sequence[object]) -> list[dict[str, Any]]:
    """Enforce one active request per phase/blocker and per living session."""
    code = "CODEX_REQUEST_STATE_INVALID"
    validated = [validate_request_state(state) for state in states]
    if len({state["request_id"] for state in validated}) != len(validated):
        _fail(code, "duplicate request state ID")
    active = [state for state in validated if state["status"] in {"OPEN", "IN_REVIEW"}]
    phase_blockers = [(state["phase_key_hash"], state["blocker_fingerprint"]) for state in active]
    if len(phase_blockers) != len(set(phase_blockers)):
        _fail(code, "more than one active request for a phase/blocker")
    sessions = [state["codex_session_id"] for state in active]
    if len(sessions) != len(set(sessions)):
        _fail(code, "more than one outstanding request for a Codex session")
    return validated


def _first_parent_commits(repo_root: Path, *, code: str) -> tuple[str, ...]:
    """Return the exact first-parent history once for one repository gate run."""
    try:
        commits = tuple(
            _git_output(
                repo_root,
                "rev-list",
                "--first-parent",
                "--reverse",
                "HEAD",
                code=code,
            )
            .decode("ascii")
            .splitlines()
        )
    except UnicodeDecodeError as exc:
        _fail(code, f"first-parent history is not ASCII: {exc}")
    if not commits or any(GIT_OBJECT_RE.fullmatch(commit) is None for commit in commits):
        _fail(code, "first-parent history is empty or malformed")
    return commits


def _first_commit_with_blob(
    *,
    repo_root: Path,
    commits: Sequence[str],
    path: str,
    expected_blob: str,
    code: str,
) -> str | None:
    """Find the first commit whose exact path has ``expected_blob`` in one Git batch.

    The former implementation spawned ``git rev-parse`` once for every commit.
    ``cat-file --batch-check`` asks the same treeish:path questions through one
    Git process, preserving first-parent order, merge states, deletions, and
    blob reappearance semantics.
    """
    if not commits:
        return None
    if "\n" in path or "\r" in path:
        _fail(code, "request path contains a batch-protocol line break")
    queries = "".join(f"{commit}:{path}\n" for commit in commits)
    result = subprocess.run(
        ["git", "cat-file", "--batch-check=%(objectname)"],
        cwd=repo_root,
        input=queries,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if result.returncode != 0:
        _fail(code, f"batched request-history lookup failed: {result.stderr.strip()}")
    rows = result.stdout.splitlines()
    if len(rows) != len(commits):
        _fail(code, "batched request-history lookup returned the wrong row count")
    for commit, row in zip(commits, rows, strict=True):
        if row == expected_blob:
            return commit
    return None


def validate_request_file_binding(
    request_path: Path,
    state_path: Path,
    *,
    repo_root: Path,
    first_parent_commits: Sequence[str] | None = None,
) -> dict[str, Any]:
    code = "CODEX_REQUEST_STATE_INVALID"
    try:
        request_relative = request_path.resolve().relative_to(repo_root.resolve()).as_posix()
        state_path.resolve().relative_to(repo_root.resolve())
        request_raw = request_path.read_bytes()
        state_raw = state_path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError, ValueError) as exc:
        _fail(code, str(exc))
    request, _payload = parse_request_body(request_raw)
    state = validate_request_state(_load_unique_yaml_text(state_raw, code=code))
    validate_request_state_binding(request, state)
    if _git_blob_id(request_raw) != state["request_git_blob"]:
        _fail(code, "request_git_blob does not hash the complete request")
    _verify_committed_blob(
        repo_root=repo_root,
        commit="HEAD",
        path=request_relative,
        expected_blob=state["request_git_blob"],
        code=code,
    )
    _require_ancestor(
        repo_root,
        request["SOURCE_COMMIT"],
        code=code,
        field="SOURCE_COMMIT",
    )
    commits = first_parent_commits
    if commits is None:
        commits = _first_parent_commits(repo_root, code=code)
    first_commit = _first_commit_with_blob(
        repo_root=repo_root,
        commits=commits,
        path=request_relative,
        expected_blob=state["request_git_blob"],
        code=code,
    )
    if first_commit != state["request_introducing_commit"]:
        _fail(code, "request_introducing_commit is not the first canonical appearance")
    return state


@contextlib.contextmanager
def _plain_flock(path: Path, *, blocking: bool = True) -> Iterator[int]:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)
    flags = fcntl.LOCK_EX | (0 if blocking else fcntl.LOCK_NB)
    try:
        fcntl.flock(fd, flags)
    except Exception:
        os.close(fd)
        raise
    try:
        yield fd
    finally:
        fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def cas_transition_request_state(
    path: Path,
    *,
    expected_state_sha256: str,
    target_status: str,
    lock_path: Path,
    resolved_locally_after_claim: bool | None = None,
) -> dict[str, Any]:
    code = "CODEX_REQUEST_STATE_CAS_CONFLICT"
    _require_hash(expected_state_sha256, SHA256_RE, code=code, field="expected_state_sha256")
    with _plain_flock(lock_path):
        raw = path.read_bytes()
        actual = hashlib.sha256(raw).hexdigest()
        if actual != expected_state_sha256:
            _fail(code, f"expected {expected_state_sha256}, found {actual}")
        current = validate_request_state(
            _load_unique_yaml_text(raw.decode("utf-8"), code="CODEX_REQUEST_STATE_INVALID")
        )
        legal = {
            "OPEN": {"IN_REVIEW", "DROPPED"},
            "IN_REVIEW": {"ANSWERED"},
            "ANSWERED": set(),
            "DROPPED": set(),
        }
        same_status_resolution = (
            current["status"] == "IN_REVIEW"
            and target_status == "IN_REVIEW"
            and resolved_locally_after_claim is True
            and not current["resolved_locally_after_claim"]
        )
        if target_status not in legal[current["status"]] and not same_status_resolution:
            _fail("CODEX_REQUEST_STATE_TRANSITION_INVALID", f"{current['status']}->{target_status}")
        if resolved_locally_after_claim is True and target_status != "IN_REVIEW":
            _fail(
                "CODEX_REQUEST_STATE_TRANSITION_INVALID",
                "RESOLVED_LOCALLY_AFTER_CLAIM is an IN_REVIEW annotation",
            )
        updated = dict(current)
        updated["status"] = target_status
        if target_status == "ANSWERED":
            updated["resolved_locally_after_claim"] = current["resolved_locally_after_claim"]
        else:
            updated["resolved_locally_after_claim"] = resolved_locally_after_claim is True
        updated["revision"] += 1
        updated["previous_state_sha256"] = actual
        validate_request_state(updated)
        peer_states: list[dict[str, Any]] = []
        for peer_path in sorted(path.parent.glob("CODEX_REQ_STATE_*.yaml")):
            if peer_path.resolve() == path.resolve():
                continue
            peer_states.append(
                validate_request_state(
                    _load_unique_yaml_text(
                        peer_path.read_text(encoding="utf-8"),
                        code="CODEX_REQUEST_STATE_INVALID",
                    )
                )
            )
        validate_request_open_set([*peer_states, updated])
        _atomic_write(path, _canonical_yaml_bytes(updated))
        return updated


def validate_answer_binding(
    request_raw: bytes,
    request_state: object,
    answer_raw: bytes,
    *,
    repo_root: Path,
) -> dict[str, Any]:
    code = "CODEX_ANSWER_BINDING_INVALID"
    request, _payload = parse_request_body(request_raw)
    state = validate_request_state(request_state)
    validate_request_state_binding(request, state)
    request_git_blob = _git_blob_id(request_raw)
    if state["request_git_blob"] != request_git_blob:
        _fail(code, "state request Git blob does not bind the complete request bytes")
    if state["status"] not in {"IN_REVIEW", "ANSWERED"}:
        _fail(code, "answer is not bound to an in-review request")
    try:
        answer_text = answer_raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        _fail(code, str(exc))
    match = re.search(r"```yaml\s*\n(.*?)\n```", answer_text, re.DOTALL)
    if match is None:
        _fail(code, "missing answer YAML envelope")
    answer = _load_unique_yaml_text(match.group(1), code=code)
    _require_exact_fields(answer, ANSWER_FIELDS, code=code, label="answer envelope")
    expected = {
        "ANSWER_SCHEMA_VERSION": "q3_codex_answer.v1",
        "ANSWERS_REQ": request["CODEX_REQ"],
        "REQUEST_BLOB": request["REQUEST_BLOB"],
        "REQUEST_GIT_BLOB": state["request_git_blob"],
        "REQUEST_SOURCE_COMMIT": state["request_introducing_commit"],
        "PHASE_KEY_HASH": request["PHASE_KEY_HASH"],
        "BLOCKER_FINGERPRINT": request["BLOCKER_FINGERPRINT"],
    }
    if any(answer.get(key) != value for key, value in expected.items()):
        _fail(code, "answer request identity drift")
    verdict_path = _canonical_repo_path(answer["VERDICT_PATH"], code=code, field="VERDICT_PATH")
    verdict_blob = _require_hash(
        answer["VERDICT_BLOB"], GIT_OBJECT_RE, code=code, field="VERDICT_BLOB"
    )
    _verify_committed_blob(
        repo_root=repo_root,
        commit="HEAD",
        path=verdict_path,
        expected_blob=verdict_blob,
        code=code,
    )
    for field in ("DECISION", "NEXT_NODE"):
        _require_nfc_string(answer[field], code=code, field=field)
    _require_string_list(answer["FORBIDDEN"], code=code, field="FORBIDDEN")
    return answer


def first_parent_request_order(
    requests: Sequence[Mapping[str, str]], *, repo_root: Path
) -> list[dict[str, str]]:
    code = "CODEX_REQUEST_FIFO_INVALID"
    commits = (
        _git_output(repo_root, "rev-list", "--first-parent", "--reverse", "HEAD", code=code)
        .decode("ascii")
        .splitlines()
    )
    order: list[tuple[int, str, str, dict[str, str]]] = []
    for request in requests:
        path = _canonical_repo_path(request.get("path"), code=code, field="path")
        request_id = _require_token(request.get("request_id"), code=code, field="request_id")
        blob = _require_hash(
            request.get("request_git_blob"), GIT_OBJECT_RE, code=code, field="request_git_blob"
        )
        first_index: int | None = None
        for index, commit in enumerate(commits):
            result = subprocess.run(
                ["git", "rev-parse", f"{commit}:{path}"],
                cwd=repo_root,
                stdout=subprocess.PIPE,
                stderr=subprocess.DEVNULL,
                text=True,
            )
            if result.returncode == 0 and result.stdout.strip() == blob:
                first_index = index
                break
        if first_index is None:
            _fail(code, f"request is absent from canonical first-parent history: {path}")
        order.append((first_index, path, request_id, dict(request)))
    order.sort(key=lambda row: (row[0], row[1], row[2]))
    return [row[3] for row in order]


def record_tactical_repair_attempt(
    state_path: Path,
    *,
    repair_id: str,
    task_blob: str,
    source_commit: str,
    baseline: Mapping[str, Any],
    lock_path: Path,
) -> dict[str, Any]:
    with _plain_flock(lock_path):
        state = load_state(
            state_path,
            repo_root=state_path.parents[2],
            semantic_attestation_resolver=resolve_semantic_attestation,
        )
        matches = [row for row in state["tactical_repairs"] if row["repair_id"] == repair_id]
        if matches:
            repair = matches[0]
            if (
                repair["task_blob"] != task_blob
                or repair["source_commit"] != source_commit
                or repair["baseline"] != dict(baseline)
            ):
                _fail("TACTICAL_REPAIR_BASELINE_DRIFT")
        else:
            repair = {
                "repair_id": repair_id,
                "task_blob": task_blob,
                "source_commit": source_commit,
                "attempts": 0,
                "baseline": dict(baseline),
            }
            _validate_tactical_repair(repair)
            state["tactical_repairs"].append(repair)
        if repair["attempts"] >= 2:
            _fail("TACTICAL_REPAIR_BUDGET_EXHAUSTED")
        repair["attempts"] += 1
        _validate_tactical_repair(repair)
        _atomic_write(state_path, _canonical_state_bytes(state))
        return repair


def validate_tactical_repair_candidate(
    baseline: Mapping[str, Any], candidate: Mapping[str, Any]
) -> None:
    code = "TACTICAL_REPAIR_SURFACE_DRIFT"
    _require_exact_fields(baseline, TACTICAL_BASELINE_FIELDS, code=code, label="repair baseline")
    _require_exact_fields(candidate, TACTICAL_BASELINE_FIELDS, code=code, label="repair candidate")
    protected = TACTICAL_BASELINE_FIELDS - {"proof_body_ranges"}
    changed = sorted(field for field in protected if baseline[field] != candidate[field])
    if changed or baseline["proof_body_ranges"] != candidate["proof_body_ranges"]:
        _fail(code, ",".join(changed) or "proof_body_ranges")


def _boot_id() -> str:
    try:
        return Path("/proc/sys/kernel/random/boot_id").read_text(encoding="ascii").strip()
    except OSError:
        pass
    if sys.platform == "darwin":
        try:
            result = subprocess.run(
                ["/usr/sbin/sysctl", "-n", "kern.boottime"],
                check=False,
                capture_output=True,
                text=True,
                encoding="ascii",
                timeout=2,
            )
        except (OSError, subprocess.SubprocessError) as exc:
            _fail("WRITER_LOCK_IDENTITY_INVALID", str(exc))
        value = result.stdout.strip()
        if result.returncode != 0 or not value:
            _fail("WRITER_LOCK_IDENTITY_INVALID", "cannot read Darwin boot time")
        return f"darwin-{hashlib.sha256(value.encode('ascii')).hexdigest()}"
    _fail("WRITER_LOCK_IDENTITY_INVALID", "cannot read host boot identity")


def _process_start_time(pid: int) -> str:
    try:
        raw = Path(f"/proc/{pid}/stat").read_text(encoding="ascii")
    except OSError:
        raw = ""
    if not raw and sys.platform == "darwin":
        env = os.environ.copy()
        env["LC_ALL"] = "C"
        try:
            result = subprocess.run(
                ["/bin/ps", "-o", "lstart=", "-p", str(pid)],
                check=False,
                capture_output=True,
                text=True,
                encoding="ascii",
                env=env,
                timeout=2,
            )
        except (OSError, subprocess.SubprocessError) as exc:
            _fail("WRITER_LOCK_IDENTITY_INVALID", str(exc))
        value = result.stdout.strip()
        if result.returncode != 0 or not value:
            _fail("WRITER_LOCK_IDENTITY_INVALID", f"cannot read Darwin process {pid}")
        return f"darwin-{hashlib.sha256(value.encode('ascii')).hexdigest()}"
    if not raw:
        _fail("WRITER_LOCK_IDENTITY_INVALID", f"cannot read /proc/{pid}/stat")
    right = raw.rsplit(")", 1)
    if len(right) != 2:
        _fail("WRITER_LOCK_IDENTITY_INVALID", f"malformed /proc/{pid}/stat")
    fields_after_comm = right[1].strip().split()
    if len(fields_after_comm) < 20:
        _fail("WRITER_LOCK_IDENTITY_INVALID", f"short /proc/{pid}/stat")
    return fields_after_comm[19]


def _process_matches(identity: Mapping[str, Any]) -> bool:
    try:
        pid = int(identity["pid"])
        if identity["boot_id"] != _boot_id():
            return False
        return identity["process_start_time"] == _process_start_time(pid)
    except (KeyError, TypeError, ValueError, ThreeBodyViolation):
        return False


def _lock_record_is_live(record: object) -> bool:
    return isinstance(record, dict) and _process_matches(record)


def _validate_lock_record(raw: object) -> dict[str, Any]:
    code = "WRITER_LOCK_IDENTITY_INVALID"
    record = _require_exact_fields(raw, LOCK_RECORD_FIELDS, code=code, label="writer lock")
    if record["schema"] != "q3_writer_lock.v1" or record["writer_body"] not in {
        "CODEX",
        "LINUX",
    }:
        _fail(code, "lock schema or writer body invalid")
    if not isinstance(record["pid"], int) or isinstance(record["pid"], bool) or record["pid"] <= 0:
        _fail(code, "lock PID invalid")
    for field in ("worktree", "branch", "process_start_time", "boot_id"):
        _require_nfc_string(record[field], code=code, field=field)
    if (
        not isinstance(record["codex_session_id"], str)
        or SESSION_RE.fullmatch(record["codex_session_id"]) is None
    ):
        _fail(code, "lock session ID invalid")
    _canonical_repo_path(record["task_path"], code=code, field="task_path")
    for field in ("task_blob", "base_head"):
        _require_hash(record[field], GIT_OBJECT_RE, code=code, field=field)
    _require_hash(record["phase_key_hash"], SHA256_RE, code=code, field="phase_key_hash")
    for field in ("run_id", "trigger_nonce"):
        _require_token(record[field], code=code, field=field)
    return record


def _validate_child_identity(raw: object, *, code: str) -> dict[str, Any]:
    identity = _require_exact_fields(raw, CHILD_IDENTITY_FIELDS, code=code, label="child identity")
    if identity["state"] != "CHILD_READY_TO_EXEC":
        _fail(code, "child is not ready for exec handoff")
    for field in ("run_id", "trigger_nonce"):
        _require_token(identity[field], code=code, field=field)
    for field in ("task_blob", "base_head"):
        _require_hash(identity[field], GIT_OBJECT_RE, code=code, field=field)
    if not isinstance(identity["pid"], int) or isinstance(identity["pid"], bool):
        _fail(code, "child PID invalid")
    if not isinstance(identity["lock_inode"], str) or not identity["lock_inode"].isdigit():
        _fail(code, "child lock inode invalid")
    for field in ("process_start_time", "boot_id"):
        _require_nfc_string(identity[field], code=code, field=field)
    return identity


def _read_lock_record(fd: int) -> dict[str, Any] | None:
    os.lseek(fd, 0, os.SEEK_SET)
    raw = os.read(fd, 1_000_000)
    if not raw.strip():
        return None
    return _validate_lock_record(_load_unique_json_bytes(raw, code="WRITER_LOCK_IDENTITY_INVALID"))


def _write_lock_record(fd: int, record: Mapping[str, Any]) -> None:
    raw = _canonical_state_bytes(record)
    os.lseek(fd, 0, os.SEEK_SET)
    os.ftruncate(fd, 0)
    os.write(fd, raw)
    os.fsync(fd)


def _acquire_writer_lock(path: Path, record: Mapping[str, Any]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        os.close(fd)
        _fail("WRITER_LOCK_COLLISION")
    validated_record = _validate_lock_record(dict(record))
    old = _read_lock_record(fd)
    if _lock_record_is_live(old):
        fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)
        _fail("WRITER_LOCK_STALE_RECOVERY_UNSAFE", "live identity without held flock")
    _write_lock_record(fd, validated_record)
    os.set_inheritable(fd, True)
    return fd


def _event_key(event: Mapping[str, Any]) -> tuple[str, str]:
    return event["run_id"], event["trigger_nonce"]


def _find_event(state: Mapping[str, Any], event: Mapping[str, Any]) -> dict[str, Any] | None:
    key = _event_key(event)
    return next((row for row in state["event_ledger"] if _event_key(row) == key), None)


def _validate_wake_event(event: object) -> dict[str, Any]:
    code = "THREE_BODY_WAKE_EVENT_INVALID"
    expected = {"run_id", "trigger_nonce", "source_event_commit", "answer_blob"}
    if not isinstance(event, dict) or set(event) != expected:
        _fail(code, "wake event closed fields differ")
    _require_token(event["run_id"], code=code, field="run_id")
    _require_token(event["trigger_nonce"], code=code, field="trigger_nonce")
    _require_hash(
        event["source_event_commit"],
        GIT_OBJECT_RE,
        code=code,
        field="source_event_commit",
    )
    _require_hash(event["answer_blob"], SHA256_RE, code=code, field="answer_blob")
    return event


def build_codex_resume_command(
    *,
    session_id: str,
    repo_root: Path,
    output_schema: Path,
    final_reply: Path,
    prompt: str,
) -> list[str]:
    if SESSION_RE.fullmatch(session_id) is None:
        _fail("PINNED_SESSION_INVALID", "session ID is not canonical")
    if not prompt.strip():
        _fail("PINNED_SESSION_INVALID", "empty follow-up prompt")
    return [
        "codex",
        "exec",
        "-C",
        str(repo_root.resolve()),
        "--sandbox",
        "workspace-write",
        "--json",
        "--output-schema",
        str(output_schema.resolve()),
        "-o",
        str(final_reply.resolve()),
        "resume",
        session_id,
        prompt,
    ]


def build_codex_read_only_resume_command(
    *,
    session_id: str,
    repo_root: Path,
    prompt: str,
    codex_bin: str = "codex",
) -> list[str]:
    if SESSION_RE.fullmatch(session_id) is None:
        _fail("PINNED_SESSION_INVALID", "session ID is not canonical")
    if not prompt.strip() or not codex_bin.strip():
        _fail("PINNED_SESSION_INVALID", "empty prompt or Codex binary")
    return [
        codex_bin,
        "exec",
        "-C",
        str(repo_root.resolve()),
        "--sandbox",
        "read-only",
        "resume",
        session_id,
        prompt,
    ]


def run_read_only_watch(
    *,
    repo_root: Path,
    branch: str,
    session_id: str,
    prompt_path: str,
    codex_bin: str = "codex",
    lock_path: Path | None = None,
) -> dict[str, Any]:
    """Fetch the pinned branch and wake Codex only when origin is ahead.

    This path never updates HEAD or the worktree. It deliberately does not use
    the writer lock or event ledger because the resumed turn is sandboxed
    read-only and may only inspect ``HEAD..origin/<branch>``.
    """
    if not branch or branch.startswith("-") or _current_branch(repo_root) != branch:
        _fail("LAUNCH_PIN_DRIFT", "watch branch changed")
    relative_prompt = _canonical_repo_path(
        prompt_path, code="PINNED_SESSION_INVALID", field="prompt_path"
    )
    prompt_file = repo_root / relative_prompt
    if not prompt_file.is_file():
        _fail("PINNED_SESSION_INVALID", f"missing watch prompt: {relative_prompt}")
    prompt = prompt_file.read_text(encoding="utf-8")
    command = build_codex_read_only_resume_command(
        session_id=session_id,
        repo_root=repo_root,
        prompt=prompt,
        codex_bin=codex_bin,
    )
    watch_lock = lock_path or DEFAULT_READ_ONLY_WATCH_LOCK
    try:
        with _plain_flock(watch_lock, blocking=False):
            _git_output(
                repo_root,
                "fetch",
                "--quiet",
                "origin",
                branch,
                code="PINNED_SESSION_LAUNCH_FAILED",
            )
            raw_ahead = _git_output(
                repo_root,
                "rev-list",
                "--count",
                f"HEAD..origin/{branch}",
                code="PINNED_SESSION_LAUNCH_FAILED",
            )
            try:
                remote_ahead = int(raw_ahead.decode("ascii").strip())
            except ValueError:
                _fail("PINNED_SESSION_LAUNCH_FAILED", "invalid remote-ahead count")
            if remote_ahead <= 0:
                return {"result": "NO_REMOTE_ADVANCE", "remote_ahead": 0}
            result = subprocess.run(command, cwd=repo_root, stdin=subprocess.DEVNULL)
            if result.returncode != 0:
                _fail(
                    "PINNED_SESSION_LAUNCH_FAILED",
                    f"read-only resume exited {result.returncode}",
                )
            return {
                "result": "READ_ONLY_WAKE_COMPLETE",
                "remote_ahead": remote_ahead,
                "session_id": session_id,
            }
    except BlockingIOError:
        return {"result": "WATCH_ALREADY_RUNNING"}


def _current_branch(repo_root: Path) -> str:
    raw = _git_output(repo_root, "rev-parse", "--abbrev-ref", "HEAD", code="LAUNCH_PIN_DRIFT")
    return raw.decode("utf-8").strip()


def _current_head(repo_root: Path) -> str:
    return (
        _git_output(repo_root, "rev-parse", "HEAD", code="LAUNCH_PIN_DRIFT").decode("ascii").strip()
    )


def _control_version(repo_root: Path) -> int:
    path = repo_root / "docs" / "CODEX_CONTROL.md"
    if not path.is_file():
        _fail("LAUNCH_PIN_DRIFT", "active control is missing")
    match = re.search(r"^CONTROL_VERSION:\s*(\d+)\s*$", path.read_text(encoding="utf-8"), re.M)
    if match is None:
        _fail("LAUNCH_PIN_DRIFT", "control version is missing")
    return int(match.group(1))


def _git_blob_for_worktree_path(repo_root: Path, task_path: str) -> str:
    path = repo_root / task_path
    if not path.is_file():
        _fail("LAUNCH_PIN_DRIFT", f"missing task path: {task_path}")
    return (
        _git_output(repo_root, "hash-object", "--", task_path, code="LAUNCH_PIN_DRIFT")
        .decode("ascii")
        .strip()
    )


def _canonical_phase_hash(repo_root: Path) -> str:
    path = repo_root / "orchestrator/state/CHANNEL_RUNTIME.json"
    data = _load_unique_json_bytes(path.read_bytes(), code="LAUNCH_PIN_DRIFT")
    try:
        phase = data["active_proshka_phase"]["phase_key"]
    except (KeyError, TypeError):
        _fail("LAUNCH_PIN_DRIFT", "canonical phase key missing")
    if not isinstance(phase, dict):
        _fail("LAUNCH_PIN_DRIFT", "canonical phase key invalid")
    return hashlib.sha256(_canonical_json_bytes(phase)).hexdigest()


def _build_lock_record(
    *,
    repo_root: Path,
    branch: str,
    writer_body: str,
    codex_session_id: str,
    task_path: str,
    task_blob: str,
    phase_key_hash: str,
    base_head: str,
    event: Mapping[str, Any],
) -> dict[str, Any]:
    return {
        "schema": "q3_writer_lock.v1",
        "worktree": str(repo_root.resolve()),
        "branch": branch,
        "writer_body": writer_body,
        "pid": os.getpid(),
        "process_start_time": _process_start_time(os.getpid()),
        "boot_id": _boot_id(),
        "codex_session_id": codex_session_id,
        "task_path": task_path,
        "task_blob": task_blob,
        "phase_key_hash": phase_key_hash,
        "base_head": base_head,
        "run_id": event["run_id"],
        "trigger_nonce": event["trigger_nonce"],
    }


def _child_identity_from_marker(path: Path) -> dict[str, Any]:
    marker = _load_unique_json_bytes(path.read_bytes(), code="PINNED_SESSION_LAUNCH_FAILED")
    return _validate_child_identity(marker, code="PINNED_SESSION_LAUNCH_FAILED")


def _validate_child_identity_binding(
    identity: Mapping[str, Any],
    *,
    event: Mapping[str, Any],
    task_blob: str,
    base_head: str,
    lock_inode: str,
    code: str,
) -> None:
    expected = {
        "run_id": event["run_id"],
        "trigger_nonce": event["trigger_nonce"],
        "task_blob": task_blob,
        "base_head": base_head,
        "lock_inode": lock_inode,
    }
    drift = sorted(field for field, value in expected.items() if identity[field] != value)
    if drift:
        _fail(code, f"child identity drift: {','.join(drift)}")


def launch_pinned_session(
    *,
    state_path: Path,
    lock_path: Path,
    event: Mapping[str, Any],
    repo_root: Path,
    branch: str,
    session_id: str,
    task_path: str,
    task_blob: str,
    phase_key_hash: str,
    base_head: str,
    command: Sequence[str],
    crash_after_exec: bool = False,
) -> dict[str, Any]:
    """Launch one pinned child, with duplicate-safe at-most-once semantics.

    ``crash_after_exec`` is a plant hook: it simulates parent death after the
    child accepted the exec handoff but before the parent persisted ``STARTED``.
    """
    wake = _validate_wake_event(dict(event))
    _canonical_repo_path(task_path, code="LAUNCH_PIN_DRIFT", field="task_path")
    _require_hash(task_blob, GIT_OBJECT_RE, code="LAUNCH_PIN_DRIFT", field="task_blob")
    _require_hash(phase_key_hash, SHA256_RE, code="LAUNCH_PIN_DRIFT", field="phase_key_hash")
    _require_hash(base_head, GIT_OBJECT_RE, code="LAUNCH_PIN_DRIFT", field="base_head")
    if SESSION_RE.fullmatch(session_id) is None:
        _fail("PINNED_SESSION_INVALID")
    if not command or "--last" in command or session_id not in command:
        _fail("PINNED_SESSION_INVALID", "launcher command is not bound to exact session ID")
    if _current_head(repo_root) != base_head or wake["source_event_commit"] != base_head:
        _fail("LAUNCH_PIN_DRIFT", "HEAD or source event commit changed")
    if _current_branch(repo_root) != branch:
        _fail("LAUNCH_PIN_DRIFT", "branch changed")
    if _control_version(repo_root) != CONTROL_VERSION:
        _fail("LAUNCH_PIN_DRIFT", "control version changed")
    if _git_blob_for_worktree_path(repo_root, task_path) != task_blob:
        _fail("LAUNCH_PIN_DRIFT", "task blob changed")
    if _canonical_phase_hash(repo_root) != phase_key_hash:
        _fail("LAUNCH_PIN_DRIFT", "phase key changed")
    state = validate_repository_gate(
        repo_root=repo_root,
        state_path=state_path,
        require_dispatch_clear=True,
    )
    existing = _find_event(state, wake)
    if existing is not None:
        if any(existing[field] != wake[field] for field in wake):
            _fail("DUPLICATE_TRIGGER_DRIFT")
        return {"result": "DUPLICATE_TRIGGER_NOOP", "event": existing}

    record = _build_lock_record(
        repo_root=repo_root,
        branch=branch,
        writer_body="CODEX",
        codex_session_id=session_id,
        task_path=task_path,
        task_blob=task_blob,
        phase_key_hash=phase_key_hash,
        base_head=base_head,
        event=wake,
    )
    try:
        lock_fd = _acquire_writer_lock(lock_path, record)
    except ThreeBodyViolation as exc:
        if exc.code == "WRITER_LOCK_COLLISION":
            reread = load_state(
                state_path,
                repo_root=repo_root,
                semantic_attestation_resolver=resolve_semantic_attestation,
            )
            existing = _find_event(reread, wake)
            if existing is not None and all(existing[field] == wake[field] for field in wake):
                return {"result": "DUPLICATE_TRIGGER_NOOP", "event": existing}
        raise

    try:
        state = validate_repository_gate(
            repo_root=repo_root,
            state_path=state_path,
            require_dispatch_clear=True,
        )
    except Exception:
        fcntl.flock(lock_fd, fcntl.LOCK_UN)
        os.close(lock_fd)
        raise
    existing = _find_event(state, wake)
    if existing is not None:
        fcntl.flock(lock_fd, fcntl.LOCK_UN)
        os.close(lock_fd)
        if any(existing[field] != wake[field] for field in wake):
            _fail("DUPLICATE_TRIGGER_DRIFT")
        return {"result": "DUPLICATE_TRIGGER_NOOP", "event": existing}

    marker_path = lock_path.with_name(
        f"{lock_path.name}.{wake['run_id']}.{wake['trigger_nonce']}.marker.json"
    )
    reserved = {
        **wake,
        "status": "RESERVED",
        "child_identity": None,
        "failure": None,
    }
    state["event_ledger"].append(reserved)
    _atomic_write(state_path, _canonical_state_bytes(state))

    error_read, error_write = os.pipe()
    os.set_inheritable(error_write, True)
    os.set_inheritable(lock_fd, True)
    wrapper = [
        sys.executable,
        str(Path(__file__).resolve()),
        "_child-exec",
        "--marker",
        str(marker_path),
        "--error-fd",
        str(error_write),
        "--run-id",
        wake["run_id"],
        "--trigger-nonce",
        wake["trigger_nonce"],
        "--task-blob",
        task_blob,
        "--base-head",
        base_head,
        "--lock-inode",
        str(os.fstat(lock_fd).st_ino),
        "--",
        *command,
    ]
    try:
        child = subprocess.Popen(
            wrapper,
            cwd=repo_root,
            pass_fds=(lock_fd, error_write),
            stdin=subprocess.DEVNULL,
        )
        os.close(error_write)
        error_write = -1
        chunks: list[bytes] = []
        while True:
            chunk = os.read(error_read, 4096)
            if not chunk:
                break
            chunks.append(chunk)
        error = b"".join(chunks).decode("utf-8", errors="replace")
        if error:
            reserved["status"] = "FAILED_BEFORE_LAUNCH"
            reserved["failure"] = error
            _atomic_write(state_path, _canonical_state_bytes(state))
            _fail("PINNED_SESSION_LAUNCH_FAILED", error)
        deadline = time.monotonic() + 5.0
        while not marker_path.is_file() and time.monotonic() < deadline:
            time.sleep(0.01)
        if not marker_path.is_file():
            reserved["status"] = "FAILED_BEFORE_LAUNCH"
            reserved["failure"] = "CHILD_READY_TO_EXEC marker missing"
            _atomic_write(state_path, _canonical_state_bytes(state))
            _fail("PINNED_SESSION_LAUNCH_FAILED", reserved["failure"])
        identity = _child_identity_from_marker(marker_path)
        _validate_child_identity_binding(
            identity,
            event=wake,
            task_blob=task_blob,
            base_head=base_head,
            lock_inode=str(os.fstat(lock_fd).st_ino),
            code="PINNED_SESSION_LAUNCH_FAILED",
        )
        if crash_after_exec:
            os.close(lock_fd)
            lock_fd = -1
            return {
                "result": "PLANT_PARENT_CRASH_AFTER_EXEC",
                "pid": child.pid,
                "marker": str(marker_path),
                "process": child,
            }
        reserved["status"] = "STARTED"
        reserved["child_identity"] = identity
        _atomic_write(state_path, _canonical_state_bytes(state))
        os.close(lock_fd)
        lock_fd = -1
        return {
            "result": "STARTED",
            "pid": child.pid,
            "event": reserved,
            "process": child,
        }
    except Exception:
        if reserved["status"] == "RESERVED" and not crash_after_exec:
            reserved["status"] = "FAILED_BEFORE_LAUNCH"
            reserved["failure"] = "launcher exception before durable STARTED"
            _atomic_write(state_path, _canonical_state_bytes(state))
        raise
    finally:
        os.close(error_read)
        if error_write >= 0:
            os.close(error_write)
        if lock_fd >= 0:
            fcntl.flock(lock_fd, fcntl.LOCK_UN)
            os.close(lock_fd)


def recover_launch_state(
    *,
    state_path: Path,
    lock_path: Path,
    marker_path: Path,
    event: Mapping[str, Any],
    repo_root: Path,
) -> str:
    wake = _validate_wake_event(dict(event))
    state = load_state(
        state_path,
        repo_root=repo_root,
        semantic_attestation_resolver=resolve_semantic_attestation,
    )
    current = _find_event(state, wake)
    if current is None:
        _fail("THREE_BODY_EVENT_LEDGER_INVALID", "event was never reserved")
    if current["status"] != "RESERVED":
        return current["status"]
    try:
        record = _validate_lock_record(
            _load_unique_json_bytes(lock_path.read_bytes(), code="WRITER_LOCK_IDENTITY_INVALID")
        )
    except OSError as exc:
        _fail("WRITER_LOCK_IDENTITY_INVALID", str(exc))
    if (
        record["worktree"] != str(repo_root.resolve())
        or record["run_id"] != wake["run_id"]
        or record["trigger_nonce"] != wake["trigger_nonce"]
        or record["base_head"] != wake["source_event_commit"]
    ):
        _fail("WRITER_LOCK_IDENTITY_INVALID", "lock record does not bind wake event")
    try:
        with _plain_flock(lock_path, blocking=False):
            if marker_path.is_file():
                identity = _child_identity_from_marker(marker_path)
                _validate_child_identity_binding(
                    identity,
                    event=wake,
                    task_blob=record["task_blob"],
                    base_head=record["base_head"],
                    lock_inode=str(lock_path.stat().st_ino),
                    code="WRITER_LOCK_STALE_RECOVERY_UNSAFE",
                )
                if _process_matches(identity):
                    _fail(
                        "WRITER_LOCK_STALE_RECOVERY_UNSAFE",
                        "matching child is live although writer lock is acquirable",
                    )
                current["status"] = "STARTED"
                current["child_identity"] = identity
                current["failure"] = None
                _atomic_write(state_path, _canonical_state_bytes(state))
                return "STARTED"
            if current["status"] == "RESERVED":
                current["status"] = "FAILED_BEFORE_LAUNCH"
                current["failure"] = "no matching child and writer lock is free"
                _atomic_write(state_path, _canonical_state_bytes(state))
            return current["status"]
    except BlockingIOError:
        if not marker_path.is_file():
            _fail("WRITER_LOCK_STALE_RECOVERY_UNSAFE", "held lock without child marker")
        identity = _child_identity_from_marker(marker_path)
        _validate_child_identity_binding(
            identity,
            event=wake,
            task_blob=record["task_blob"],
            base_head=record["base_head"],
            lock_inode=str(lock_path.stat().st_ino),
            code="WRITER_LOCK_STALE_RECOVERY_UNSAFE",
        )
        if not _process_matches(identity):
            _fail("WRITER_LOCK_STALE_RECOVERY_UNSAFE", "held lock with stale child identity")
        return "STARTED_OBSERVED"


def _child_exec(args: argparse.Namespace) -> int:
    marker = {
        "state": "CHILD_READY_TO_EXEC",
        "run_id": args.run_id,
        "trigger_nonce": args.trigger_nonce,
        "pid": os.getpid(),
        "process_start_time": _process_start_time(os.getpid()),
        "boot_id": _boot_id(),
        "task_blob": args.task_blob,
        "base_head": args.base_head,
        "lock_inode": args.lock_inode,
    }
    _atomic_write(Path(args.marker), _canonical_state_bytes(marker))
    os.set_inheritable(args.error_fd, False)
    command = list(args.command)
    if command and command[0] == "--":
        command = command[1:]
    try:
        os.execvp(command[0], command)
    except OSError as exc:
        os.write(args.error_fd, str(exc).encode("utf-8", errors="replace"))
        return 127


def materialize_semantic_admission(
    *,
    entry_id: str,
    attestation_id: str,
    state_path: Path = DEFAULT_STATE,
    lock_path: Path = DEFAULT_WRITER_LOCK,
    repo_root: Path = REPO_ROOT,
    semantic_attestation_resolver: Callable[[str], dict[str, Any] | None] | None = None,
    supplier_preflight_resolver: Callable[[str], str | None] | None = None,
    autonomy_lease_resolver: Callable[[str], dict[str, Any] | None] | None = None,
) -> dict[str, Any]:
    """Move one quarantine entry from KERNEL_GREEN to SEMANTICALLY_ADMITTED.

    Exactly three fields change: ``status``, ``admitted_scope`` and
    ``semantic_attestation_id``.  The admitted scope comes from the externally
    resolved receipt, never from an argument.  The candidate state is validated
    with the same resolver before it replaces the tracked state.
    """
    code = "SEMANTIC_ADMISSION_REFUSED"
    if semantic_attestation_resolver is not None:
        resolver = semantic_attestation_resolver
    else:
        def resolver(requested_attestation_id: str) -> dict[str, Any] | None:
            if any(
                requested_attestation_id == waiver_id
                for _, waiver_id in EXACT_OWNER_WAIVERS
            ):
                return resolve_semantic_attestation(requested_attestation_id)
            return resolve_linux_semantic_attestation(requested_attestation_id)
    with _plain_flock(lock_path):
        if not state_path.is_file():
            _fail(code, f"missing state: {state_path}")
        state = _load_unique_json_bytes(
            state_path.read_bytes(), code="SEMANTIC_QUARANTINE_STATE_INVALID"
        )
        entries = state.get("entries")
        if not isinstance(entries, list):
            _fail(code, "state has no entry list")
        index = None
        for position, candidate in enumerate(entries):
            if isinstance(candidate, Mapping) and candidate.get("entry_id") == entry_id:
                index = position
                break
        if index is None:
            _fail(code, f"unknown entry: {entry_id}")
        entry = dict(entries[index])

        status = entry.get("status")
        if status == "SEMANTICALLY_ADMITTED":
            if entry.get("semantic_attestation_id") == attestation_id:
                return {
                    "entry_id": entry_id,
                    "attestation_id": attestation_id,
                    "status": status,
                    "admitted_scope": list(entry.get("admitted_scope") or []),
                    "changed": False,
                }
            _fail(code, "admitted entry cannot take a different attestation ID")
        if status != "KERNEL_GREEN":
            _fail(code, f"entry is {status}, only KERNEL_GREEN can be admitted")

        receipt = resolver(attestation_id)
        if receipt is None:
            _fail(code, f"no external receipt resolved for {attestation_id}")
        _require_semantic_attestation_issuer(
            entry=entry,
            receipt=receipt,
            attestation_id=attestation_id,
            code=code,
        )
        if receipt.get("attestation_id") != attestation_id:
            _fail(code, "receipt does not carry the requested attestation ID")
        scope = receipt.get("admitted_scope")
        if not isinstance(scope, list) or not scope:
            _fail(code, "receipt carries no admitted scope")

        entry["status"] = "SEMANTICALLY_ADMITTED"
        entry["admitted_scope"] = list(scope)
        entry["semantic_attestation_id"] = attestation_id

        candidate_entries = list(entries)
        candidate_entries[index] = entry
        candidate_state = dict(state)
        candidate_state["entries"] = candidate_entries

        validated = validate_state(
            candidate_state,
            repo_root=repo_root,
            semantic_attestation_resolver=resolver,
            supplier_preflight_resolver=supplier_preflight_resolver,
            autonomy_lease_resolver=autonomy_lease_resolver,
        )
        _atomic_write(state_path, _canonical_state_bytes(validated))
        return {
            "entry_id": entry_id,
            "attestation_id": attestation_id,
            "status": "SEMANTICALLY_ADMITTED",
            "admitted_scope": list(scope),
            "changed": True,
        }


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command_name", required=True)
    validate = sub.add_parser("validate", help="validate canonical v9 state")
    validate.add_argument("--state", type=Path, default=DEFAULT_STATE)
    request = sub.add_parser("request-validate", help="validate a CODEX_REQ body")
    request.add_argument("path", type=Path)
    launch = sub.add_parser("launch", help="launch one exact pinned Codex session")
    launch.add_argument("--state", type=Path, default=DEFAULT_STATE)
    launch.add_argument("--lock", type=Path, default=DEFAULT_WRITER_LOCK)
    launch.add_argument("--run-id", required=True)
    launch.add_argument("--trigger-nonce", required=True)
    launch.add_argument("--source-event-commit", required=True)
    launch.add_argument("--answer-blob", required=True)
    launch.add_argument("--session-id", required=True)
    launch.add_argument("--branch", required=True)
    launch.add_argument("--task-path", required=True)
    launch.add_argument("--task-blob", required=True)
    launch.add_argument("--phase-key-hash", required=True)
    launch.add_argument("--base-head", required=True)
    launch.add_argument("--output-schema", type=Path, required=True)
    launch.add_argument("--final-reply", type=Path, required=True)
    launch.add_argument("--prompt", required=True)
    watch = sub.add_parser(
        "watch-read-only", help="wake one exact Codex session when origin is ahead"
    )
    watch.add_argument("--lock", type=Path, default=DEFAULT_READ_ONLY_WATCH_LOCK)
    watch.add_argument("--session-id", required=True)
    watch.add_argument("--branch", required=True)
    watch.add_argument("--prompt-path", default="docs/Codex/WATCH_PROMPT.md")
    watch.add_argument("--codex-bin", default="codex")
    admit = sub.add_parser(
        "semantic-admit",
        help="materialize one externally attested semantic admission",
    )
    admit.add_argument("--entry-id", required=True)
    admit.add_argument("--attestation-id", required=True)
    admit.add_argument("--state", type=Path, default=DEFAULT_STATE)
    admit.add_argument("--lock", type=Path, default=DEFAULT_WRITER_LOCK)
    child = sub.add_parser("_child-exec")
    child.add_argument("--marker", required=True)
    child.add_argument("--error-fd", type=int, required=True)
    child.add_argument("--run-id", required=True)
    child.add_argument("--trigger-nonce", required=True)
    child.add_argument("--task-blob", required=True)
    child.add_argument("--base-head", required=True)
    child.add_argument("--lock-inode", required=True)
    child.add_argument("command", nargs=argparse.REMAINDER)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        if args.command_name == "_child-exec":
            return _child_exec(args)
        if args.command_name == "validate":
            state = load_state(
                args.state,
                repo_root=REPO_ROOT,
                semantic_attestation_resolver=resolve_semantic_attestation,
            )
            print(
                "THREE_BODY_STATE_VALID "
                f"entries={len(state['entries'])} events={len(state['event_ledger'])} "
                f"active_lease={'yes' if state['active_lease'] else 'no'}"
            )
            return 0
        if args.command_name == "semantic-admit":
            result = materialize_semantic_admission(
                entry_id=args.entry_id,
                attestation_id=args.attestation_id,
                state_path=args.state,
                lock_path=args.lock,
                repo_root=REPO_ROOT,
            )
            print(json.dumps(result, ensure_ascii=False, sort_keys=True))
            return 0
        if args.command_name == "request-validate":
            envelope, payload = parse_request_body(args.path.read_bytes())
            print(f"CODEX_REQUEST_VALID id={envelope['CODEX_REQ']} payload_bytes={len(payload)}")
            return 0
        if args.command_name == "watch-read-only":
            result = run_read_only_watch(
                repo_root=REPO_ROOT,
                branch=args.branch,
                session_id=args.session_id,
                prompt_path=args.prompt_path,
                codex_bin=args.codex_bin,
                lock_path=args.lock,
            )
            print(json.dumps(result, ensure_ascii=False, sort_keys=True))
            return 0
        if args.command_name == "launch":
            command = build_codex_resume_command(
                session_id=args.session_id,
                repo_root=REPO_ROOT,
                output_schema=args.output_schema,
                final_reply=args.final_reply,
                prompt=args.prompt,
            )
            result = launch_pinned_session(
                state_path=args.state,
                lock_path=args.lock,
                event={
                    "run_id": args.run_id,
                    "trigger_nonce": args.trigger_nonce,
                    "source_event_commit": args.source_event_commit,
                    "answer_blob": args.answer_blob,
                },
                repo_root=REPO_ROOT,
                branch=args.branch,
                session_id=args.session_id,
                task_path=args.task_path,
                task_blob=args.task_blob,
                phase_key_hash=args.phase_key_hash,
                base_head=args.base_head,
                command=command,
            )
            printable = {key: value for key, value in result.items() if key != "process"}
            print(json.dumps(printable, ensure_ascii=False, sort_keys=True))
            return 0
    except (OSError, ThreeBodyViolation) as exc:
        print(exc, file=sys.stderr)
        return 2
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
