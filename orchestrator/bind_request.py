#!/usr/bin/env python3
"""Bind one exact Proshka request; publish a pinned commit outside the writer lock.

All local changes and durable intent updates hold the existing writer lock.
An existing intent is reconciled, never automatically rebound or pushed again.
A missing push receipt triggers fresh remote inspection of the pinned payload.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from orchestrator import workflow_runtime as workflow

QUEUE = ROOT / "docs/routeB_bus/PROSHKA_QUEUE.md"


class BindingError(RuntimeError):
    pass


class QueueDriftError(BindingError):
    pass


def sh(*args, check=True):
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True, timeout=90, check=False)
    if check and result.returncode:
        # Git transport diagnostics can contain credential-bearing URLs.
        raise BindingError("COMMAND_FAILED:" + Path(args[0]).name + ":" + str(result.returncode))
    return result.stdout.strip()


def header(text: str, key: str) -> str:
    value, error = workflow._single_request_header(text, key)
    if error or not value:
        raise BindingError("REQUEST_HEADER_INVALID:" + key)
    return value


ENTRY = """## {rid} · {title} · {status}

- `STATUS: {status}`
- Request: `{rel}`
- Boundary: `{boundary}`
- Call class: `{call}`
- Intake carried: {intake}
- Registered predictions: {preds}
- Delivery mode: owner remote; GitHub locator
- Request commit / bytes / lines / SHA-256 / Git blob / Final LF:
  `{commit}` / `{nbytes}` / `{nlines}` /
  `{sha}` /
  `{blob}` / `{lf}`

---

"""


def _intent_path(operation_id: str) -> Path:
    if re.fullmatch(r"[0-9a-f]{64}", operation_id) is None:
        raise BindingError("BINDING_OPERATION_ID_INVALID")
    return workflow._git_common_dir(ROOT) / "q3-bind-intents" / (operation_id + ".json")


def _save_intent(record: dict, before: bytes | None, epoch) -> None:
    path = _intent_path(record["operation_id"])
    epoch.recheck()
    if path.is_symlink() or path.parent.is_symlink():
        raise BindingError("BINDING_UNSAFE_INTENT_PATH")
    current = path.read_bytes() if path.exists() else None
    if current != before:
        raise BindingError("BINDING_INTENT_PREIMAGE_CHANGED")
    path.parent.mkdir(mode=0o700, exist_ok=True)
    workflow._atomic_bytes(path, workflow._team_json(record))
    epoch.recheck()
    if path.read_bytes() != workflow._team_json(record):
        raise BindingError("BINDING_INTENT_READBACK_CHANGED")


def _pending(request_path: str) -> dict | None:
    directory = workflow._git_common_dir(ROOT) / "q3-bind-intents"
    if directory.is_symlink():
        raise BindingError("BINDING_UNSAFE_INTENT_PATH")
    matches = []
    for path in sorted(directory.glob("*.json")):
        if path.is_symlink() or path.stat().st_size > 128 * 1024:
            raise BindingError("BINDING_INTENT_INVALID")
        record = workflow._load_unique_json(path)
        if path != _intent_path(record.get("operation_id", "")) or path.read_bytes() != workflow._team_json(record):
            raise BindingError("BINDING_INTENT_INVALID")
        if record.get("request_path") == request_path and record.get("state") != "ABORTED":
            matches.append(record)
    if len(matches) > 1:
        raise BindingError("BINDING_INTENT_AMBIGUOUS")
    return matches[0] if matches else None


def _actor_recheck(record: dict, *, source_check=True) -> None:
    actor = record["actor"]
    if actor is None:
        if workflow._team_enabled(ROOT):
            raise BindingError("BINDING_PREACTIVATION_INTENT_REQUIRES_RECONCILIATION")
        return
    raw, data, _ = workflow._team_current(ROOT)
    workflow._team_actor(ROOT, data)
    if (data["ownership"]["state"] != "ACTIVE" or data["reconciliation_pending"]
            or data["ownership"]["epoch"] != actor["epoch"]
            or data["owner_thread_id"] != actor["task"]
            or workflow.os.environ.get("Q3_OWNER_EPOCH") != str(actor["epoch"])
            or data["operation"]["id"] != actor["operation_id"]
            or workflow._resume_digest(raw) != actor["checkpoint_sha256"]):
        raise BindingError("BINDING_OWNER_OR_OPERATION_CHANGED")
    if source_check:
        # Only this transaction's exact queue postimage replaces its preimage.
        expected = dict(data["source_manifest"])
        if record.get("queue_sha256") and record["queue_path"] in expected:
            expected[record["queue_path"]] = record["queue_sha256"]
        workflow._team_verify_paths(ROOT, expected)
        workflow._team_verify_paths(ROOT, {record["request_path"]: record["request_sha256"],
                                          record["queue_path"]: record["queue_sha256"]})
    if record["push_requested"]:
        reservation = workflow._team_local_operation(ROOT, actor["operation_id"])
        confirmed = (not source_check and reservation is not None and reservation.get("state") == "CONFIRMED"
                     and reservation.get("evidence", {}).get("binding_operation_id") == record["operation_id"])
        if (reservation is None or (reservation.get("state") != "RESERVED" and not confirmed)
                or reservation.get("epoch") != actor["epoch"]
                or reservation.get("checkpoint_sha256") != actor["checkpoint_sha256"]):
            raise BindingError("BINDING_ORIGINAL_RESERVATION_REQUIRED")


def _remote_tip() -> str:
    rows = sh("git", "ls-remote", "--exit-code", "origin", "refs/heads/rh_clean").splitlines()
    if len(rows) != 1:
        raise BindingError("BINDING_REMOTE_REF_INVALID")
    tip, ref = rows[0].split("\t")
    if not workflow._team_hex(tip, 40) or ref != "refs/heads/rh_clean":
        raise BindingError("BINDING_REMOTE_REF_INVALID")
    return tip


def _remote_verification(record: dict) -> str | None:
    """Fresh branch observation and exact committed payload; never compare a later queue."""
    if not record.get("queue_commit"):
        return None
    try:
        rows = sh("git", "ls-remote", "--exit-code", "origin", "refs/heads/rh_clean").splitlines()
        if len(rows) != 1:
            return None
        tip, ref = rows[0].split("\t")
        if not workflow._team_hex(tip, 40) or ref != "refs/heads/rh_clean":
            return None
        sh("git", "fetch", "--no-tags", "--no-write-fetch-head", "origin", tip)
        sh("git", "merge-base", "--is-ancestor", record["queue_commit"], tip)
        sh("git", "merge-base", "--is-ancestor", record["request_commit"], record["queue_commit"])
        for commit, path, digest, blob in (
            (record["request_commit"], record["request_path"], record["request_sha256"], record["request_blob"]),
            (record["queue_commit"], record["queue_path"], record["queue_sha256"], record["queue_blob"]),
        ):
            if sh("git", "rev-parse", commit + ":" + path) != blob:
                return None
            if workflow._resume_digest(workflow._team_git(ROOT, "show", commit + ":" + path)) != digest:
                return None
        if sh("git", "ls-remote", "--exit-code", "origin", "refs/heads/rh_clean") != rows[0]:
            return None
        return tip
    except (BindingError, workflow.WorkflowRuntimeError, OSError, ValueError, subprocess.SubprocessError):
        return None


def _delivery_line(record: dict) -> None:
    print(f"LINE: Adjudicate {record['request_id']}. Authoritative byte-exact payload: {record['request_path']} "
          f"at commit {record['request_commit']} (blob {record['request_blob']}, SHA-256 {record['request_sha256']}, "
          f"{record['lines']} lines, {record['bytes']} bytes) on Malaeu/chen_q3 rh_clean; fetch it from GitHub "
          "and verify the hash. Follow its required response schema and return exactly the requested verdict, "
          "committed at EXPECTED_VERDICT_PATH.")


def _observe_publication(record: dict) -> int:
    tip = _remote_verification(record)  # All network waits occur outside flock.
    with workflow._execution_writer_epoch(ROOT) as epoch:
        _actor_recheck(record, source_check=False)
        if _pending(record["request_path"]) != record:
            raise BindingError("BINDING_INTENT_PREIMAGE_CHANGED")
        if tip is None:
            print("UNKNOWN_PUSH_OUTCOME — inspect the existing binding and remote; no automatic retry.", file=sys.stderr)
            return 3
        if record["actor"] is not None and record["push_requested"]:
            local = workflow._team_local(ROOT)
            operation_id = record["actor"]["operation_id"]
            prior = local["operations"][operation_id]
            if prior["state"] == "RESERVED":
                observation = {"schema": "q3_team_binding_publication.v1", "binding_operation_id": record["operation_id"],
                               "request_commit": record["request_commit"], "request_sha256": record["request_sha256"],
                               "queue_commit": record["queue_commit"], "queue_sha256": record["queue_sha256"],
                               "remote_commit": tip}
                updated = {**local, "operations": {**local["operations"], operation_id:
                           {**prior, "state": "CONFIRMED", "evidence": observation}}}
                workflow._team_local_save(ROOT, local, updated, epoch)
        observed = {**record, "state": "PUBLISHED", "remote_commit": tip}
        _save_intent(observed, workflow._team_json(record), epoch)
    _delivery_line(observed)
    return 0


def bind(args, epoch, remote_base: str | None) -> tuple[dict, bool] | int:
    relative = Path(args.request)
    if relative.is_absolute():
        relative = relative.relative_to(ROOT)
    data = workflow._resume_file(ROOT, relative)
    if data is None or not data.endswith(b"\n"):
        raise BindingError("REQUEST_MISSING_OR_FINAL_LF_MISSING")
    request_path = str(relative)
    queue_path = str(QUEUE.relative_to(ROOT))
    prior = _pending(request_path)  # lookup and reservation are one writer epoch
    if prior is not None:
        _actor_recheck(prior, source_check=False)
        return prior, False
    actor = workflow.team_guard(ROOT, command="bind-request", paths=[request_path, queue_path], effect=not args.no_push)
    base_head = sh("git", "rev-parse", "HEAD")
    if not args.no_push and base_head != remote_base:
        raise BindingError("BINDING_UNPUBLISHED_BASE:reconcile existing local commits before binding")
    text = data.decode("utf-8")
    rid, boundary, call = (header(text, key) for key in ("REQUEST_ID", "BOUNDARY_ID", "CALL_CLASS"))
    original_queue = workflow._resume_file(ROOT, Path(queue_path))
    if original_queue is None:
        raise BindingError("QUEUE_MISSING")
    queue_text = original_queue.decode("utf-8")
    if re.search(r"(?m)^##\s+" + re.escape(rid) + r"(?:\s|$)", queue_text):
        raise SystemExit("queue already has " + rid)
    if sh("git", "status", "--porcelain", "--", queue_path):
        raise BindingError("QUEUE_DIRTY_PRESERVE_BEFORE_BINDING")
    record = {"schema": "q3_bind_intent.v1", "request_path": request_path, "queue_path": queue_path,
              "request_id": rid, "boundary_id": boundary, "request_sha256": workflow._resume_digest(data),
              "queue_pre_sha256": workflow._resume_digest(original_queue), "base_head": base_head,
              "actor": actor, "push_requested": not args.no_push, "bytes": len(data), "lines": data.count(b"\n"),
              "state": "INTENT"}
    record["operation_id"] = hashlib.sha256(workflow._team_json(record)).hexdigest()
    _save_intent(record, None, epoch)
    prefix = args.commit_prefix or "[Codex][rh_clean][Proshka-bind]"
    if sh("git", "status", "--porcelain", "--", request_path):
        epoch.recheck()
        sh("git", "add", "--", request_path)
        sh("git", "commit", "-q", "--only", "-m", f"{prefix} Request {rid}", "--", request_path)
    commit = sh("git", "rev-parse", "HEAD")
    blob = sh("git", "rev-parse", commit + ":" + request_path)
    if workflow._team_git(ROOT, "show", commit + ":" + request_path) != data:
        raise BindingError("REQUEST_COMMIT_BYTES_CHANGED")
    entry = ENTRY.format(rid=rid, title=args.title, status=args.status, rel=request_path, boundary=boundary, call=call,
                         intake=args.intake, preds=args.predictions, commit=commit, nbytes=len(data), nlines=data.count(b"\n"),
                         sha=record["request_sha256"], blob=blob, lf="yes")
    match = re.search(r"(?m)^## REQ-", queue_text)
    proposed = (queue_text[:match.start()] + entry + queue_text[match.start():] if match else queue_text + "\n" + entry).encode()
    prepared = {**record, "request_commit": commit, "request_blob": blob, "queue_sha256": workflow._resume_digest(proposed)}
    _save_intent(prepared, workflow._team_json(record), epoch)
    record = prepared
    workflow._resume_cas_bytes(ROOT, Path(queue_path), original_queue, proposed, epoch)
    try:
        output = sh(sys.executable, "orchestrator/workflow_runtime.py", "review-plan", "--attachment", request_path,
                    "--request-commit", commit, "--request-id", rid, "--boundary-id", boundary,
                    "--expected-sha256", record["request_sha256"], check=False)
        try:
            review = json.loads(output)
        except ValueError:
            review = {"status": "UNPARSED"}
        if review.get("status") != "REVIEW_DISPATCH_READY":
            raise BindingError("REVIEW_PLAN_HOLD")
    except BaseException as error:
        if workflow._resume_file(ROOT, Path(queue_path)) != proposed:
            raise QueueDriftError("QUEUE_CHANGED_PRESERVING_FOREIGN_BYTES") from error
        workflow._resume_cas_bytes(ROOT, Path(queue_path), proposed, original_queue, epoch)
        _save_intent({**record, "state": "ABORTED"}, workflow._team_json(record), epoch)
        if isinstance(error, BindingError) and str(error) == "REVIEW_PLAN_HOLD":
            print("HOLD — queue restored; reconcile before another attempt.")
            return 2
        raise
    _actor_recheck(record)
    epoch.recheck()
    sh("git", "add", "--", queue_path)
    sh("git", "commit", "-q", "--only", "-m", f"{prefix} Bind {rid}", "--", queue_path)
    binding = sh("git", "rev-parse", "HEAD")
    if workflow._team_git(ROOT, "show", binding + ":" + queue_path) != proposed:
        raise BindingError("QUEUE_COMMIT_BYTES_CHANGED")
    prepared = {**record, "state": "PREPARED", "queue_commit": binding,
                "queue_blob": sh("git", "rev-parse", binding + ":" + queue_path)}
    _save_intent(prepared, workflow._team_json(record), epoch)
    return prepared, True


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("request")
    parser.add_argument("--title", required=True)
    parser.add_argument("--predictions", default="see request")
    parser.add_argument("--intake", default="see request")
    parser.add_argument("--status", choices=["OPEN"], default="OPEN")
    parser.add_argument("--no-push", action="store_true")
    parser.add_argument("--commit-prefix")
    args = parser.parse_args()
    for name in ("title", "predictions", "intake", "commit_prefix"):
        value = getattr(args, name)
        if value is not None and (not value.strip() or "\n" in value or "\r" in value):
            parser.error("--" + name.replace("_", "-") + " must be a nonempty single line")
    relative = Path(args.request)
    if relative.is_absolute():
        relative = relative.relative_to(ROOT)
    # Actor check precedes network; the lock is released for remote observation.
    with workflow._execution_writer_epoch(ROOT):
        prior = _pending(str(relative))
        if prior is None:
            workflow.team_guard(ROOT, command="bind-request", paths=[str(relative), str(QUEUE.relative_to(ROOT))], effect=not args.no_push)
        else:
            _actor_recheck(prior, source_check=False)
    remote_base = None
    if prior is None and not args.no_push:
        try:
            remote_base = _remote_tip()
        except (BindingError, OSError, ValueError, subprocess.SubprocessError):
            print("BINDING_REMOTE_UNAVAILABLE — no binding or push attempted.", file=sys.stderr)
            return 3
    with workflow._execution_writer_epoch(ROOT) as epoch:
        prepared = bind(args, epoch, remote_base)
        if isinstance(prepared, int):
            return prepared
        record, fresh = prepared
        if fresh and not args.no_push:
            _actor_recheck(record)
            pending = {**record, "state": "PUSH_UNKNOWN"}
            _save_intent(pending, workflow._team_json(record), epoch)
            record = pending
    if fresh and args.no_push:
        print("UNPUBLISHED — binding saved; publish the pinned commits before dispatch.")
        return 0
    if fresh:
        try:
            if _remote_tip() != record["base_head"]:
                print("BINDING_REMOTE_CHANGED — pinned binding retained; no push attempted.", file=sys.stderr)
                return 3
            sh("git", "push", "-q", "origin", record["queue_commit"] + ":refs/heads/rh_clean")
        except (BindingError, OSError, subprocess.SubprocessError):
            pass  # A failed/lost client receipt does not establish the remote outcome.
    return _observe_publication(record)


if __name__ == "__main__":
    raise SystemExit(main())
