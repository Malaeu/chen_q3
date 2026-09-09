#!/usr/bin/env python3
"""bind_request.py — one command to bind a judge request (replaces the ad-hoc python heredocs of 2026-09-03/04).

Usage:
  python3 orchestrator/bind_request.py <request.txt> --title "<queue title>" [--predictions "<list>"] [--intake "<text>"] [--status OPEN]
Does, in order:
  1. reads REQUEST_ID / BOUNDARY_ID / CALL_CLASS from the request header;
  2. checks duplicate/dirty queue state, then commits only the request path if changed;
  3. computes commit, blob, sha256, lines, bytes, final-LF;
  4. inserts a queue entry at the top of docs/routeB_bus/PROSHKA_QUEUE.md (after the first '---' or before the first '## REQ-')
     using str.format on a template with NO bare substrings (fixes the `.replace("SHA", ...)` mangling);
  5. runs workflow_runtime.py review-plan and prints its status;
  6. commits + pushes the queue, prints the delivery line for the owner.
Never pushes if review-plan is not REVIEW_DISPATCH_READY (restores the queue on HOLD).
No automatic rebase: pinned request commits must remain stable.
Holds the canonical writer lock through binding, validation and publication.
"""
from __future__ import annotations
import argparse, hashlib, json, re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from orchestrator.workflow_runtime import _execution_writer_epoch

QUEUE = ROOT / "docs/routeB_bus/PROSHKA_QUEUE.md"

def sh(*a, check=True):
    return subprocess.run(a, cwd=ROOT, text=True, capture_output=True, check=check).stdout.strip()

def header(txt: str, key: str) -> str:
    m = re.search(rf"^{key}:\s*(.+)$", txt, re.M)
    if not m: sys.exit(f"missing header {key}")
    return m.group(1).strip()

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

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("request"); ap.add_argument("--title", required=True)
    ap.add_argument("--predictions", default="see request"); ap.add_argument("--intake", default="see request")
    ap.add_argument("--status", default="OPEN"); ap.add_argument("--no-push", action="store_true")
    ap.add_argument("--commit-prefix", help="Override the prefix for both request and binding commits")
    a = ap.parse_args()
    if a.status != "OPEN":
        ap.error("only OPEN requests can be bound for dispatch")
    if a.commit_prefix is not None and (not a.commit_prefix.strip() or "\n" in a.commit_prefix or "\r" in a.commit_prefix):
        ap.error("--commit-prefix must be a nonempty single line")
    with _execution_writer_epoch(ROOT) as epoch:
        return bind(a, epoch)

def bind(a, epoch) -> int:
    request_prefix = a.commit_prefix or "[Linux-Claude][rh_clean][Goal058]"
    bind_prefix = a.commit_prefix or "[Linux-Claude][rh_clean][Proshka-bind]"
    req = (ROOT / a.request).resolve(); rel = str(req.relative_to(ROOT))
    txt = req.read_text(encoding="utf-8")
    rid, boundary, call = header(txt, "REQUEST_ID"), header(txt, "BOUNDARY_ID"), header(txt, "CALL_CLASS")
    original_queue = QUEUE.read_bytes()
    q = original_queue.decode("utf-8")
    if re.search(rf"^##\s+{re.escape(rid)}(?:\s|$)", q, re.M):
        sys.exit(f"queue already has {rid}")
    queue_rel = str(QUEUE.relative_to(ROOT))
    if sh("git", "status", "--porcelain", "--", queue_rel):
        sys.exit("queue has uncommitted changes; preserve them before binding")
    if sh("git", "status", "--porcelain", "--", rel):
        epoch.recheck()
        sh("git", "add", "--", rel); sh("git", "commit", "-q", "--only", "-m", f"{request_prefix} Request {rid}", "--", rel)
    commit = sh("git", "rev-parse", "HEAD"); blob = sh("git", "rev-parse", f"HEAD:{rel}")
    data = req.read_bytes(); sha = hashlib.sha256(data).hexdigest()
    nbytes, nlines, lf = len(data), data.count(b"\n"), "yes" if data.endswith(b"\n") else "NO"
    entry = ENTRY.format(rid=rid, title=a.title, status=a.status, rel=rel, boundary=boundary, call=call,
                         intake=a.intake, preds=a.predictions, commit=commit, nbytes=nbytes, nlines=nlines, sha=sha, blob=blob, lf=lf)
    m = re.search(r"^## REQ-", q, re.M)
    q = q[:m.start()] + entry + q[m.start():] if m else q + "\n" + entry
    if QUEUE.read_bytes() != original_queue:
        sys.exit("queue changed during binding; rerun without overwriting it")
    epoch.recheck()
    QUEUE.write_text(q, encoding="utf-8")
    try:
        out = sh(sys.executable, "orchestrator/workflow_runtime.py", "review-plan", "--attachment", rel, "--request-commit", commit,
                 "--request-id", rid, "--boundary-id", boundary, "--expected-sha256", sha, check=False)
    except BaseException:
        epoch.recheck()
        QUEUE.write_bytes(original_queue)
        raise
    try: st = json.loads(out)
    except Exception: st = {"status": "UNPARSED", "holds": [out[-300:]]}
    print("review-plan:", st.get("status"), st.get("holds"))
    if st.get("status") != "REVIEW_DISPATCH_READY":
        epoch.recheck()
        QUEUE.write_bytes(original_queue)
        print("HOLD — queue restored; fix and rerun."); return 2
    epoch.recheck()
    sh("git", "add", "--", queue_rel); sh("git", "commit", "-q", "--only", "-m", f"{bind_prefix} Bind {rid}", "--", queue_rel)
    if not a.no_push:
        sh("git", "push", "-q", "origin", "HEAD:refs/heads/rh_clean")
    else:
        print("UNPUBLISHED — binding saved locally; publish the pinned commits before dispatch.")
        return 0
    print(f"\nLINE: Adjudicate {rid}. Authoritative byte-exact payload: {rel} at commit {commit} (blob {blob}, SHA-256 {sha}, {nlines} lines, {nbytes} bytes) on Malaeu/chen_q3 rh_clean; fetch it from GitHub and verify the hash. Follow its required response schema and return exactly the requested verdict, committed at EXPECTED_VERDICT_PATH.")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
