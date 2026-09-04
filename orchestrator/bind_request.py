#!/usr/bin/env python3
"""bind_request.py — one command to bind a judge request (replaces the ad-hoc python heredocs of 2026-09-03/04).

Usage:
  python3 orchestrator/bind_request.py <request.txt> --title "<queue title>" [--predictions "<list>"] [--intake "<text>"] [--status OPEN]
Does, in order:
  1. reads REQUEST_ID / BOUNDARY_ID / CALL_CLASS from the request header;
  2. commits the request if it is not yet committed (by path);
  3. computes commit, blob, sha256, lines, bytes, final-LF;
  4. inserts a queue entry at the top of docs/routeB_bus/PROSHKA_QUEUE.md (after the first '---' or before the first '## REQ-')
     using str.format on a template with NO bare substrings (fixes the `.replace("SHA", ...)` mangling);
  5. runs workflow_runtime.py review-plan and prints its status;
  6. commits + pushes the queue, prints the delivery line for the owner.
Never pushes if review-plan is not REVIEW_DISPATCH_READY (prints HOLD and stops before the queue commit).
"""
from __future__ import annotations
import argparse, hashlib, json, re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
QUEUE = ROOT / "docs/routeB_bus/PROSHKA_QUEUE.md"
TRAILER = "\n\nCo-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>\nClaude-Session: https://claude.ai/code/session_01N8cwEvtbQ33okoggUqWKqK"

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
    a = ap.parse_args()
    req = (ROOT / a.request).resolve(); rel = str(req.relative_to(ROOT))
    txt = req.read_text(encoding="utf-8")
    rid, boundary, call = header(txt, "REQUEST_ID"), header(txt, "BOUNDARY_ID"), header(txt, "CALL_CLASS")
    if sh("git", "status", "--porcelain", "--", rel):
        sh("git", "add", rel); sh("git", "commit", "-q", "-m", f"[Linux-Claude][rh_clean][Goal058] Request {rid}" + TRAILER)
    commit = sh("git", "rev-parse", "HEAD"); blob = sh("git", "rev-parse", f"HEAD:{rel}")
    data = req.read_bytes(); sha = hashlib.sha256(data).hexdigest()
    nbytes, nlines, lf = len(data), data.count(b"\n"), "yes" if data.endswith(b"\n") else "NO"
    q = QUEUE.read_text(encoding="utf-8")
    if f"## {rid} " in q: sys.exit(f"queue already has {rid}")
    entry = ENTRY.format(rid=rid, title=a.title, status=a.status, rel=rel, boundary=boundary, call=call,
                         intake=a.intake, preds=a.predictions, commit=commit, nbytes=nbytes, nlines=nlines, sha=sha, blob=blob, lf=lf)
    m = re.search(r"^## REQ-", q, re.M)
    q = q[:m.start()] + entry + q[m.start():] if m else q + "\n" + entry
    QUEUE.write_text(q, encoding="utf-8")
    out = sh(sys.executable, "orchestrator/workflow_runtime.py", "review-plan", "--attachment", rel, "--request-commit", commit,
             "--request-id", rid, "--boundary-id", boundary, "--expected-sha256", sha, check=False)
    try: st = json.loads(out)
    except Exception: st = {"status": "UNPARSED", "holds": [out[-300:]]}
    print("review-plan:", st.get("status"), st.get("holds"))
    if st.get("status") != "REVIEW_DISPATCH_READY":
        print("HOLD — queue edited but NOT committed; fix and rerun."); return 2
    sh("git", "add", str(QUEUE.relative_to(ROOT))); sh("git", "commit", "-q", "-m", f"[Linux-Claude][rh_clean][Proshka-bind] Bind {rid}" + TRAILER)
    if not a.no_push:
        sh("git", "fetch", "-q", "origin", "rh_clean"); sh("git", "rebase", "-q", "--autostash", "origin/rh_clean"); sh("git", "push", "-q", "origin", "rh_clean")
    print(f"\nLINE: Adjudicate {rid}. Authoritative byte-exact payload: {rel} at commit {commit} (blob {blob}, SHA-256 {sha}, {nlines} lines, {nbytes} bytes) on Malaeu/chen_q3 rh_clean; fetch it from GitHub and verify the hash. Follow its required response schema and return exactly the requested verdict, committed at EXPECTED_VERDICT_PATH.")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
