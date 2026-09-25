#!/usr/bin/env python3
"""One command at the end of a phase/checkpoint (plain mode, owner order 2026-09-25).

Portable: Linux and macOS (no bash-4 features, no GNU coreutils).

  scripts/phase_end.sh "commit message"            journal → check → shelf → literature → stats → commit → push → readback
  scripts/phase_end.sh "commit message" --no-log   same, without requiring today's journal entry (owner bypass)
  scripts/phase_end.sh --dry-run                   check → stats only

Steps:
  0. Journal: docs/Progress_Log.md needs "## <today> — ..." (insights, blockers, Zinger needles,
     why we are here, next move). Template: docs/Codex/NEXT.md «Конец фазы».
  1. q3_check on every changed/new Lean file under q3.lean.aristotle/Q3.
  2. Shelf refresh (semantic index via orchestrator/spine.py), non-fatal.
  2b. Literature: "- lit: ..." queries in NEXT.md → arXiv/Crossref (docs/literature/scan_<date>.json)
      and X posts/news via xurl (docs/literature/x_<date>.json, community signal only). Non-fatal.
      scite and Consensus are MCP-only: the agent runs them.
  3. AUTO-STATS block and "Updated:" line in docs/Codex/NEXT.md.
  4. git add, commit, pull --rebase, push.
  5. Readback: origin/rh_clean == HEAD.
"""

from __future__ import annotations

import datetime as dt
import json
import os
import re
import shutil
import subprocess
import sys
import urllib.parse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BRANCH = "rh_clean"
NEXT = ROOT / "docs/Codex/NEXT.md"
LOG = ROOT / "docs/Progress_Log.md"
LIT_DIR = ROOT / "docs/literature"

# qmd/xurl live in user-level bin dirs that non-interactive shells often miss (Linux and macOS).
for extra in ("~/.bun/bin", "~/.local/bin", "/opt/homebrew/bin", "/usr/local/bin"):
    p = str(Path(extra).expanduser())
    if p not in os.environ.get("PATH", "").split(os.pathsep):
        os.environ["PATH"] = os.environ.get("PATH", "") + os.pathsep + p
os.environ["GIT_OPTIONAL_LOCKS"] = "0"


def run(
    cmd: list[str], *, check: bool = True, timeout: float | None = None, capture: bool = False
) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd, cwd=ROOT, check=check, timeout=timeout, text=True, capture_output=capture
    )


def git(*args: str) -> str:
    return run(["git", *args], capture=True).stdout.strip()


def python() -> str:
    venv = ROOT / ".venv/bin/python"
    return str(venv) if venv.exists() else sys.executable


def lit_queries() -> list[str]:
    return [
        m.group(1).strip()
        for m in re.finditer(r"^- lit:\s*(.+)$", NEXT.read_text(encoding="utf-8"), re.M)
    ]


def changed_lean() -> list[str]:
    diff = run(
        ["git", "diff", "--name-only", f"origin/{BRANCH}", "--", "q3.lean.aristotle/Q3"],
        check=False,
        capture=True,
    ).stdout.split()
    new = git("ls-files", "--others", "--exclude-standard", "--", "q3.lean.aristotle/Q3").split()
    return sorted({f for f in diff + new if f.endswith(".lean") and (ROOT / f).is_file()})


def literature(today: str) -> None:
    queries = lit_queries()
    if not queries:
        print("   no '- lit:' queries in NEXT.md")
        return
    LIT_DIR.mkdir(parents=True, exist_ok=True)
    try:
        r = run(
            [python(), "scripts/literature_discovery.py", *queries, "--max-results", "5"],
            check=True,
            capture=True,
            timeout=180,
        )
        out = LIT_DIR / f"scan_{today}.json"
        out.write_text(r.stdout, encoding="utf-8")
        cands = json.loads(r.stdout).get("candidates", [])
        print(f"   arXiv/Crossref: {len(cands)} candidates → {out.relative_to(ROOT)}")
        for c in cands[:8]:
            print("   -", c.get("title", "")[:110])
    except Exception as exc:  # network, timeout, parse
        print(f"   WARN: arXiv/Crossref scan failed ({type(exc).__name__}) — non-fatal")
    if not shutil.which("xurl"):
        print("   WARN: xurl not installed — X search skipped")
        return
    rows = []
    for q in queries:
        for kind, path in (
            (
                "posts",
                f"/2/tweets/search/recent?query={urllib.parse.quote(q + ' -is:retweet')}"
                "&max_results=10&tweet.fields=created_at,author_id",
            ),
            ("news", f"/2/news/search?query={urllib.parse.quote(q)}"),
        ):
            try:
                data = json.loads(
                    run(["xurl", path], check=False, capture=True, timeout=60).stdout
                ).get("data", [])
            except Exception:
                data = []
            for d in data:
                rows.append(
                    {
                        "query": q,
                        "kind": kind,
                        "id": d.get("id") or d.get("rest_id"),
                        "created_at": d.get("created_at"),
                        "text": (d.get("text") or d.get("name") or d.get("summary") or "")[:500],
                    }
                )
    out = LIT_DIR / f"x_{today}.json"
    out.write_text(
        json.dumps(
            {"boundary": "COMMUNITY_SIGNAL_NOT_EVIDENCE", "rows": rows},
            ensure_ascii=False,
            indent=1,
        ),
        encoding="utf-8",
    )
    print(f"   X: {len(rows)} posts/news → {out.relative_to(ROOT)}")


def stats(today: str) -> None:
    text = NEXT.read_text(encoding="utf-8")
    try:
        ledger = json.loads(
            run([python(), "orchestrator/roof_port_ledger.py"], check=False, capture=True).stdout
            or "{}"
        )
    except json.JSONDecodeError:
        ledger = {}
    ports = ledger.get("ports", [])
    port_line = ", ".join(f"{p['port']}={p['status']}" for p in ports) or "UNAVAILABLE"
    goal = (ROOT / "docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md").read_text(
        encoding="utf-8"
    )
    gates = re.findall(r"^\|\s*\d+\s*\|\s*`(G[0-9a-z]+)`\s*\|[^|]*\|\s*(.+?)\s*\|\s*$", goal, re.M)
    closed = [g for g, st in gates if re.search(r"READY|PROVED", st)]
    open_ = [g for g, _ in gates if g not in closed]
    sorry = axiom = 0
    for f in (ROOT / "q3.lean.aristotle/Q3/Proofs/RouteB").rglob("*.lean"):
        body = f.read_text(encoding="utf-8", errors="replace")
        sorry += len(re.findall(r"\bsorry\b", body))
        axiom += len(re.findall(r"^\s*axiom\s", body, re.M))
    queue = (ROOT / "docs/routeB_bus/PROSHKA_QUEUE.md").read_text(encoding="utf-8")
    open_req = re.findall(r"^## (REQ-\S+).*·\s*OPEN\s*$", queue, re.M)
    head = git("rev-parse", "--short=8", "HEAD")
    block = "\n".join(
        [
            "<!-- AUTO-STATS:BEGIN (scripts/phase_end.sh — не править руками) -->",
            f"Статистика на {today}, HEAD {head}:",
            f"- Ворота Goal058: закрыто {len(closed)}/{len(gates)} ({', '.join(closed)}); открыто: {', '.join(open_)}",
            f"- Крыша: {ledger.get('port_summary', {}).get('jointly_bound', '?')}/{len(ports)} портов связано; {port_line}",
            f"- RouteB Lean: sorry={sorry}, axiom={axiom}",
            f"- Открытые запросы Прошке: {len(open_req)}"
            + (f" ({', '.join(open_req)})" if open_req else ""),
            "<!-- AUTO-STATS:END -->",
        ]
    )
    pattern = re.compile(r"<!-- AUTO-STATS:BEGIN.*?<!-- AUTO-STATS:END -->", re.S)
    text = (
        pattern.sub(block, text)
        if pattern.search(text)
        else text.replace("## Дорожная карта", block + "\n\n## Дорожная карта", 1)
    )
    text = re.sub(
        r"^Updated: .*$",
        f"Updated: {today} · by: scripts/phase_end.sh · HEAD at update: {head}",
        text,
        count=1,
        flags=re.M,
    )
    NEXT.write_text(text, encoding="utf-8")
    print(block)


def main() -> int:
    args = sys.argv[1:]
    dry, nolog = "--dry-run" in args, "--no-log" in args
    msg = next((a for a in args if not a.startswith("--")), "")
    if not dry and not msg:
        print(
            'usage: scripts/phase_end.sh "commit message" [--no-log] | --dry-run', file=sys.stderr
        )
        return 64
    today = dt.date.today().isoformat()

    print("== 0 Journal entry in docs/Progress_Log.md")
    if dry or nolog:
        print("   skipped")
    elif re.search(rf"^## {today}", LOG.read_text(encoding="utf-8"), re.M):
        print(f"   OK: entry for {today} present")
    else:
        print(
            f"   MISSING: add '## {today} — <what this phase found>' to docs/Progress_Log.md\n"
            "   (template: docs/Codex/NEXT.md «Конец фазы»; bypass: --no-log)",
            file=sys.stderr,
        )
        return 65

    print("== 1/5 Lean check of changed files")
    lean = changed_lean()
    if not lean:
        print("   no changed Lean files")
    for f in lean:
        print(f"   q3_check {f}")
        run(["bash", "scripts/q3_check.sh", f])

    print("== 2/5 Shelf refresh")
    if dry:
        print("   skipped (dry run)")
    elif shutil.which("qmd"):
        r = run(
            [python(), "orchestrator/spine.py", "--refresh", "--reason", "semantic-index-refresh"],
            check=False,
            capture=True,
        )
        print(
            "   OK: semantic shelf refreshed"
            if r.returncode == 0
            else "   WARN: shelf refresh failed (non-fatal)"
        )
    else:
        print("   WARN: qmd not installed on this machine — shelf not refreshed")

    print("== 2b Literature")
    if dry:
        print("   skipped (dry run)")
    else:
        literature(today)

    print("== 3/5 Stats block in docs/Codex/NEXT.md")
    stats(today)
    if dry:
        print("== 4/5, 5/5 skipped (dry run). Review: git diff docs/Codex/NEXT.md")
        return 0

    print("== 4/5 Commit and push")
    run(["git", "add", "-u"])
    paths = ["docs/Codex", "docs/routeB_bus", "docs/Progress_Log.md", *lean]
    if LIT_DIR.is_dir():
        paths.append("docs/literature")
    run(["git", "add", "--", *paths])
    if run(["git", "diff", "--cached", "--quiet"], check=False).returncode == 0:
        print("   nothing to commit")
    else:
        run(["git", "commit", "-q", "-m", msg])
    run(["git", "pull", "-q", "--rebase", "origin", BRANCH])
    run(["git", "push", "-q", "origin", BRANCH])

    print("== 5/5 Readback")
    run(["git", "fetch", "-q", "origin", BRANCH])
    if git("rev-parse", "HEAD") == git("rev-parse", f"origin/{BRANCH}"):
        print(f"   OK: origin/{BRANCH} == HEAD ({git('rev-parse', '--short', 'HEAD')})")
        return 0
    print("   FAIL: HEAD != origin", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
