#!/usr/bin/env python3
"""One command at the end of a phase/checkpoint (plain mode, owner order 2026-09-25).

Portable: Linux and macOS (no bash-4 features, no GNU coreutils).

  scripts/phase_end.sh "commit message" --scope PATH [--scope PATH ...]
                                                     journal → check → shelf → literature → stats → scoped commit → push → readback
  scripts/phase_end.sh "commit message" --scope PATH --no-log
                                                     same, without requiring today's journal entry (owner bypass)
  scripts/phase_end.sh --dry-run                   read-only preview; no checks or network

Steps:
  0. Journal: docs/Progress_Log.md needs "## <today> — ..." (insights, blockers, Zinger needles,
     why we are here, next move). Template: docs/Codex/NEXT.md «Конец фазы».
  1. q3_check on every changed/new Lean file under q3.lean.aristotle/Q3.
  2. Shelf refresh (semantic index via orchestrator/spine.py), non-fatal.
  2b. Literature: "- lit: ..." queries in NEXT.md → arXiv/Crossref (docs/literature/scan_<date>.json)
      and X posts/news via xurl (docs/literature/x_<date>.json, community signal only). Non-fatal.
      scite and Consensus are MCP-only: the agent runs them.
  3. AUTO-STATS block and "Updated:" line in docs/Codex/NEXT.md.
  4. stage only the selected paths, commit, pull --rebase, push.
  5. Readback: origin/rh_clean == HEAD.
"""

from __future__ import annotations

import argparse
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


def run(
    cmd: list[str], *, check: bool = True, timeout: float | None = None, capture: bool = False
) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd, cwd=ROOT, check=check, timeout=timeout, text=True, capture_output=capture
    )


def git(*args: str) -> str:
    return run(["git", *args], capture=True).stdout.strip()


def configure_environment() -> None:
    # qmd/xurl live in user-level bin dirs that non-interactive shells often miss.
    for extra in ("~/.bun/bin", "~/.local/bin", "/opt/homebrew/bin", "/usr/local/bin"):
        p = str(Path(extra).expanduser())
        if p not in os.environ.get("PATH", "").split(os.pathsep):
            os.environ["PATH"] = os.environ.get("PATH", "") + os.pathsep + p
    os.environ["GIT_OPTIONAL_LOCKS"] = "0"


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run phase closeout and commit only explicitly scoped paths, or the "
            "closeout-generated files when starting from a clean worktree."
        ),
        epilog=(
            'Example: scripts/phase_end.sh "phase complete" '
            "--scope q3.lean.aristotle/Q3/Proofs/RouteB/Example.lean "
            "--scope docs/Codex/NEXT.md"
        ),
    )
    parser.add_argument("message", nargs="?", help="commit message")
    parser.add_argument(
        "--scope",
        action="append",
        metavar="PATH",
        help=(
            "repo-relative file or directory (directories include descendants); "
            "repeat for multiple paths; "
            "required when starting dirty; other dirty paths are preserved and block push"
        ),
    )
    parser.add_argument(
        "--no-log", action="store_true", help="skip the required journal-entry check"
    )
    parser.add_argument(
        "--dry-run", action="store_true", help="read-only preview; runs no checks or network calls"
    )
    return parser.parse_args(argv)


def normalize_scope(paths: list[str]) -> list[str]:
    normalized: list[str] = []
    for raw in paths:
        path = Path(raw)
        if not raw or path.is_absolute() or ".." in path.parts:
            raise ValueError(f"scope must stay inside the repository: {raw!r}")
        rel = path.as_posix().rstrip("/")
        if rel in ("", ".", ".git") or rel.startswith(".git/"):
            raise ValueError(f"scope must name a repository path, not its root or Git metadata: {raw!r}")
        if rel not in normalized:
            normalized.append(rel)
    return normalized


def scope_pathspecs(paths: list[str]) -> list[str]:
    # Literal pathspecs prevent wildcard or pathspec-magic text from widening scope.
    return [f":(literal){path}" for path in paths]


def scope_contains_path(scopes: list[str], candidate: str) -> bool:
    path = Path(candidate)
    return any(path == Path(scope) or Path(scope) in path.parents for scope in scopes)


def worktree_status() -> str:
    return git("status", "--porcelain", "--untracked-files=all")


def commit_scoped(message: str, paths: list[str]) -> bool:
    if not paths:
        print("   nothing to commit in the generated scope")
        return False
    pathspecs = scope_pathspecs(paths)
    run(["git", "add", "--", *pathspecs])
    if run(
        ["git", "diff", "--cached", "--quiet", "--", *pathspecs], check=False
    ).returncode == 0:
        print("   nothing to commit in the requested scope")
        return False
    run(["git", "commit", "--only", "-q", "-m", message, "--", *pathspecs])
    return True


def python() -> str:
    venv = ROOT / ".venv/bin/python"
    return str(venv) if venv.exists() else sys.executable


def lit_queries() -> list[str]:
    return [
        m.group(1).strip()
        for m in re.finditer(r"^- lit:\s*(.+)$", NEXT.read_text(encoding="utf-8"), re.M)
    ]


def changed_lean(scopes: list[str] | None = None) -> list[str]:
    diff = run(
        ["git", "diff", "--name-only", f"origin/{BRANCH}", "--", "q3.lean.aristotle/Q3"],
        check=False,
        capture=True,
    ).stdout.split()
    new = git("ls-files", "--others", "--exclude-standard", "--", "q3.lean.aristotle/Q3").split()
    files = sorted({f for f in diff + new if f.endswith(".lean") and (ROOT / f).is_file()})
    if scopes is not None:
        files = [f for f in files if scope_contains_path(scopes, f)]
    return files


def literature(today: str, allowed_outputs: set[str] | None = None) -> list[str]:
    written: list[str] = []
    queries = lit_queries()
    if not queries:
        print("   no '- lit:' queries in NEXT.md")
        return written
    scan_out = (LIT_DIR / f"scan_{today}.json").relative_to(ROOT).as_posix()
    x_out = (LIT_DIR / f"x_{today}.json").relative_to(ROOT).as_posix()
    if allowed_outputs is None or scan_out in allowed_outputs:
        LIT_DIR.mkdir(parents=True, exist_ok=True)
        try:
            r = run(
                [python(), "scripts/literature_discovery.py", *queries, "--max-results", "5"],
                check=True,
                capture=True,
                timeout=180,
            )
            out = ROOT / scan_out
            out.write_text(r.stdout, encoding="utf-8")
            written.append(scan_out)
            cands = json.loads(r.stdout).get("candidates", [])
            print(f"   arXiv/Crossref: {len(cands)} candidates → {scan_out}")
            for c in cands[:8]:
                print("   -", c.get("title", "")[:110])
        except Exception as exc:  # network, timeout, parse
            print(f"   WARN: arXiv/Crossref scan failed ({type(exc).__name__}) — non-fatal")
    else:
        print(f"   arXiv/Crossref skipped (outside --scope): {scan_out}")
    if allowed_outputs is not None and x_out not in allowed_outputs:
        print(f"   X search skipped (outside --scope): {x_out}")
        return written
    if not shutil.which("xurl"):
        print("   WARN: xurl not installed — X search skipped")
        return written
    LIT_DIR.mkdir(parents=True, exist_ok=True)
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
    out = ROOT / x_out
    out.write_text(
        json.dumps(
            {"boundary": "COMMUNITY_SIGNAL_NOT_EVIDENCE", "rows": rows},
            ensure_ascii=False,
            indent=1,
        ),
        encoding="utf-8",
    )
    written.append(x_out)
    print(f"   X: {len(rows)} posts/news → {x_out}")
    return written


def stats(today: str) -> str:
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
            f"- Goal058 (текстовая метка READY/PROVED): {len(closed)}/{len(gates)} ({', '.join(closed)}); без метки: {', '.join(open_)}",
            f"- Крыша (статусы ledger): {ledger.get('port_summary', {}).get('jointly_bound', '?')}/{len(ports)} портов со статусом jointly_bound; {port_line}",
            f"- RouteB Lean (текстовый поиск, не kernel-аудит): sorry={sorry}, строк axiom={axiom}",
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
    return NEXT.relative_to(ROOT).as_posix()


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    if args.dry_run:
        try:
            scopes = normalize_scope(args.scope or [])
        except ValueError as exc:
            print(f"ERROR: {exc}", file=sys.stderr)
            return 64
        print("== Dry run: read-only preview; no files, Lean checks, or network calls touched")
        if scopes:
            print("   requested commit scope: " + ", ".join(scopes))
        else:
            print(
                "   no explicit scope; dirty worktrees will be refused, while a clean run "
                "commits only generated summary/literature files"
            )
        return 0
    if not args.message:
        print(
            'usage: scripts/phase_end.sh "commit message" [--scope PATH ...] '
            "[--no-log] | --dry-run",
            file=sys.stderr,
        )
        return 64
    try:
        scopes = normalize_scope(args.scope or [])
    except ValueError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 64

    current_branch = git("branch", "--show-current")
    if current_branch != BRANCH:
        print(
            f"ERROR: refusing closeout on branch {current_branch!r}; expected {BRANCH!r}.",
            file=sys.stderr,
        )
        return 64

    configure_environment()
    initially_dirty = bool(worktree_status())
    if initially_dirty and not scopes:
        print(
            "ERROR: refusing a no-scope run because the worktree has staged, unstaged, "
            "or untracked changes; pass --scope PATH for each path this run may commit.",
            file=sys.stderr,
        )
        return 64

    today = dt.date.today().isoformat()

    print("== 0 Journal entry in docs/Progress_Log.md")
    if args.no_log:
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
    lean = changed_lean(scopes if scopes else None)
    if not lean:
        print("   no changed Lean files")
    for f in lean:
        print(f"   q3_check {f}")
        run(["bash", "scripts/q3_check.sh", f])

    print("== 2/5 Shelf refresh")
    if scopes:
        print("   skipped (derived shelf refresh is outside --scope)")
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
    if scopes:
        scan_out = (LIT_DIR / f"scan_{today}.json").relative_to(ROOT).as_posix()
        x_out = (LIT_DIR / f"x_{today}.json").relative_to(ROOT).as_posix()
        allowed_literature = {
            path for path in (scan_out, x_out) if scope_contains_path(scopes, path)
        }
        generated_paths = literature(today, allowed_literature) if allowed_literature else []
        if not allowed_literature:
            print("   skipped (current literature outputs are outside --scope)")
    else:
        generated_paths = literature(today)

    print("== 3/5 Stats block in docs/Codex/NEXT.md")
    next_path = NEXT.relative_to(ROOT).as_posix()
    if not scopes or scope_contains_path(scopes, next_path):
        generated_paths.append(stats(today))
    else:
        print(f"   skipped (outside --scope): {next_path}")

    print("== 4/5 Commit and push")
    commit_paths = scopes if scopes else normalize_scope(generated_paths)
    commit_scoped(args.message, commit_paths)
    remaining = worktree_status()
    if remaining:
        print(
            "ERROR: out-of-scope changes remain; commit completed where applicable, "
            "so pull/rebase and push were skipped to preserve them.",
            file=sys.stderr,
        )
        return 1
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
