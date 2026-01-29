#!/usr/bin/env python3
import argparse
import json
import shlex
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "full" / "q3.lean.aristotle"
ACTIVE_DIR = ROOT / "ACTIVE"


def now_utc() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")


def load_json(path: Path, default):
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def tail(text: str, limit: int = 2000) -> str:
    if text is None:
        return ""
    return text if len(text) <= limit else text[-limit:]


def run_check(cmd, cwd: Path | None, timeout_s: int) -> tuple[int, str, str, float]:
    start = time.time()
    proc = subprocess.run(
        cmd,
        cwd=cwd,
        capture_output=True,
        text=True,
        timeout=timeout_s,
    )
    duration = time.time() - start
    return proc.returncode, proc.stdout, proc.stderr, duration


def normalize_command(command):
    if command is None:
        return None
    if isinstance(command, list):
        return command
    if isinstance(command, str):
        return shlex.split(command)
    raise ValueError("command must be string or list")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--config",
        default=str(ACTIVE_DIR / "graphs" / "NUMERIC_CHECKS.json"),
        help="input config JSON",
    )
    ap.add_argument(
        "--out",
        default=str(ACTIVE_DIR / "graphs" / "NUMERIC_CHECKS_REPORT.json"),
        help="output report JSON",
    )
    ap.add_argument(
        "--md",
        default=str(ACTIVE_DIR / "graphs" / "NUMERIC_CHECKS_REPORT.md"),
        help="output report Markdown",
    )
    ap.add_argument(
        "--write-back",
        action="store_true",
        help="write updated status back into config JSON",
    )
    ap.add_argument(
        "--strict",
        action="store_true",
        help="exit nonzero if any check fails",
    )
    ap.add_argument(
        "--timeout",
        type=int,
        default=60,
        help="default timeout seconds for each check",
    )
    args = ap.parse_args()

    config_path = Path(args.config)
    config = load_json(config_path, {"checks": []})
    checks = config.get("checks", [])

    results = []
    any_fail = False
    for item in checks:
        cid = item.get("id")
        command = normalize_command(item.get("command"))
        timeout_s = int(item.get("timeout_s", args.timeout))
        cwd = item.get("cwd")
        cwd_path = Path(cwd) if cwd else None
        if cwd_path and not cwd_path.is_absolute():
            cwd_path = (ROOT / cwd_path).resolve()

        status = item.get("status", "UNKNOWN").upper()
        exit_code = None
        out = ""
        err = ""
        duration = 0.0
        if command:
            exit_code, out, err, duration = run_check(command, cwd_path, timeout_s)
            status = "PASS" if exit_code == int(item.get("expect_exit_code", 0)) else "FAIL"
        if status == "FAIL":
            any_fail = True

        results.append(
            {
                "id": cid,
                "status": status,
                "command": command,
                "cwd": str(cwd_path) if cwd_path else None,
                "exit_code": exit_code,
                "duration_s": round(duration, 3),
                "stdout_tail": tail(out),
                "stderr_tail": tail(err),
                "notes": item.get("notes"),
            }
        )

        if args.write_back:
            item["status"] = status
            item["last_run"] = now_utc()

    report = {
        "schema_version": "1.0",
        "generated_at": now_utc(),
        "checks": results,
    }

    Path(args.out).write_text(json.dumps(report, indent=2), encoding="utf-8")

    md = []
    md.append(f"# Numeric Sanity Check Report — {report['generated_at']}")
    md.append("")
    md.append(f"**Checks:** {len(results)}")
    md.append("")
    for r in results:
        md.append(f"## {r.get('id')}")
        md.append(f"- Status: `{r.get('status')}`")
        if r.get("command"):
            md.append(f"- Command: `{' '.join(r['command'])}`")
        if r.get("exit_code") is not None:
            md.append(f"- Exit code: `{r.get('exit_code')}`")
        if r.get("duration_s"):
            md.append(f"- Duration: `{r.get('duration_s')}s`")
        if r.get("notes"):
            md.append(f"- Notes: {r.get('notes')}")
        md.append("")

    Path(args.md).write_text("\n".join(md) + "\n", encoding="utf-8")

    if args.write_back:
        config["generated_at"] = now_utc()
        config_path.write_text(json.dumps(config, indent=2), encoding="utf-8")

    if args.strict and any_fail:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
