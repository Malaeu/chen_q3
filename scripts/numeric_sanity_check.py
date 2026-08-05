#!/usr/bin/env python3
"""Run explicitly configured numeric diagnostics as non-authoritative evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shlex
import subprocess
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = (Path(__file__).resolve().parents[1] / "full" / "q3.lean.aristotle").resolve()
ACTIVE_DIR = ROOT / "ACTIVE"


def now_utc() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    if not path.is_file():
        raise FileNotFoundError(path)
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"expected JSON object: {path}")
    return data


def normalize_command(command: object) -> list[str] | None:
    if command is None:
        return None
    if isinstance(command, list) and all(isinstance(item, str) for item in command):
        return command
    if isinstance(command, str):
        return shlex.split(command)
    raise ValueError("command must be a string or a list of strings")


def tail(text: str, limit: int = 2000) -> str:
    return text if len(text) <= limit else text[-limit:]


def resolve_cwd(value: object, root: Path) -> Path:
    path = Path(str(value)).expanduser() if value else root
    if not path.is_absolute():
        path = root / path
    path = path.resolve()
    try:
        path.relative_to(root.resolve())
    except ValueError as exc:
        raise ValueError(f"numeric check cwd escapes project root: {path}") from exc
    return path


def validate_checks(checks: list[dict[str, Any]]) -> None:
    identifiers: set[str] = set()
    for index, item in enumerate(checks, start=1):
        check_id = str(item.get("id") or "").strip()
        if not check_id:
            raise ValueError(f"numeric check #{index} has no id")
        if check_id in identifiers:
            raise ValueError(f"duplicate numeric check id: {check_id}")
        identifiers.add(check_id)
        if normalize_command(item.get("command")) is None:
            raise ValueError(f"numeric check has no command: {check_id}")


def run_config(
    config: dict[str, Any],
    *,
    root: Path = ROOT,
    default_timeout: int = 60,
    generated_at: str | None = None,
) -> dict[str, Any]:
    raw_checks = config.get("checks", [])
    if not isinstance(raw_checks, list):
        raise ValueError("checks must be a list")
    checks = [dict(item) for item in raw_checks]
    validate_checks(checks)
    results: list[dict[str, Any]] = []
    for item in checks:
        check_id = str(item["id"])
        command = normalize_command(item["command"])
        assert command is not None
        cwd = resolve_cwd(item.get("cwd"), root)
        timeout_s = int(item.get("timeout_s", default_timeout))
        if timeout_s <= 0:
            raise ValueError(f"timeout must be positive: {check_id}")
        started = time.monotonic()
        timed_out = False
        try:
            proc = subprocess.run(
                command,
                cwd=cwd,
                capture_output=True,
                text=True,
                timeout=timeout_s,
            )
            exit_code = proc.returncode
            stdout = proc.stdout or ""
            stderr = proc.stderr or ""
            expected = int(item.get("expect_exit_code", 0))
            status = "PASS" if exit_code == expected else "FAIL"
        except subprocess.TimeoutExpired as exc:
            timed_out = True
            exit_code = None
            stdout = (exc.stdout or "") if isinstance(exc.stdout, str) else ""
            stderr = (exc.stderr or "") if isinstance(exc.stderr, str) else ""
            status = "TIMEOUT"
        duration = round(time.monotonic() - started, 3)
        results.append({
            "id": check_id,
            "evidence_class": "NUMERIC_EVIDENCE_ONLY",
            "status": status,
            "command": command,
            "cwd": str(cwd),
            "exit_code": exit_code,
            "duration_s": duration,
            "timed_out": timed_out,
            "stdout_sha256": sha256_text(stdout),
            "stderr_sha256": sha256_text(stderr),
            "stdout_tail": tail(stdout),
            "stderr_tail": tail(stderr),
            "notes": item.get("notes"),
            "target_file": item.get("target_file"),
        })

    counts = {
        status: sum(1 for result in results if result["status"] == status)
        for status in ("PASS", "FAIL", "TIMEOUT")
    }
    return {
        "schema_version": "2.0",
        "sensor_kind": "NUMERIC_EVIDENCE_COMMAND_RUNNER",
        "generated_at": generated_at or now_utc(),
        "coverage_status": "CONFIGURED" if results else "EMPTY_CONFIG",
        "boundary": {
            "evidence_only": True,
            "not_lean_authority": True,
            "not_route_kill": True,
            "not_taint_input": True,
        },
        "summary": {"configured": len(results), **counts},
        "checks": results,
    }


def render_markdown(report: dict[str, Any]) -> str:
    lines = [
        f"# Numeric Evidence Report — {report['generated_at']}",
        "",
        "**Authority:** evidence only; not Lean authority, proof status, taint, or route kill.",
        f"**Coverage:** `{report['coverage_status']}`",
        f"**Configured checks:** {report['summary']['configured']}",
        "",
    ]
    if not report["checks"]:
        lines.append("_No numeric diagnostics are configured. This is zero coverage, not PASS._")
    for result in report["checks"]:
        lines += [
            f"## {result['id']}",
            f"- Status: `{result['status']}`",
            f"- Command: `{' '.join(result['command'])}`",
            f"- Exit code: `{result['exit_code']}`",
            f"- Duration: `{result['duration_s']}s`",
            f"- stdout SHA-256: `{result['stdout_sha256']}`",
            f"- stderr SHA-256: `{result['stderr_sha256']}`",
            "",
        ]
    return "\n".join(lines) + "\n"


def atomic_write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temp_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    os.close(descriptor)
    temp_path = Path(temp_name)
    try:
        temp_path.write_text(content, encoding="utf-8")
        os.chmod(temp_path, 0o644)
        os.replace(temp_path, path)
    except Exception:
        temp_path.unlink(missing_ok=True)
        raise


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", default=str(ACTIVE_DIR / "graphs" / "NUMERIC_CHECKS.json"))
    parser.add_argument("--out", default=str(ACTIVE_DIR / "graphs" / "NUMERIC_CHECKS_REPORT.json"))
    parser.add_argument("--md", default=str(ACTIVE_DIR / "graphs" / "NUMERIC_CHECKS_REPORT.md"))
    parser.add_argument("--strict", action="store_true")
    parser.add_argument("--require-configured", action="store_true")
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args()
    report = run_config(load_json(Path(args.config)), default_timeout=args.timeout)
    atomic_write(Path(args.out), json.dumps(report, indent=2) + "\n")
    atomic_write(Path(args.md), render_markdown(report))
    print(
        f"Wrote {args.out} and {args.md}; coverage={report['coverage_status']} "
        f"checks={report['summary']['configured']}"
    )
    if args.require_configured and report["coverage_status"] == "EMPTY_CONFIG":
        return 2
    if args.strict and (report["summary"]["FAIL"] or report["summary"]["TIMEOUT"]):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
