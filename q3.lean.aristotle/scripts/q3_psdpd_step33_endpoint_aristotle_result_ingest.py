#!/usr/bin/env python3
"""Fail-closed Aristotle result ingest helper for Step33 endpoint packages.

This script does not integrate returned code.  It records the project status and,
when a result is available, downloads, unpacks, scans, and Lean-checks the
returned Lean files so the next local step can decide whether integration is
allowed.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import tarfile
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DEFAULT_PROJECT_ID = "3cd86d8e-6e0b-4a7f-a027-adecacb71b6f"

SCRIPT = Path(__file__).resolve()
Q3_ROOT = SCRIPT.parents[1]
REPO_ROOT = SCRIPT.parents[2]
ACTIVE_DIR = Q3_ROOT / "ACTIVE/requests/step33_bootstrap"
OUTPUT_DIR = Q3_ROOT / "aristotle_output"

MARKER_RE = re.compile(r"\b(sorry|admit|axiom|unsafe)\b|exact\?")


@dataclass
class CommandResult:
    cmd: list[str]
    cwd: str
    returncode: int
    stdout: str
    stderr: str


def run(cmd: list[str], cwd: Path) -> CommandResult:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    return CommandResult(
        cmd=cmd,
        cwd=str(cwd),
        returncode=proc.returncode,
        stdout=proc.stdout,
        stderr=proc.stderr,
    )


def aristotle_cmd() -> str:
    local = REPO_ROOT / ".venv/bin/aristotle"
    if local.exists():
        return str(local)
    found = shutil.which("aristotle")
    if found:
        return found
    return "aristotle"


def parse_status(project_id: str, list_stdout: str) -> dict[str, str]:
    for raw in list_stdout.splitlines():
        line = raw.strip()
        if not line.startswith(project_id):
            continue
        parts = line.split()
        if len(parts) < 3:
            return {"id": project_id, "status": "UNKNOWN", "progress": "UNKNOWN", "raw": line}
        return {
            "id": project_id,
            "status": parts[1],
            "progress": parts[-1],
            "raw": line,
        }
    return {"id": project_id, "status": "NOT_FOUND", "progress": "UNKNOWN", "raw": ""}


def safe_extract_tar(tar_path: Path, dest: Path) -> None:
    dest_resolved = dest.resolve()
    with tarfile.open(tar_path, "r:gz") as tar:
        for member in tar.getmembers():
            target = (dest / member.name).resolve()
            if not str(target).startswith(str(dest_resolved)):
                raise RuntimeError(f"refusing path-traversal tar member: {member.name}")
        tar.extractall(dest)


def scan_markers(paths: list[Path]) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for path in paths:
        for lineno, line in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), start=1):
            if MARKER_RE.search(line):
                hits.append({"file": str(path), "line": lineno, "text": line.strip()})
    return hits


def write_reports(report: dict[str, Any], json_path: Path, md_path: Path) -> None:
    json_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    status = report["status"]["status"]
    progress = report["status"]["progress"]
    project_id = report["projectId"]
    integration = report["integrationAllowed"]
    marker_count = len(report.get("markerHits", []))
    lean_failures = [
        item for item in report.get("leanChecks", [])
        if item["result"]["returncode"] != 0
    ]

    lines = [
        "# Step33 Endpoint Aristotle Result Ingest",
        "",
        "status: fail-closed helper output",
        f"updated: {report['updatedAt']}",
        f"project_id: `{project_id}`",
        f"project_status: `{status}`",
        f"project_progress: `{progress}`",
        f"integration_allowed: `{str(integration).lower()}`",
        "",
        "## Decision",
        "",
    ]
    if integration:
        lines.append("Returned Lean files passed marker scan and local Lean checks. Manual review/integration is still required.")
    elif status in {"IN_PROGRESS", "QUEUED"}:
        lines.append("Project is still running. No result was downloaded or integrated.")
    elif status == "NOT_FOUND":
        lines.append("Project was not found in the Aristotle list output.")
    else:
        lines.append("Do not integrate yet. See marker hits, Lean failures, or command failures below.")

    lines.extend([
        "",
        "## Result",
        "",
        f"- tarball: `{report.get('tarball', '')}`",
        f"- extract_dir: `{report.get('extractDir', '')}`",
        f"- lean_files: `{len(report.get('leanFiles', []))}`",
        f"- marker_hits: `{marker_count}`",
        f"- lean_failures: `{len(lean_failures)}`",
        "",
        "## Commands",
        "",
    ])
    for item in report["commands"]:
        lines.append(f"- `{ ' '.join(item['cmd']) }` -> `{item['returncode']}`")

    if marker_count:
        lines.extend(["", "## Marker Hits", ""])
        for hit in report["markerHits"][:50]:
            lines.append(f"- `{hit['file']}:{hit['line']}`: `{hit['text']}`")
        if marker_count > 50:
            lines.append(f"- ... {marker_count - 50} more")

    if lean_failures:
        lines.extend(["", "## Lean Failures", ""])
        for item in lean_failures:
            lines.append(f"- `{ ' '.join(item['result']['cmd']) }`")

    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project-id", default=DEFAULT_PROJECT_ID)
    parser.add_argument("--json", type=Path, default=ACTIVE_DIR / "a_endpoint_aristotle_result_ingest.json")
    parser.add_argument("--md", type=Path, default=ACTIVE_DIR / "a_endpoint_aristotle_result_ingest.md")
    args = parser.parse_args()

    project_id = args.project_id
    aristotle = aristotle_cmd()
    commands: list[dict[str, Any]] = []

    list_cmd = [
        aristotle,
        "list",
        "--status",
        "QUEUED",
        "IN_PROGRESS",
        "COMPLETE",
        "COMPLETE_WITH_ERRORS",
        "FAILED",
        "--limit",
        "20",
    ]
    list_result = run(list_cmd, REPO_ROOT)
    commands.append(asdict(list_result))
    status = parse_status(project_id, list_result.stdout)

    report: dict[str, Any] = {
        "updatedAt": datetime.now(timezone.utc).isoformat(),
        "projectId": project_id,
        "status": status,
        "commands": commands,
        "tarball": "",
        "extractDir": "",
        "leanFiles": [],
        "markerHits": [],
        "leanChecks": [],
        "integrationAllowed": False,
    }

    if list_result.returncode != 0 or status["status"] not in {"COMPLETE", "COMPLETE_WITH_ERRORS"}:
        write_reports(report, args.json, args.md)
        return 0

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    tarball = OUTPUT_DIR / f"{project_id}.tar.gz"
    extract_dir = OUTPUT_DIR / project_id
    extract_dir.mkdir(parents=True, exist_ok=True)
    report["tarball"] = str(tarball)
    report["extractDir"] = str(extract_dir)

    result_cmd = [aristotle, "result", project_id, "--destination", str(tarball)]
    result = run(result_cmd, REPO_ROOT)
    commands.append(asdict(result))
    report["commands"] = commands
    if result.returncode != 0:
        write_reports(report, args.json, args.md)
        return 0

    safe_extract_tar(tarball, extract_dir)
    lean_files = sorted(extract_dir.rglob("*.lean"))
    report["leanFiles"] = [str(path) for path in lean_files]
    report["markerHits"] = scan_markers(lean_files)

    lean_checks: list[dict[str, Any]] = []
    for lean_file in lean_files:
        rel = lean_file.relative_to(Q3_ROOT)
        check = run(["lake", "env", "lean", str(rel)], Q3_ROOT)
        lean_checks.append({"file": str(lean_file), "result": asdict(check)})
    report["leanChecks"] = lean_checks

    report["integrationAllowed"] = (
        status["status"] == "COMPLETE"
        and not report["markerHits"]
        and bool(lean_files)
        and all(item["result"]["returncode"] == 0 for item in lean_checks)
    )
    write_reports(report, args.json, args.md)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
