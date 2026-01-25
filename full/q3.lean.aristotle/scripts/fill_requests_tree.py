#!/usr/bin/env python3
"""Fill TODO sections in ACTIVE/requests node.md files with safe placeholders.

Only replaces sections that contain a single "- TODO" line.
"""
from __future__ import annotations
import re
from pathlib import Path

ROOT = Path("/Users/emalam/Documents/GitHub/chen_q3/sandboxes/projekt_2/full/q3.lean.aristotle")
REQUESTS_DIR = ROOT / "ACTIVE" / "requests"

REQUEST_RE = re.compile(r"^- request: `(?P<path>[^`]+)`", re.M)


def get_request_path(node_path: Path) -> Path | None:
    text = node_path.read_text(encoding="utf-8")
    m = REQUEST_RE.search(text)
    if not m:
        return None
    req_rel = m.group("path")
    return (node_path.parent / req_rel).resolve()


def section_has_todo(section_text: str) -> bool:
    return section_text.strip() == "- TODO"


def replace_section(text: str, header: str, new_lines: list[str]) -> str:
    pattern = re.compile(rf"({re.escape(header)}\n)(.*?)(\n## |\Z)", re.S)
    m = pattern.search(text)
    if not m:
        return text
    body = m.group(2).rstrip()
    if not section_has_todo(body):
        return text
    replacement = m.group(1) + "\n".join(new_lines) + "\n" + ("\n## " if m.group(3).startswith("\n## ") else "")
    return text[:m.start()] + replacement + text[m.end():]


def fill_node(node_path: Path) -> bool:
    text = node_path.read_text(encoding="utf-8")
    req_path = get_request_path(node_path)
    req_exists = req_path.exists() if req_path else False
    req_name = req_path.name if req_path else "(missing)"

    why_lines = [
        f"- Request artifact `{req_name}` captured a concrete task in this topic.",
        "- This node exists to record why it was asked, what evidence we have, and the decision taken.",
    ]

    if req_exists:
        evidence_lines = [
            f"- Source request file exists: `{req_path}`.",
            "- Related outputs (if any) are linked above; validate for correctness before reuse.",
        ]
    else:
        evidence_lines = [
            "- Source request file is missing; confirm the request path above is still valid.",
            "- Related outputs (if any) are linked above; validate for correctness before reuse.",
        ]

    decision_lines = [
        "- Pending triage: open the request and any linked outputs.",
        "- Extract concrete sub-lemmas or actions; set status to keep/retire after review.",
    ]

    new_text = text
    new_text = replace_section(new_text, "## Why we are here", why_lines)
    new_text = replace_section(new_text, "## Evidence / checks", evidence_lines)
    new_text = replace_section(new_text, "## Decision", decision_lines)

    if new_text != text:
        node_path.write_text(new_text, encoding="utf-8")
        return True
    return False


def main() -> None:
    if not REQUESTS_DIR.exists():
        raise SystemExit(f"Missing requests dir: {REQUESTS_DIR}")
    updated = 0
    for node in REQUESTS_DIR.rglob("node.md"):
        if fill_node(node):
            updated += 1
    print(f"Filled {updated} nodes")


if __name__ == "__main__":
    main()
