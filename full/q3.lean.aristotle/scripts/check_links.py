#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path


LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
SCHEME_RE = re.compile(r"^[a-zA-Z][a-zA-Z0-9+.-]*:")


def strip_code_fences(text: str) -> str:
    in_code = False
    out_lines = []
    for line in text.splitlines():
        if line.strip().startswith("```"):
            in_code = not in_code
            continue
        if in_code:
            continue
        out_lines.append(line)
    return "\n".join(out_lines)


def iter_markdown_files(root: Path, exclude_dirs: set[str]):
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [
            d for d in dirnames if d not in exclude_dirs and not d.startswith(".")
        ]
        for name in filenames:
            if name.endswith(".md"):
                yield Path(dirpath) / name


def main() -> int:
    parser = argparse.ArgumentParser(description="Check markdown links in docs.")
    parser.add_argument(
        "--root",
        default=str(Path(__file__).resolve().parents[1]),
        help="Root directory to scan (defaults to project root).",
    )
    args = parser.parse_args()

    root = Path(args.root).resolve()
    exclude_dirs = {".git", ".lake", "node_modules"}
    missing: list[tuple[Path, str]] = []

    for path in iter_markdown_files(root, exclude_dirs):
        text = path.read_text(errors="ignore")
        clean = strip_code_fences(text)
        for match in LINK_RE.finditer(clean):
            raw = match.group(1).strip()
            if not raw or raw.startswith("#"):
                continue
            if SCHEME_RE.match(raw):
                continue
            start = match.start()
            if start > 0 and (clean[start - 1].isalnum() or clean[start - 1] == "_"):
                continue
            if " " in raw:
                raw = raw.split(" ", 1)[0]
            path_part = raw.split("#", 1)[0]
            if not path_part:
                continue
            if path_part.startswith("/"):
                target = Path(path_part)
            else:
                target = (path.parent / path_part).resolve()
            if not target.exists():
                missing.append((path, path_part))

    if missing:
        print("MISSING_LINKS")
        for file_path, link in sorted(missing):
            try:
                rel = file_path.relative_to(root)
            except ValueError:
                rel = file_path
            print(f"{rel}:{link}")
        return 1

    print("NO_MISSING_LINKS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
