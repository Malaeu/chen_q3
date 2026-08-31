#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from pathlib import Path, PurePosixPath

LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
SCHEME_RE = re.compile(r"^[a-zA-Z][a-zA-Z0-9+.-]*:")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class HistoricalPinError(ValueError):
    pass


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
        dirnames[:] = [d for d in dirnames if d not in exclude_dirs and not d.startswith(".")]
        for name in filenames:
            if name.endswith(".md"):
                yield Path(dirpath) / name


def historical_pins(repo_root: Path) -> dict[Path, str]:
    manifest_path = repo_root / "docs" / "semantic_quarantine" / "PORTABILITY_MANIFEST_v1.json"
    if not manifest_path.is_file():
        raise HistoricalPinError(f"missing manifest: {manifest_path}")
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise HistoricalPinError(f"unreadable manifest: {manifest_path}") from exc
    if not isinstance(manifest, dict):
        raise HistoricalPinError("manifest root must be an object")
    if manifest.get("schema_version") != "q3.portability_manifest.v1":
        raise HistoricalPinError("unexpected manifest schema_version")
    historical_hits = manifest.get("historical_hits")
    if not isinstance(historical_hits, list):
        raise HistoricalPinError("historical_hits must be a list")

    repo_lexical = repo_root.absolute()
    pins: dict[Path, str] = {}
    for entry in historical_hits:
        if not isinstance(entry, dict):
            raise HistoricalPinError("historical_hits entries must be objects")
        if entry.get("class") != "HISTORICAL_PINNED":
            continue
        path = entry.get("path")
        digest = entry.get("sha256")
        if not isinstance(path, str) or not path:
            raise HistoricalPinError("HISTORICAL_PINNED path must be a nonempty string")
        if not isinstance(digest, str) or SHA256_RE.fullmatch(digest) is None:
            raise HistoricalPinError(f"invalid SHA-256 for historical path: {path}")
        if "\\" in path:
            raise HistoricalPinError(f"historical path is not POSIX-relative: {path}")
        relative = PurePosixPath(path)
        if relative.is_absolute() or any(part in {".", ".."} for part in relative.parts):
            raise HistoricalPinError(f"historical path is not canonical: {path}")
        if relative.as_posix() != path:
            raise HistoricalPinError(f"historical path is not canonical: {path}")
        lexical_path = (repo_lexical / Path(*relative.parts)).absolute()
        if not lexical_path.is_relative_to(repo_lexical):
            raise HistoricalPinError(f"historical path escapes repository: {path}")
        if lexical_path in pins:
            raise HistoricalPinError(f"duplicate historical path: {path}")
        pins[lexical_path] = digest
    return pins


def main() -> int:
    parser = argparse.ArgumentParser(description="Check markdown links in docs.")
    parser.add_argument(
        "--root",
        default=str(Path(__file__).resolve().parents[1]),
        help="Root directory to scan (defaults to project root).",
    )
    args = parser.parse_args()

    root = Path(args.root).resolve()
    repo_root = root.parent
    sections_root = repo_root / "full" / "sections"
    try:
        pinned_history = historical_pins(repo_root)
    except HistoricalPinError as exc:
        print("HISTORICAL_PIN_MANIFEST_INVALID")
        print(exc)
        return 2
    # ACTIVE/ is a symlink hub; link targets are evaluated relative to their
    # original locations, not the hub. Exclude it from link checks.
    # Also exclude literature corpora (OCR/fulltext) to avoid false-positive links.
    exclude_dirs = {".git", ".lake", "node_modules", "ACTIVE", "literature", "zotero"}
    missing: list[tuple[Path, str]] = []

    for path in iter_markdown_files(root, exclude_dirs):
        expected_digest = pinned_history.get(path.absolute())
        if expected_digest is not None:
            actual_digest = hashlib.sha256(path.read_bytes()).hexdigest()
            if actual_digest == expected_digest:
                continue
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
                if not target.exists():
                    missing.append((path, path_part))
                continue

            target = (path.parent / path_part).resolve()
            if target.exists():
                continue

            # Fallbacks for repo-root paths (e.g. full/sections, paper/sections).
            alt_targets = []
            alt_targets.append((repo_root / path_part).resolve())

            normalized = path_part
            while normalized.startswith("../"):
                normalized = normalized[3:]
            if normalized.startswith("sections/"):
                alt_targets.append((repo_root / "full" / normalized).resolve())

            if not any(t.exists() for t in alt_targets):
                if normalized.startswith("sections/") and not sections_root.exists():
                    continue
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
