#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import shutil
import textwrap
import zipfile
from datetime import datetime
from pathlib import Path, PurePosixPath


REPO_ROOT = Path(__file__).resolve().parents[2]
Q3_ROOT = REPO_ROOT / "q3.lean.aristotle"
INCOMING_ROOT = Q3_ROOT / "docs" / "incoming_notes"
EXTRACTED_ROOT = INCOMING_ROOT / "extracted"
ARCHIVE_ROOT = INCOMING_ROOT / "archive"
REVIEWED_ROOT = Q3_ROOT / "docs" / "reviewed_notes"
TEXT_EXTENSIONS = {".md", ".markdown", ".txt"}
REQUIRED_REVIEW_MARKERS = (
    "- review status: `reviewed`",
    "- safe for embeddings: `yes`",
)


def slugify(text: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9]+", "_", text).strip("_").lower()
    return cleaned or "note"


def timestamp() -> str:
    return datetime.now().astimezone().strftime("%Y%m%d_%H%M%S")


def repo_rel(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT)).replace("\\", "/")


def resolve_input(path_str: str) -> Path:
    raw = Path(path_str)
    if not raw.is_absolute():
        candidate = (Path.cwd() / raw).resolve()
        if candidate.exists():
            raw = candidate
        else:
            raw = (INCOMING_ROOT / raw).resolve()
    else:
        raw = raw.resolve()
    if not raw.exists():
        raise SystemExit(f"Input not found: {path_str}")
    if INCOMING_ROOT.resolve() not in raw.parents and raw != INCOMING_ROOT.resolve():
        raise SystemExit(f"Input must live under {INCOMING_ROOT}")
    return raw


def safe_members(zf: zipfile.ZipFile) -> list[zipfile.ZipInfo]:
    keep: list[zipfile.ZipInfo] = []
    for info in zf.infolist():
        if info.is_dir():
            continue
        pure = PurePosixPath(info.filename)
        if pure.is_absolute() or ".." in pure.parts:
            continue
        if pure.suffix.lower() in TEXT_EXTENSIONS:
            keep.append(info)
    return keep


def reviewed_stub_name(source: Path) -> str:
    today = datetime.now().astimezone().strftime("%Y_%m_%d")
    stem_slug = slugify(source.stem)
    if stem_slug.startswith(f"{today}_"):
        stem_slug = stem_slug[len(today) + 1 :]
    if not stem_slug:
        stem_slug = "note"
    return f"{today}_{stem_slug}_review.md"


def make_review_stub(source: Path, extracted_files: list[Path]) -> Path:
    REVIEWED_ROOT.mkdir(parents=True, exist_ok=True)
    stub = REVIEWED_ROOT / reviewed_stub_name(source)
    if stub.exists():
        return stub

    lines = [
        "# Reviewed Note",
        "",
        "## Source",
        "",
        f"- raw file: `{repo_rel(source)}`",
        f"- date: `{datetime.now().astimezone().isoformat(timespec='seconds')}`",
        "- author / tool: `incoming_notes ingestion`",
        "",
        "## Status",
        "",
        "- review status: `draft`",
        "- scope: `math`",
        "- safe for embeddings: `no`",
        "",
        "## Extracted files",
        "",
    ]
    if extracted_files:
        lines.extend(f"- `{repo_rel(path)}`" for path in extracted_files)
    else:
        lines.append("- none")
    lines.extend(
        [
            "",
            "## Core claim",
            "",
            "_Fill after review._",
            "",
            "## Checked against repo",
            "",
            "- Lean files:",
            "- TeX files:",
            "- control docs:",
            "",
            "## What survived review",
            "",
            "-",
            "",
            "## What was rejected or weakened",
            "",
            "-",
            "",
            "## Reusable theorem / lemma pointers",
            "",
            "-",
            "",
            "## Next action",
            "",
            "- promote to `docs/INSIGHTS.md`",
            "- refresh `q3_docs` after this note becomes `safe for embeddings: yes`",
            "",
        ]
    )
    stub.write_text("\n".join(lines), encoding="utf-8")
    return stub


def reviewed_note_is_ready(reviewed: Path) -> bool:
    text = reviewed.read_text(encoding="utf-8")
    return all(marker in text for marker in REQUIRED_REVIEW_MARKERS)


def write_manifest(source: Path, extract_dir: Path, extracted_files: list[Path], review_stub: Path) -> None:
    manifest = extract_dir / "_manifest.md"
    lines = [
        "# Incoming note extraction manifest",
        "",
        f"- source: `{repo_rel(source)}`",
        f"- extracted at: `{datetime.now().astimezone().isoformat(timespec='seconds')}`",
        f"- review stub: `{repo_rel(review_stub)}`",
        "",
        "## Extracted files",
        "",
    ]
    if extracted_files:
        lines.extend(f"- `{repo_rel(path)}`" for path in extracted_files)
    else:
        lines.append("- none")
    manifest.write_text("\n".join(lines), encoding="utf-8")


def prepare(source: Path, force: bool) -> int:
    EXTRACTED_ROOT.mkdir(parents=True, exist_ok=True)
    ARCHIVE_ROOT.mkdir(parents=True, exist_ok=True)
    extracted_files: list[Path] = []

    if source.suffix.lower() == ".zip":
        extract_dir = EXTRACTED_ROOT / slugify(source.stem)
        if extract_dir.exists():
            if not force:
                raise SystemExit(
                    f"Extraction target already exists: {repo_rel(extract_dir)} (use --force to replace)"
                )
            shutil.rmtree(extract_dir)
        extract_dir.mkdir(parents=True, exist_ok=True)
        with zipfile.ZipFile(source) as zf:
            members = safe_members(zf)
            if not members:
                shutil.rmtree(extract_dir)
                raise SystemExit(f"No markdown-like files found in zip: {repo_rel(source)}")
            for info in members:
                pure = PurePosixPath(info.filename)
                target = extract_dir / Path(*pure.parts)
                target.parent.mkdir(parents=True, exist_ok=True)
                with zf.open(info) as src, target.open("wb") as dst:
                    shutil.copyfileobj(src, dst)
                extracted_files.append(target)
        extracted_files.sort()
    elif source.suffix.lower() in TEXT_EXTENSIONS:
        extracted_files = [source]
        extract_dir = EXTRACTED_ROOT / slugify(source.stem)
        extract_dir.mkdir(parents=True, exist_ok=True)
    else:
        raise SystemExit("Supported inputs: .zip, .md, .markdown, .txt")

    review_stub = make_review_stub(source, extracted_files)
    write_manifest(source, extract_dir, extracted_files, review_stub)

    print(f"Source:       {repo_rel(source)}")
    if source.suffix.lower() == ".zip":
        print(f"Extracted to: {repo_rel(extract_dir)}")
    print(f"Review stub:  {repo_rel(review_stub)}")
    print("Files:")
    for path in extracted_files:
        print(f"  - {repo_rel(path)}")
    return 0


def archive(source: Path, reviewed: Path) -> int:
    if not reviewed.exists():
        raise SystemExit(f"Reviewed note not found: {reviewed}")
    if REVIEWED_ROOT.resolve() not in reviewed.resolve().parents:
        raise SystemExit(f"Reviewed note must live under {REVIEWED_ROOT}")
    if not reviewed_note_is_ready(reviewed):
        raise SystemExit(
            "Reviewed note is not ready for archive. "
            "Set `review status: reviewed` and `safe for embeddings: yes` first."
        )

    stamp = f"{timestamp()}_{slugify(source.stem)}"
    target_root = ARCHIVE_ROOT / stamp
    raw_dir = target_root / "raw"
    extracted_dir = target_root / "extracted"
    raw_dir.mkdir(parents=True, exist_ok=False)
    extracted_dir.mkdir(parents=True, exist_ok=False)

    raw_target = raw_dir / source.name
    shutil.move(str(source), str(raw_target))

    candidate_extracted = EXTRACTED_ROOT / slugify(source.stem)
    moved_extracted = False
    if candidate_extracted.exists():
        shutil.move(str(candidate_extracted), str(extracted_dir / candidate_extracted.name))
        moved_extracted = True

    manifest = target_root / "_archive.md"
    manifest.write_text(
        textwrap.dedent(
            f"""\
            # Incoming note archive

            - archived at: `{datetime.now().astimezone().isoformat(timespec='seconds')}`
            - reviewed note: `{repo_rel(reviewed)}`
            - raw source moved from: `{repo_rel(source)}`
            - raw source archived at: `{repo_rel(raw_target)}`
            - extracted folder archived: `{moved_extracted}`
            """
        ),
        encoding="utf-8",
    )

    print(f"Archived raw source to: {repo_rel(raw_target)}")
    if moved_extracted:
        print(f"Archived extracted folder under: {repo_rel(extracted_dir)}")
    print(f"Reviewed note kept at: {repo_rel(reviewed)}")
    return 0


def status() -> int:
    print("Incoming notes:")
    for path in sorted(INCOMING_ROOT.iterdir()):
        if path.name in {"README.md", "archive", "extracted"}:
            continue
        print(f"  - {repo_rel(path)}")
    print("")
    print("Archive root:")
    print(f"  - {repo_rel(ARCHIVE_ROOT)}")
    print("Extracted root:")
    print(f"  - {repo_rel(EXTRACTED_ROOT)}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description="Prepare and archive incoming markdown notes")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_prepare = sub.add_parser("prepare", help="Extract a raw zip/markdown note and create a reviewed stub")
    p_prepare.add_argument("input", help="Path to raw zip/markdown under docs/incoming_notes/")
    p_prepare.add_argument("--force", action="store_true", help="Replace existing extracted folder")

    p_archive = sub.add_parser("archive", help="Archive a processed raw note after review")
    p_archive.add_argument("input", help="Raw source path under docs/incoming_notes/")
    p_archive.add_argument(
        "--reviewed",
        required=True,
        help="Path to the reviewed markdown note under docs/reviewed_notes/",
    )

    sub.add_parser("status", help="Show inbox/archive locations")

    args = ap.parse_args()
    if args.cmd == "prepare":
        return prepare(resolve_input(args.input), force=args.force)
    if args.cmd == "archive":
        reviewed = Path(args.reviewed)
        if not reviewed.is_absolute():
            reviewed = (Q3_ROOT / reviewed).resolve()
        return archive(resolve_input(args.input), reviewed)
    return status()


if __name__ == "__main__":
    raise SystemExit(main())
