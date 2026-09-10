#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import shutil
import sys
import tempfile
import time
from collections import Counter
from datetime import datetime
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
Q3_ROOT = REPO_ROOT / "q3.lean.aristotle"
CACHE_ROOT = Q3_ROOT / ".qmd_cache"
STABLE_STAGE_ROOT = CACHE_ROOT / "q3_docs_current"
COLLECTION = "q3_docs"
QMD_EMBED_TIMEOUT_S = 2400.0
QMD_EMBED_RETRIES = 5
# ECMAScript String.trim(): match Bun's empty-document check, including BOM.
QMD_TRIM_CHARACTERS = (
    " \t\n\r\v\f\u00a0\u1680\u2000\u2001\u2002\u2003\u2004\u2005"
    "\u2006\u2007\u2008\u2009\u200a\u2028\u2029\u202f\u205f\u3000\ufeff"
)
ROOT_SCRIPTS = REPO_ROOT / "scripts"
if str(ROOT_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(ROOT_SCRIPTS))

from q3_docs_corpus import (  # noqa: E402
    MAX_SEMANTIC_LEAN_BYTES,
    collect_sources,
    qmd_index_probe,
)
from qmd_ops import cleanup_stale_stage_dirs, qmd_lock, run_qmd  # noqa: E402


def resolve_qmd() -> str:
    found = shutil.which("qmd")
    if found:
        return found
    bun_qmd = Path.home() / ".bun" / "bin" / "qmd"
    if bun_qmd.exists():
        return str(bun_qmd)
    raise SystemExit("qmd not found on PATH and ~/.bun/bin/qmd is missing")


def stage_root_for_run() -> Path:
    stamp = datetime.now().astimezone().strftime("%Y%m%d_%H%M%S_%f")
    return CACHE_ROOT / f"q3_docs_stage_{stamp}_{os.getpid()}"


def build_stage(stage_root: Path, files: list[Path]) -> Counter:
    if stage_root.exists():
        shutil.rmtree(stage_root)
    stage_root.mkdir(parents=True, exist_ok=True)

    counts: Counter[str] = Counter()
    for src in files:
        rel = src.relative_to(REPO_ROOT)
        dst = stage_root / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
        # QMD skips empty files before deactivating their old indexed body.
        # Preserve raw bytes, including legacy invalid UTF-8, just as Bun does.
        if not dst.read_bytes().decode("utf-8", errors="replace").strip(QMD_TRIM_CHARACTERS):
            raise SystemExit(f"Q3_DOCS_EMPTY_SOURCE: {rel}")
        counts[src.suffix or "<none>"] += 1

    manifest = stage_root / "_manifest.md"
    lines = [
        "# q3_docs manifest",
        "",
        f"Collection: `{COLLECTION}`",
        f"Repo root: `{REPO_ROOT}`",
        f"Stage root: `{STABLE_STAGE_ROOT}`",
        "",
        "Curated scope:",
        "",
        "- current control and workflow docs,",
        "- current Route B bus and canonical active request markdown,",
        "- active manuscript TeX,",
        "- live Q3 Lean files excluding `Archive`, `Clean`, and heavy `PrimeCert` shards,",
        f"- compact Lean sources up to {MAX_SEMANTIC_LEAN_BYTES} bytes; larger generated "
        "payloads stay in exact `rg` search,",
        "- only reviewed notes marked `safe for embeddings: yes` are promoted from "
        "`docs/reviewed_notes/`,",
        "- raw inbox notes, extracted zip payloads, and archived sources under "
        "`docs/incoming_notes/` are excluded until distilled,",
        "- no transcript dumps or old queue artifacts.",
        "",
        f"Total files: `{len(files)}`",
        f"Markdown: `{counts['.md']}`",
        f"TeX: `{counts['.tex']}`",
        f"Lean: `{counts['.lean']}`",
        "",
    ]
    manifest.write_text("\n".join(lines), encoding="utf-8")
    return counts


def run(
    cmd: list[str],
    cwd: Path | None = None,
    *,
    timeout_s: float = 90.0,
    retries: int = 4,
) -> str:
    started = time.monotonic()
    try:
        return run_qmd(cmd, cwd=cwd, timeout_s=timeout_s, retries=retries)
    except RuntimeError as exc:
        raise SystemExit(str(exc)) from exc
    finally:
        print(f"Q3_DOCS_COMMAND seconds={time.monotonic() - started:.3f} argv={cmd}", flush=True)


def update_collection(qmd: str, stage_root: Path, embed: bool) -> None:
    """Called under the same qmd lock as stage promotion."""
    listing = run([qmd, "collection", "list"])
    existing = f"{COLLECTION} (qmd://{COLLECTION}/)" in listing
    live = qmd_index_probe(collection=COLLECTION) if existing else None
    if (
        live is not None
        and live["collection_root"] == str(stage_root.resolve())
        and live["collection_mask"] == "**/*"
    ):
        # This QMD version has no collection-scoped `update`. Its supported
        # config override scopes enumeration without editing the user's YAML
        # or running other collections' update hooks. Keep the live DB pinned.
        with tempfile.TemporaryDirectory(prefix="q3-qmd-update-") as config_dir:
            config = {"collections": {COLLECTION: {"path": str(stage_root), "pattern": "**/*"}}}
            (Path(config_dir) / "index.yml").write_text(json.dumps(config), encoding="utf-8")
            print(run([
                "env", f"QMD_CONFIG_DIR={config_dir}", f"INDEX_PATH={live['index_path']}",
                qmd, "update",
            ]).strip())
    else:
        if existing:
            run([qmd, "collection", "remove", COLLECTION])
        print(run([
            qmd, "collection", "add", str(stage_root), "--name", COLLECTION, "--mask", "**/*",
        ]).strip())
    if embed:
        print(run(
            [qmd, "embed"],
            timeout_s=QMD_EMBED_TIMEOUT_S,
            retries=QMD_EMBED_RETRIES,
        ).strip())


def promote_stage(pending: Path) -> Path:
    if STABLE_STAGE_ROOT.exists():
        shutil.rmtree(STABLE_STAGE_ROOT)
    os.replace(pending, STABLE_STAGE_ROOT)
    return STABLE_STAGE_ROOT


def main() -> int:
    ap = argparse.ArgumentParser(description="Incrementally refresh curated q3_docs qmd collection")
    ap.add_argument("--no-embed", action="store_true", help="update collection without qmd embed")
    ap.add_argument("--print-files", action="store_true", help="print included files")
    args = ap.parse_args()

    qmd = resolve_qmd()
    with qmd_lock("refresh_q3_docs"):
        files = collect_sources()
        CACHE_ROOT.mkdir(parents=True, exist_ok=True)
        cleanup_stale_stage_dirs(CACHE_ROOT)
        stage_root = stage_root_for_run()
        try:
            started = time.monotonic()
            counts = build_stage(stage_root, files)
            if args.print_files:
                for path in files:
                    print(path.relative_to(REPO_ROOT))
            print(
                f"Prepared {len(files) + 1} files for {COLLECTION}: "
                f"{len(files)} sources ({counts['.md']} md, {counts['.tex']} tex, "
                f"{counts['.lean']} lean) + 1 generated manifest; "
                f"stage_seconds={time.monotonic() - started:.3f}", flush=True,
            )
            stable_stage = promote_stage(stage_root)
            update_collection(qmd=qmd, stage_root=stable_stage, embed=not args.no_embed)
            print(run([qmd, "status"]).strip())
        finally:
            if stage_root.exists():
                shutil.rmtree(stage_root, ignore_errors=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
