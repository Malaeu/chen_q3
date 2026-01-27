#!/usr/bin/env python3
import argparse
import hashlib
import json
import sqlite3
from datetime import datetime, timezone
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]
Q3_ROOT = PROJECT_ROOT / "full" / "q3.lean.aristotle"
DEFAULT_OUT_DIR = Q3_ROOT / "literature" / "zotero"
DEFAULT_PAPER_INDEX = Q3_ROOT / "ACTIVE" / "PAPER_INDEX.json"


def now_utc() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")


def yaml_quote(value: str | None) -> str:
    if value is None:
        return "null"
    return json.dumps(value)


def open_db(db_path: Path) -> sqlite3.Connection:
    uri = f"file:{db_path}?mode=ro&immutable=1"
    return sqlite3.connect(uri, uri=True)


def fetch_item_id(cursor: sqlite3.Cursor, key: str) -> int | None:
    cursor.execute("select itemID from items where key=?", (key,))
    row = cursor.fetchone()
    return row[0] if row else None


def fetch_parent_item_id(cursor: sqlite3.Cursor, attachment_item_id: int) -> int | None:
    cursor.execute("select parentItemID from itemAttachments where itemID=?", (attachment_item_id,))
    row = cursor.fetchone()
    return row[0] if row else None


def fetch_item_key(cursor: sqlite3.Cursor, item_id: int) -> str | None:
    cursor.execute("select key from items where itemID=?", (item_id,))
    row = cursor.fetchone()
    return row[0] if row else None


def fetch_fields(cursor: sqlite3.Cursor, item_id: int) -> dict:
    cursor.execute("select fieldID, fieldName from fields")
    field_map = {field_id: name for field_id, name in cursor.fetchall()}
    cursor.execute("select fieldID, valueID from itemData where itemID=?", (item_id,))
    fields = {}
    for field_id, value_id in cursor.fetchall():
        cursor.execute("select value from itemDataValues where valueID=?", (value_id,))
        value_row = cursor.fetchone()
        if value_row:
            fields[field_map.get(field_id, str(field_id))] = value_row[0]
    return fields


def fetch_creators(cursor: sqlite3.Cursor, item_id: int) -> list[dict]:
    cursor.execute(
        """
        select c.firstName, c.lastName, c.fieldMode, ct.creatorType
        from itemCreators ic
        join creators c on c.creatorID = ic.creatorID
        join creatorTypes ct on ct.creatorTypeID = ic.creatorTypeID
        where ic.itemID=?
        order by ic.orderIndex
        """,
        (item_id,),
    )
    creators = []
    for first_name, last_name, field_mode, creator_type in cursor.fetchall():
        if field_mode == 1:
            full_name = last_name or first_name or ""
        else:
            full_name = " ".join(part for part in [first_name, last_name] if part)
        creators.append({"type": creator_type, "name": full_name})
    return creators


def load_fulltext(cache_path: Path) -> str:
    return cache_path.read_text(encoding="utf-8", errors="ignore").strip()


def compute_sha256(text: str) -> str:
    digest = hashlib.sha256()
    digest.update(text.encode("utf-8"))
    return digest.hexdigest()


def write_markdown(out_path: Path, meta: dict, fulltext: str) -> None:
    lines = ["---"]
    lines.append(f"title: {yaml_quote(meta.get('title'))}")
    authors = meta.get("authors") or []
    if authors:
        lines.append("authors:")
        for author in authors:
            lines.append(f"  - {yaml_quote(author)}")
    lines.append(f"date: {yaml_quote(meta.get('date'))}")
    lines.append(f"publication: {yaml_quote(meta.get('publication'))}")
    lines.append(f"doi: {yaml_quote(meta.get('doi'))}")
    lines.append(f"url: {yaml_quote(meta.get('url'))}")
    lines.append("zotero:")
    lines.append(f"  attachment_key: {yaml_quote(meta.get('attachment_key'))}")
    lines.append(f"  parent_key: {yaml_quote(meta.get('parent_key'))}")
    lines.append(f"  item_id: {meta.get('item_id')}")
    lines.append(f"  attachment_item_id: {meta.get('attachment_item_id')}")
    lines.append("---")
    lines.append("")
    lines.append(fulltext)
    out_path.write_text("\n".join(lines), encoding="utf-8")


def update_paper_index(
    paper_index_path: Path,
    entries: list[dict],
    overwrite: bool,
) -> None:
    if paper_index_path.exists():
        data = json.loads(paper_index_path.read_text(encoding="utf-8"))
    else:
        data = {"schema_version": "1.0", "generated_at": now_utc(), "sources": []}

    existing = {source.get("id") for source in data.get("sources", [])}
    new_sources = []
    for entry in entries:
        entry_id = entry.get("id")
        if entry_id in existing and not overwrite:
            continue
        if entry_id in existing and overwrite:
            data["sources"] = [s for s in data.get("sources", []) if s.get("id") != entry_id]
        new_sources.append(entry)

    if new_sources:
        data["sources"] = data.get("sources", []) + new_sources
        data["generated_at"] = now_utc()
        paper_index_path.write_text(json.dumps(data, indent=2), encoding="utf-8")


def process_storage_dir(
    cursor: sqlite3.Cursor,
    storage_dir: Path,
    out_dir: Path,
    overwrite: bool,
) -> dict | None:
    attachment_key = storage_dir.name
    cache_path = storage_dir / ".zotero-ft-cache"
    if not cache_path.exists():
        return None

    attachment_item_id = fetch_item_id(cursor, attachment_key)
    if attachment_item_id is None:
        return None

    parent_item_id = fetch_parent_item_id(cursor, attachment_item_id)
    target_item_id = parent_item_id or attachment_item_id
    parent_key = fetch_item_key(cursor, target_item_id) or attachment_key

    fields = fetch_fields(cursor, target_item_id)
    creators = fetch_creators(cursor, target_item_id)
    authors = [c["name"] for c in creators if c["type"] == "author" and c["name"]]

    title = fields.get("title") or f"Zotero {parent_key}"
    date = fields.get("date")
    publication = fields.get("publicationTitle")
    doi = fields.get("DOI")
    url = fields.get("url")

    fulltext = load_fulltext(cache_path)
    if not fulltext:
        return None

    target_dir = out_dir / parent_key
    target_dir.mkdir(parents=True, exist_ok=True)
    output_path = target_dir / "fulltext.md"
    if output_path.exists() and not overwrite:
        return None

    meta = {
        "title": title,
        "authors": authors,
        "date": date,
        "publication": publication,
        "doi": doi,
        "url": url,
        "attachment_key": attachment_key,
        "parent_key": parent_key,
        "item_id": target_item_id,
        "attachment_item_id": attachment_item_id,
    }

    write_markdown(output_path, meta, fulltext)

    entry = {
        "id": f"ZOTERO_{parent_key}",
        "title": title,
        "author": ", ".join(authors) if authors else None,
        "year": date[:4] if date else None,
        "source_url": url or (f"https://doi.org/{doi}" if doi else None),
        "sha256": compute_sha256(fulltext),
        "local_path": str(output_path.relative_to(Q3_ROOT)),
        "notes": f"Zotero attachment {attachment_key} (parent {parent_key})",
    }
    return entry


def main() -> int:
    parser = argparse.ArgumentParser(description="Convert Zotero full-text cache to markdown.")
    parser.add_argument("--db", default="~/Zotero/zotero.sqlite", help="path to zotero.sqlite")
    parser.add_argument("--storage", default="~/Zotero/storage", help="Zotero storage dir")
    parser.add_argument("--out", default=str(DEFAULT_OUT_DIR), help="output markdown directory")
    parser.add_argument(
        "--paper-index", default=str(DEFAULT_PAPER_INDEX), help="PAPER_INDEX.json path"
    )
    parser.add_argument("--limit", type=int, default=None, help="limit number of items")
    parser.add_argument("--only-key", help="process only a specific storage key")
    parser.add_argument("--overwrite", action="store_true", help="overwrite existing markdown")
    parser.add_argument("--write-index", action="store_true", help="update PAPER_INDEX.json")
    parser.add_argument("--dry-run", action="store_true", help="list items without writing")
    args = parser.parse_args()

    storage_dir = Path(args.storage).expanduser()
    db_path = Path(args.db).expanduser()
    out_dir = Path(args.out)
    paper_index_path = Path(args.paper_index)

    if not db_path.exists():
        raise SystemExit(f"Missing zotero DB: {db_path}")
    if not storage_dir.exists():
        raise SystemExit(f"Missing storage dir: {storage_dir}")

    out_dir.mkdir(parents=True, exist_ok=True)

    conn = open_db(db_path)
    cursor = conn.cursor()

    storage_dirs = [p for p in storage_dir.iterdir() if p.is_dir()]
    if args.only_key:
        storage_dirs = [p for p in storage_dirs if p.name == args.only_key]

    entries = []
    processed = 0
    for storage_path in sorted(storage_dirs):
        if args.limit is not None and processed >= args.limit:
            break
        cache_path = storage_path / ".zotero-ft-cache"
        if not cache_path.exists():
            continue

        if args.dry_run:
            print(storage_path.name)
            processed += 1
            continue

        entry = process_storage_dir(cursor, storage_path, out_dir, args.overwrite)
        if entry:
            entries.append(entry)
            processed += 1

    conn.close()

    if args.write_index and entries:
        update_paper_index(paper_index_path, entries, args.overwrite)

    print(f"Processed {processed} items. Wrote {len(entries)} markdown files.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
