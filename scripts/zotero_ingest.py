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
DEFAULT_MISSING_REPORT = Q3_ROOT / "ACTIVE" / "ZOTERO_MISSING_CACHE.md"


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


def fetch_collections(cursor: sqlite3.Cursor) -> list[dict]:
    cursor.execute("select collectionID, collectionName, parentCollectionID, key from collections")
    collections = []
    for collection_id, name, parent_id, key in cursor.fetchall():
        collections.append(
            {
                "collection_id": collection_id,
                "name": name,
                "parent_id": parent_id,
                "key": key,
            }
        )
    return collections


def resolve_collection_ids(
    cursor: sqlite3.Cursor,
    collection_name: str | None,
    collection_key: str | None,
    include_children: bool,
) -> list[int]:
    collections = fetch_collections(cursor)
    children_map: dict[int, list[int]] = {}
    for c in collections:
        parent_id = c["parent_id"]
        if parent_id is not None:
            children_map.setdefault(parent_id, []).append(c["collection_id"])

    def add_descendants(seed_ids: list[int]) -> list[int]:
        seen = set(seed_ids)
        queue = list(seed_ids)
        while queue:
            cid = queue.pop(0)
            for child_id in children_map.get(cid, []):
                if child_id not in seen:
                    seen.add(child_id)
                    queue.append(child_id)
        return sorted(seen)

    base_ids: list[int] = []
    if collection_key:
        for c in collections:
            if c["key"] == collection_key:
                base_ids.append(c["collection_id"])
    elif collection_name:
        for c in collections:
            if c["name"] == collection_name:
                base_ids.append(c["collection_id"])

    if not base_ids:
        return []

    if include_children:
        return add_descendants(base_ids)
    return sorted(set(base_ids))


def list_collections(cursor: sqlite3.Cursor) -> None:
    collections = fetch_collections(cursor)
    by_id = {c["collection_id"]: c for c in collections}
    for c in sorted(collections, key=lambda x: (x["name"] or "", x["collection_id"])):
        parent = by_id.get(c["parent_id"])
        parent_name = parent["name"] if parent else None
        print(f"{c['name']}  (key={c['key']}, parent={parent_name})")


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


def build_missing_entries(
    cursor: sqlite3.Cursor,
    attachment_keys: list[str],
    storage_dir: Path,
) -> list[dict]:
    missing = []
    for key in attachment_keys:
        cache_path = storage_dir / key / ".zotero-ft-cache"
        if cache_path.exists():
            continue
        attachment_item_id = fetch_item_id(cursor, key)
        parent_item_id = (
            fetch_parent_item_id(cursor, attachment_item_id) if attachment_item_id else None
        )
        target_item_id = parent_item_id or attachment_item_id
        parent_key = fetch_item_key(cursor, target_item_id) if target_item_id else None
        fields = fetch_fields(cursor, target_item_id) if target_item_id else {}
        creators = fetch_creators(cursor, target_item_id) if target_item_id else []
        authors = [c["name"] for c in creators if c["type"] == "author" and c["name"]]
        missing.append(
            {
                "attachment_key": key,
                "parent_key": parent_key,
                "title": fields.get("title"),
                "authors": authors,
                "date": fields.get("date"),
                "doi": fields.get("DOI"),
            }
        )
    return missing


def write_missing_report(path: Path, missing: list[dict], collection_label: str | None) -> None:
    lines = ["# Zotero Missing Full‑Text Cache", ""]
    if collection_label:
        lines.append(f"**Collection:** {collection_label}")
        lines.append("")
    lines.append(f"**Generated:** {now_utc()}")
    lines.append("")
    lines.append(f"**Missing items:** {len(missing)}")
    lines.append("")
    lines.append("| attachment_key | parent_key | title | authors | date | doi |")
    lines.append("|---|---|---|---|---|---|")
    for item in missing:
        lines.append(
            "| {attachment_key} | {parent_key} | {title} | {authors} | {date} | {doi} |".format(
                attachment_key=item.get("attachment_key") or "",
                parent_key=item.get("parent_key") or "",
                title=(item.get("title") or "").replace("|", "\\|"),
                authors=", ".join(item.get("authors") or []),
                date=item.get("date") or "",
                doi=item.get("doi") or "",
            )
        )
    path.write_text("\n".join(lines), encoding="utf-8")


def fetch_attachment_keys_for_collections(
    cursor: sqlite3.Cursor,
    collection_ids: list[int],
) -> list[str]:
    if not collection_ids:
        return []
    placeholders = ",".join("?" for _ in collection_ids)
    query = f"""
        select a.key
        from collectionItems ci
        join items p on p.itemID = ci.itemID
        join itemAttachments ia on ia.parentItemID = p.itemID
        join items a on a.itemID = ia.itemID
        where ci.collectionID in ({placeholders})
          and ia.contentType = 'application/pdf'
    """
    cursor.execute(query, collection_ids)
    keys = [row[0] for row in cursor.fetchall() if row and row[0]]
    return sorted(set(keys))


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
    parser.add_argument(
        "--collection-name", help="only ingest attachments in this Zotero collection"
    )
    parser.add_argument(
        "--collection-key", help="only ingest attachments in this Zotero collection key"
    )
    parser.add_argument(
        "--include-children",
        action="store_true",
        help="include subcollections under the target collection",
    )
    parser.add_argument(
        "--list-collections", action="store_true", help="list Zotero collections and exit"
    )
    parser.add_argument(
        "--report-missing", action="store_true", help="report attachments missing full-text cache"
    )
    parser.add_argument(
        "--report-path", default=str(DEFAULT_MISSING_REPORT), help="output report path"
    )
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

    if args.list_collections:
        list_collections(cursor)
        conn.close()
        return 0

    collection_ids: list[int] = []
    if args.collection_name or args.collection_key:
        collection_ids = resolve_collection_ids(
            cursor,
            args.collection_name,
            args.collection_key,
            args.include_children,
        )
        if not collection_ids:
            conn.close()
            raise SystemExit("Collection not found. Use --list-collections to inspect names/keys.")

    storage_dirs = [p for p in storage_dir.iterdir() if p.is_dir()]
    if args.only_key:
        storage_dirs = [p for p in storage_dirs if p.name == args.only_key]
    attachment_keys: list[str] = []
    if collection_ids:
        keys = fetch_attachment_keys_for_collections(cursor, collection_ids)
        attachment_keys = keys
        storage_dirs = [storage_dir / key for key in keys if (storage_dir / key).is_dir()]
    else:
        attachment_keys = [p.name for p in storage_dirs]

    if args.report_missing:
        collection_label = args.collection_name or args.collection_key
        missing = build_missing_entries(cursor, attachment_keys, storage_dir)
        report_path = Path(args.report_path)
        write_missing_report(report_path, missing, collection_label)
        print(f"Missing cache report: {report_path}")
        for item in missing:
            print(item.get("attachment_key"))

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
