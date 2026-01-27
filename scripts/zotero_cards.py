#!/usr/bin/env python3
import argparse
import json
import os
import re
import textwrap
import urllib.parse
import urllib.request
from pathlib import Path

DEFAULT_API_URL = "http://localhost:23119/api/users/0"
DEFAULT_STORAGE = "~/Zotero/storage"


def api_request(
    method: str, base_url: str, path: str, params: dict | None, payload, api_key: str | None
):
    url = base_url.rstrip("/") + "/" + path.lstrip("/")
    if params:
        url += "?" + urllib.parse.urlencode(params)
    data = None
    headers = {}
    if payload is not None:
        data = json.dumps(payload).encode("utf-8")
        headers["Content-Type"] = "application/json"
    if api_key:
        headers["Zotero-API-Key"] = api_key
    req = urllib.request.Request(url, data=data, method=method, headers=headers)
    with urllib.request.urlopen(req, timeout=30) as resp:
        body = resp.read().decode("utf-8")
    if not body:
        return None
    return json.loads(body)


def api_paged(base_url: str, path: str, params: dict | None, api_key: str | None, limit: int = 100):
    all_items = []
    start = 0
    params = params.copy() if params else {}
    while True:
        params.update({"limit": limit, "start": start, "format": "json"})
        batch = api_request("GET", base_url, path, params, None, api_key) or []
        if not batch:
            break
        all_items.extend(batch)
        if len(batch) < limit:
            break
        start += len(batch)
    return all_items


def get_collections(base_url: str, api_key: str | None):
    items = api_paged(base_url, "collections", {}, api_key)
    results = []
    for item in items:
        data = item.get("data", item)
        results.append(
            {
                "key": item.get("key") or data.get("key"),
                "name": data.get("name"),
                "parent": data.get("parentCollection"),
            }
        )
    return results


def find_collection_key(collections: list[dict], name: str) -> str | None:
    for c in collections:
        if c.get("name") == name:
            return c.get("key")
    return None


def ensure_subcollection(base_url: str, api_key: str | None, parent_key: str, sub_name: str):
    collections = get_collections(base_url, api_key)
    for c in collections:
        if c.get("name") == sub_name and c.get("parent") == parent_key:
            return c.get("key")
    payload = [{"name": sub_name, "parentCollection": parent_key}]
    resp = api_request("POST", base_url, "collections", None, payload, api_key)
    if isinstance(resp, dict) and resp.get("success"):
        return resp["success"].get("0")
    if isinstance(resp, dict) and resp.get("key"):
        return resp["key"]
    raise SystemExit(f"Failed to create subcollection {sub_name}")


def creator_name(creator: dict) -> str:
    if creator.get("name"):
        return creator.get("name")
    first = creator.get("firstName") or ""
    last = creator.get("lastName") or ""
    return " ".join(x for x in [first, last] if x).strip()


def creators_to_authors(creators: list[dict]) -> list[str]:
    authors = []
    for creator in creators:
        if creator.get("creatorType") != "author":
            continue
        name = creator_name(creator)
        if name:
            authors.append(name)
    return authors


def pick_attachment_key(children: list[dict], storage_dir: Path) -> str | None:
    for child in children:
        cdata = child.get("data", child)
        if cdata.get("itemType") == "attachment" and cdata.get("contentType") == "application/pdf":
            key = child.get("key") or cdata.get("key")
            if not key:
                continue
            path = cdata.get("path") or ""
            if path.startswith("storage:"):
                return key
            cache_path = storage_dir / key / ".zotero-ft-cache"
            if cache_path.exists():
                return key
    return None


def read_cache(storage_dir: Path, attachment_key: str, limit: int) -> str | None:
    cache_path = storage_dir / attachment_key / ".zotero-ft-cache"
    if not cache_path.exists():
        return None
    text = cache_path.read_text(encoding="utf-8", errors="ignore").strip()
    if not text:
        return None
    return text[:limit]


def read_cache_full(storage_dir: Path, attachment_key: str) -> str | None:
    cache_path = storage_dir / attachment_key / ".zotero-ft-cache"
    if not cache_path.exists():
        return None
    text = cache_path.read_text(encoding="utf-8", errors="ignore").strip()
    if not text:
        return None
    return text


def extract_bibliography(text: str) -> list[str]:
    if not text:
        return []
    heading = re.search(
        r"\bBIBLIOGRAPHY\b|\bBIBLIOGRAPHIE\b|\bREFERENCES\b|\bRÉFÉRENCES\b",
        text,
        re.IGNORECASE,
    )
    if not heading:
        return []
    body = text[heading.end() :]
    body = re.sub(r"\s+", " ", body).strip()
    if not body:
        return []
    matches = list(re.finditer(r"(?<!\d)([1-9]\d?)\.\s+", body))
    if not matches:
        return [body]
    entries = []
    for idx, match in enumerate(matches):
        start = match.start()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(body)
        entry = body[start:end].strip()
        if entry:
            entries.append(entry)
    return entries


def build_note_html(
    item_key: str, meta: dict, attachment_key: str | None, snippet: str | None
) -> str:
    title = meta.get("title") or "Untitled"
    authors = ", ".join(meta.get("authors") or [])
    date = meta.get("date") or ""
    doi = meta.get("DOI") or ""
    url = meta.get("url") or ""
    lines = [
        f"<p><b>ZOTERO_CARD::{item_key}</b></p>",
        f"<p><b>Title:</b> {title}</p>",
        f"<p><b>Authors:</b> {authors}</p>",
        f"<p><b>Date:</b> {date}</p>",
        f"<p><b>DOI:</b> {doi}</p>",
        f"<p><b>URL:</b> {url}</p>",
        f"<p><b>Attachment key:</b> {attachment_key or ''}</p>",
    ]
    if snippet:
        safe = snippet.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
        lines.append("<p><b>Snippet:</b></p>")
        lines.append(f"<pre>{safe}</pre>")
    return "\n".join(lines)


def build_refs_note_html(item_key: str, title: str, refs: list[str]) -> str:
    safe_title = (
        (title or "Untitled").replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    )
    lines = [f"<p><b>ZOTERO_REFS::{item_key}</b></p>", f"<p><b>Title:</b> {safe_title}</p>"]
    if refs:
        lines.append("<ol>")
        for ref in refs:
            safe = ref.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            lines.append(f"<li>{safe}</li>")
        lines.append("</ol>")
    return "\n".join(lines)


def build_refitem_note_html(item_key: str, index: int, ref: str) -> str:
    safe = ref.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    lines = [
        f"<p><b>ZOTERO_REFITEM::{item_key}::{index}</b></p>",
        f"<p><b>Ref {index}:</b></p>",
        f"<p>{safe}</p>",
    ]
    return "\n".join(lines)


def collect_existing_marker_keys(
    base_url: str, api_key: str | None, collection_key: str, marker_prefix: str
) -> set[str]:
    notes = api_paged(
        base_url, f"collections/{collection_key}/items", {"itemType": "note"}, api_key
    )
    existing = set()
    marker = re.compile(re.escape(marker_prefix) + r"([A-Z0-9]+)")
    for note in notes:
        data = note.get("data", note)
        body = data.get("note", "")
        match = marker.search(body)
        if match:
            existing.add(match.group(1))
    return existing


def collect_existing_marker_indices(
    base_url: str, api_key: str | None, collection_key: str, marker_prefix: str
) -> set[int]:
    notes = api_paged(
        base_url, f"collections/{collection_key}/items", {"itemType": "note"}, api_key
    )
    existing = set()
    marker = re.compile(re.escape(marker_prefix) + r"(\d+)")
    for note in notes:
        data = note.get("data", note)
        body = data.get("note", "")
        match = marker.search(body)
        if match:
            try:
                existing.add(int(match.group(1)))
            except ValueError:
                pass
    return existing


def update_item_collections(
    base_url: str, api_key: str | None, item_key: str, version: int, data: dict, target_key: str
):
    collections = list(set((data.get("collections") or []) + [target_key]))
    payload = data.copy()
    payload["collections"] = collections
    headers_key = api_key
    params = None
    url = base_url.rstrip("/") + "/items/" + item_key
    req = urllib.request.Request(url, data=json.dumps(payload).encode("utf-8"), method="PUT")
    req.add_header("Content-Type", "application/json")
    req.add_header("If-Unmodified-Since-Version", str(version))
    if headers_key:
        req.add_header("Zotero-API-Key", headers_key)
    with urllib.request.urlopen(req, timeout=30) as resp:
        resp.read()


def main() -> int:
    parser = argparse.ArgumentParser(description="Create Zotero subcollection + cards.")
    parser.add_argument("--api-url", default=DEFAULT_API_URL, help="Zotero API base URL")
    parser.add_argument("--api-key", default=None, help="Zotero API key (optional)")
    parser.add_argument("--collection-name", default="Riemann", help="parent collection name")
    parser.add_argument("--subcollection-name", default="Weil", help="subcollection name")
    parser.add_argument("--filter-author", default="Weil", help="author substring filter")
    parser.add_argument("--filter-title", default=None, help="title substring filter")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument(
        "--ref-item-key", default=None, help="item key to extract bibliography from"
    )
    parser.add_argument("--storage", default=DEFAULT_STORAGE, help="Zotero storage dir")
    parser.add_argument("--snippet-chars", type=int, default=1500)
    parser.add_argument(
        "--add-items", action="store_true", help="add matching items to subcollection"
    )
    parser.add_argument("--create-notes", action="store_true", help="create card notes")
    parser.add_argument("--create-ref-notes", action="store_true", help="create bibliography notes")
    parser.add_argument(
        "--create-ref-items",
        action="store_true",
        help="create one note per bibliography entry",
    )
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    storage_dir = Path(args.storage).expanduser()
    base_url = args.api_url
    api_key = args.api_key or None

    collections = get_collections(base_url, api_key)
    parent_key = find_collection_key(collections, args.collection_name)
    if not parent_key:
        raise SystemExit(f"Parent collection not found: {args.collection_name}")
    sub_key = ensure_subcollection(base_url, api_key, parent_key, args.subcollection_name)

    items = api_paged(
        base_url,
        f"collections/{parent_key}/items",
        {"include": "data"},
        api_key,
    )
    items_by_key = {}
    matches = []
    for item in items:
        data = item.get("data", item)
        if data.get("itemType") == "attachment":
            continue
        item_key = item.get("key") or data.get("key")
        if item_key:
            items_by_key[item_key] = {
                "key": item_key,
                "version": item.get("version"),
                "data": data,
            }
        title = data.get("title") or ""
        creators = data.get("creators") or []
        authors = creators_to_authors(creators)
        author_match = (
            any(args.filter_author.lower() in a.lower() for a in authors)
            if args.filter_author
            else True
        )
        title_match = args.filter_title.lower() in title.lower() if args.filter_title else True
        if author_match and title_match:
            matches.append(
                {
                    "key": item.get("key") or data.get("key"),
                    "version": item.get("version"),
                    "data": data,
                    "authors": authors,
                }
            )

    if args.limit is not None:
        matches = matches[: args.limit]

    existing_cards = collect_existing_marker_keys(base_url, api_key, sub_key, "ZOTERO_CARD::")
    existing_refs = (
        collect_existing_marker_keys(base_url, api_key, sub_key, "ZOTERO_REFS::")
        if args.create_ref_notes
        else set()
    )
    existing_refitems = (
        collect_existing_marker_indices(
            base_url, api_key, sub_key, f"ZOTERO_REFITEM::{args.ref_item_key}::"
        )
        if args.create_ref_items and args.ref_item_key
        else set()
    )
    new_notes = []
    processed = 0

    for item in matches:
        item_key = item.get("key")
        if not item_key:
            continue
        data = item["data"]
        if args.add_items and not args.dry_run:
            update_item_collections(base_url, api_key, item_key, item["version"], data, sub_key)

        if args.create_notes:
            if item_key in existing_cards:
                continue
            children = api_paged(
                base_url, f"items/{item_key}/children", {"include": "data"}, api_key
            )
            attachment_key = pick_attachment_key(children, storage_dir)
            snippet = (
                read_cache(storage_dir, attachment_key, args.snippet_chars)
                if attachment_key
                else None
            )
            note_html = build_note_html(
                item_key,
                {
                    "title": data.get("title"),
                    "authors": item["authors"],
                    "date": data.get("date"),
                    "DOI": data.get("DOI"),
                    "url": data.get("url"),
                },
                attachment_key,
                snippet,
            )
            note = {
                "itemType": "note",
                "note": note_html,
                "collections": [sub_key],
                "tags": [{"tag": "zotero-card"}, {"tag": args.subcollection_name}],
            }
            new_notes.append(note)

        if args.create_ref_notes:
            if item_key in existing_refs:
                continue
            children = api_paged(
                base_url, f"items/{item_key}/children", {"include": "data"}, api_key
            )
            attachment_key = pick_attachment_key(children, storage_dir)
            refs = []
            if attachment_key:
                full_text = read_cache_full(storage_dir, attachment_key)
                if full_text:
                    refs = extract_bibliography(full_text)
            if refs:
                note_html = build_refs_note_html(item_key, data.get("title") or "", refs)
                note = {
                    "itemType": "note",
                    "note": note_html,
                    "collections": [sub_key],
                    "tags": [
                        {"tag": "zotero-refs"},
                        {"tag": args.subcollection_name},
                    ],
                }
                new_notes.append(note)

        processed += 1

    if args.create_ref_items:
        if not args.ref_item_key:
            raise SystemExit("--ref-item-key is required with --create-ref-items")
        source = items_by_key.get(args.ref_item_key)
        if not source:
            raise SystemExit(f"ref item not found in collection: {args.ref_item_key}")
        children = api_paged(
            base_url,
            f"items/{args.ref_item_key}/children",
            {"include": "data"},
            api_key,
        )
        attachment_key = pick_attachment_key(children, storage_dir)
        refs = []
        if attachment_key:
            full_text = read_cache_full(storage_dir, attachment_key)
            if full_text:
                refs = extract_bibliography(full_text)
        for idx, ref in enumerate(refs, start=1):
            if idx in existing_refitems:
                continue
            note_html = build_refitem_note_html(args.ref_item_key, idx, ref)
            note = {
                "itemType": "note",
                "note": note_html,
                "collections": [sub_key],
                "tags": [
                    {"tag": "zotero-refitem"},
                    {"tag": args.subcollection_name},
                ],
            }
            new_notes.append(note)

    if args.dry_run:
        print(f"Matches: {len(matches)}")
        return 0

    if args.create_notes and new_notes:
        chunk = 10
        for i in range(0, len(new_notes), chunk):
            payload = new_notes[i : i + chunk]
            api_request("POST", base_url, "items", None, payload, api_key)

    print(
        textwrap.dedent(
            f"""
            Subcollection: {args.subcollection_name} ({sub_key})
            Matched items: {len(matches)}
            Notes created: {len(new_notes)}
            """
        ).strip()
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
