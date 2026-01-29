#!/usr/bin/env python3
import argparse
import json
import urllib.parse
import urllib.request
from pathlib import Path


def api_request(method: str, base_url: str, path: str, params: dict | None, payload, api_key: str):
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
    return json.loads(body) if body else None


def api_paged(base_url: str, path: str, params: dict | None, api_key: str, limit: int = 100):
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


def get_collections(base_url: str, api_key: str):
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


def ensure_subcollection(base_url: str, api_key: str, parent_key: str, sub_name: str):
    collections = get_collections(base_url, api_key)
    for c in collections:
        if c.get("name") == sub_name and c.get("parent") == parent_key:
            return c.get("key")
    payload = [{"name": sub_name, "parentCollection": parent_key}]
    resp = api_request("POST", base_url, "collections", None, payload, api_key) or {}
    if isinstance(resp, dict) and resp.get("success"):
        return resp["success"].get("0")
    raise SystemExit(f"Failed to create subcollection {sub_name}")


def load_links(path: Path) -> list[dict]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, list):
        raise SystemExit("Links JSON must be a list of objects")
    return data


def existing_urls(base_url: str, api_key: str, collection_key: str) -> set[str]:
    items = api_paged(
        base_url,
        f"collections/{collection_key}/items",
        {"include": "data"},
        api_key,
    )
    urls = set()
    for item in items:
        data = item.get("data", item)
        if data.get("itemType") == "attachment":
            continue
        url = data.get("url")
        if url:
            urls.add(url)
    return urls


def build_item_payload(item: dict, collection_key: str):
    payload = {
        "itemType": item.get("itemType", "document"),
        "title": item.get("title", "Untitled"),
        "collections": [collection_key],
    }
    if item.get("url"):
        payload["url"] = item["url"]
    if item.get("date"):
        payload["date"] = item["date"]
    if item.get("shortTitle"):
        payload["shortTitle"] = item["shortTitle"]
    if item.get("creators"):
        payload["creators"] = item["creators"]
    if item.get("tags"):
        payload["tags"] = [{"tag": t} for t in item["tags"]]
    return payload


def create_item(base_url: str, api_key: str, payload: dict) -> str | None:
    resp = api_request("POST", base_url, "items", None, [payload], api_key) or {}
    if "success" in resp and "0" in resp["success"]:
        return resp["success"]["0"]
    return None


def create_note(base_url: str, api_key: str, parent_key: str, note: str):
    payload = {
        "itemType": "note",
        "note": note,
        "parentItem": parent_key,
    }
    api_request("POST", base_url, "items", None, [payload], api_key)


def create_attachment(base_url: str, api_key: str, parent_key: str, url: str, title: str | None):
    payload = {
        "itemType": "attachment",
        "parentItem": parent_key,
        "linkMode": "linked_url",
        "title": title or "PDF",
        "url": url,
        "contentType": "application/pdf",
    }
    api_request("POST", base_url, "items", None, [payload], api_key)


def main() -> int:
    parser = argparse.ArgumentParser(description="Add external links to Zotero via Web API.")
    parser.add_argument("--api-url", required=True, help="Zotero API base URL")
    parser.add_argument("--api-key", required=True, help="Zotero API key")
    parser.add_argument("--collection-name", required=True, help="parent collection name")
    parser.add_argument("--subcollection-name", default=None, help="optional subcollection name")
    parser.add_argument("--input", required=True, help="JSON file with links")
    args = parser.parse_args()

    base_url = args.api_url
    api_key = args.api_key
    collections = get_collections(base_url, api_key)
    parent_key = find_collection_key(collections, args.collection_name)
    if not parent_key:
        raise SystemExit(f"Parent collection not found: {args.collection_name}")
    target_key = (
        ensure_subcollection(base_url, api_key, parent_key, args.subcollection_name)
        if args.subcollection_name
        else parent_key
    )

    links = load_links(Path(args.input))
    seen_urls = existing_urls(base_url, api_key, target_key)
    created = 0
    skipped = 0

    for item in links:
        url = item.get("url")
        if url and url in seen_urls:
            skipped += 1
            continue
        payload = build_item_payload(item, target_key)
        item_key = create_item(base_url, api_key, payload)
        if not item_key:
            continue
        created += 1
        if item.get("note"):
            create_note(base_url, api_key, item_key, item["note"])
        attachment_url = item.get("attachment_url")
        if attachment_url:
            create_attachment(
                base_url, api_key, item_key, attachment_url, item.get("attachment_title")
            )
        if url:
            seen_urls.add(url)

    print(f"Created: {created}, skipped: {skipped}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
