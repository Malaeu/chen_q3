#!/usr/bin/env python3
import argparse
import json
import sys
from datetime import datetime
from pathlib import Path

try:
    import requests  # type: ignore
except Exception:
    requests = None

ROOT = Path(__file__).resolve().parents[2]
INDEX = ROOT / "external" / "index.json"

ARXIV_API = "http://export.arxiv.org/api/query"


def load_index():
    if INDEX.exists():
        return json.loads(INDEX.read_text())
    return {"generated_at": None, "queries": [], "results": []}


def save_index(data):
    data["generated_at"] = datetime.utcnow().isoformat() + "Z"
    INDEX.write_text(json.dumps(data, indent=2, ensure_ascii=False))


def arxiv_search(query, max_results=5):
    if requests is None:
        return []
    params = {
        "search_query": f"all:{query}",
        "start": 0,
        "max_results": max_results,
    }
    resp = requests.get(ARXIV_API, params=params, timeout=20)
    resp.raise_for_status()
    text = resp.text
    # Minimal parse (no full XML parser to keep dependencies light)
    results = []
    for entry in text.split("<entry>")[1:]:
        title = _extract_tag(entry, "title")
        arxiv_id = _extract_tag(entry, "id")
        pdf_url = None
        for line in entry.split("<link "):
            if "type=\"application/pdf\"" in line and "href=" in line:
                pdf_url = line.split("href=\"")[1].split("\"")[0]
                break
        authors = []
        for a in entry.split("<author>")[1:]:
            authors.append(_extract_tag(a, "name"))
        results.append(
            {
                "source": "arxiv",
                "id": arxiv_id,
                "title": title,
                "authors": authors,
                "year": None,
                "url": arxiv_id,
                "pdf_url": pdf_url,
                "status": "candidate",
            }
        )
    return results


def _extract_tag(blob, tag):
    if f"<{tag}>" not in blob:
        return None
    return blob.split(f"<{tag}>", 1)[1].split(f"</{tag}>", 1)[0].strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--query", action="append", default=[], help="Search query")
    ap.add_argument("--max", type=int, default=5, help="Max results per query")
    ap.add_argument("--no-arxiv", action="store_true", help="Disable arXiv search")
    args = ap.parse_args()

    if not args.query:
        print("No queries provided.", file=sys.stderr)
        sys.exit(1)

    data = load_index()
    data["queries"] = list(dict.fromkeys(data.get("queries", []) + args.query))

    new_results = []
    if not args.no_arxiv:
        for q in args.query:
            try:
                new_results.extend(arxiv_search(q, args.max))
            except Exception as e:
                print(f"arXiv search failed for '{q}': {e}", file=sys.stderr)

    if new_results:
        data["results"].extend(new_results)
    save_index(data)
    print(f"Saved {len(new_results)} new results to {INDEX}")


if __name__ == "__main__":
    main()
