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
PAPERS = ROOT / "external" / "papers"


def load_index():
    if INDEX.exists():
        return json.loads(INDEX.read_text())
    return {"generated_at": None, "queries": [], "results": []}


def save_index(data):
    data["generated_at"] = datetime.utcnow().isoformat() + "Z"
    INDEX.write_text(json.dumps(data, indent=2, ensure_ascii=False))


def download_pdf(url, out_path):
    if requests is None:
        raise RuntimeError("requests not available")
    resp = requests.get(url, timeout=30)
    resp.raise_for_status()
    out_path.write_bytes(resp.content)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--id", required=True)
    ap.add_argument("--url", default=None)
    ap.add_argument("--pdf", default=None)
    ap.add_argument("--title", default=None)
    ap.add_argument("--authors", default=None)
    ap.add_argument("--year", default=None)
    ap.add_argument("--source", default="manual")
    args = ap.parse_args()

    data = load_index()
    entry = {
        "source": args.source,
        "id": args.id,
        "title": args.title,
        "authors": args.authors.split(",") if args.authors else [],
        "year": args.year,
        "url": args.url,
        "pdf_url": args.pdf,
        "status": "ingested",
    }

    # Download PDF if provided
    if args.pdf:
        PAPERS.mkdir(parents=True, exist_ok=True)
        out_path = PAPERS / (args.id.replace("/", "_") + ".pdf")
        try:
            download_pdf(args.pdf, out_path)
            entry["pdf_path"] = str(out_path)
        except Exception as e:
            print(f"PDF download failed: {e}", file=sys.stderr)

    data["results"].append(entry)
    save_index(data)
    print(f"Ingested {args.id} -> {INDEX}")


if __name__ == "__main__":
    main()
