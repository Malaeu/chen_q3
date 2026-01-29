#!/usr/bin/env python3
import argparse
import json
import re
import urllib.parse
import urllib.request
from pathlib import Path

BASE_URL = "https://www.claymath.org/library/Quillen/Working_papers/"


def fetch(url: str) -> str:
    with urllib.request.urlopen(url, timeout=30) as resp:
        return resp.read().decode("utf-8", errors="ignore")


def extract_year_dirs(html: str) -> list[tuple[int, str]]:
    results = []
    for match in re.finditer(r'href="(quillen%20(\d{4})/)"', html, re.IGNORECASE):
        href = match.group(1)
        year = int(match.group(2))
        results.append((year, href))
    return results


def extract_pdf_links(html: str) -> list[str]:
    links = []
    for match in re.finditer(r'href="([^"]+\.pdf)"', html, re.IGNORECASE):
        links.append(match.group(1))
    return links


def build_title(year: int, filename: str) -> tuple[str, str]:
    stem = Path(urllib.parse.unquote(filename)).stem
    title = f"Quillen Working Paper {stem}"
    short = f"Quillen WP {stem}"
    if str(year) not in stem:
        title = f"Quillen Working Paper {year} {stem}"
        short = f"Quillen WP {year} {stem}"
    return title, short


def download_pdf(url: str, target: Path):
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        return
    with urllib.request.urlopen(url, timeout=60) as resp:
        data = resp.read()
    target.write_bytes(data)


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate JSON for Quillen working papers.")
    parser.add_argument("--base-url", default=BASE_URL)
    parser.add_argument("--from-year", type=int, default=1999)
    parser.add_argument("--to-year", type=int, default=2003)
    parser.add_argument("--out-json", required=True)
    parser.add_argument("--download-dir", default=None)
    args = parser.parse_args()

    base_url = args.base_url.rstrip("/") + "/"
    root_html = fetch(base_url)
    year_dirs = extract_year_dirs(root_html)
    target_dirs = [d for d in year_dirs if args.from_year <= d[0] <= args.to_year]

    entries: list[dict] = []
    for year, href in sorted(target_dirs):
        year_url = urllib.parse.urljoin(base_url, href)
        year_html = fetch(year_url)
        pdfs = extract_pdf_links(year_html)
        for pdf in pdfs:
            pdf_url = urllib.parse.urljoin(year_url, pdf)
            title, short = build_title(year, pdf)
            entry = {
                "title": title,
                "shortTitle": short,
                "itemType": "document",
                "url": pdf_url,
                "date": str(year),
                "tags": ["quillen-working-papers", "speculative-edge"],
                "attachment_url": pdf_url,
            }
            if year == 2003 and "2003-1" in pdf:
                entry["shortTitle"] = "Quillen's Last Stand"
                entry["note"] = "Quillen's Last Stand — source for speculative edges."
                entry["tags"].append("quillen-last-stand")
            entries.append(entry)

            if args.download_dir:
                out_dir = Path(args.download_dir) / str(year)
                filename = Path(urllib.parse.unquote(pdf)).name
                download_pdf(pdf_url, out_dir / filename)

    Path(args.out_json).write_text(json.dumps(entries, indent=2), encoding="utf-8")
    print(f"Entries: {len(entries)} -> {args.out_json}")
    if args.download_dir:
        print(f"Downloaded to: {args.download_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
