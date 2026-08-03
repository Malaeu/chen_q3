#!/usr/bin/env python3
"""Zotero live-sync — pull the RH collections from the local Zotero HTTP API.

Zotero 7 desktop exposes a read-only local API on http://localhost:23119/api/
(mirrors the web API, no key needed). This pulls the RH-relevant collections
(name matches riemann|weil|clay|prolate|zeta) as BibTeX + CSL-JSON into
litreview/zotero/, so the citation ledger stays in sync with the owner's actual
Zotero — no manual copy-paste.

    python3 docs/routeB_bus/litreview/zotero_pull.py            # pull
    python3 docs/routeB_bus/litreview/zotero_pull.py --list     # just list collections

Fails gracefully (exit 2) if Zotero is not running, so the pipeline does not
break on a machine without Zotero.
"""
from __future__ import annotations
import argparse
import json
import re
import sys
import urllib.request
from pathlib import Path

BASE = "http://localhost:23119/api/users/0"
OUT = Path(__file__).resolve().parent / "zotero"
RELEVANT = re.compile(r"riemann|weil|clay|prolate|zeta", re.I)


def get(url: str, timeout: int = 30) -> bytes:
    with urllib.request.urlopen(url, timeout=timeout) as r:
        return r.read()


def collections() -> list[dict]:
    data = json.loads(get(f"{BASE}/collections?limit=100&format=json"))
    return [{"key": c["data"]["key"], "name": c["data"]["name"],
             "n": c["meta"].get("numItems", "?")} for c in data]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", action="store_true")
    args = ap.parse_args()

    try:
        if b"Zotero is running" not in get("http://localhost:23119/connector/ping", 5):
            raise RuntimeError
    except Exception:
        print("Zotero local server not reachable on :23119 — is Zotero running?")
        return 2

    cols = collections()
    if args.list:
        for c in cols:
            print(f"{c['key']}  ({c['n']:>3} items)  {c['name']}")
        return 0

    OUT.mkdir(parents=True, exist_ok=True)
    total = 0
    pulled = []
    for c in cols:
        if not RELEVANT.search(c["name"]):
            continue
        safe = re.sub(r"[^\w.-]", "_", c["name"])
        bib = get(f"{BASE}/collections/{c['key']}/items?limit=100"
                  f"&format=bibtex&itemType=-attachment")
        (OUT / f"{safe}.bib").write_bytes(bib)
        n = bib.count(b"\n@")  + (1 if bib.lstrip().startswith(b"@") else 0)
        total += n
        pulled.append(f"  {c['name']} ({c['key']}): {n} entries -> zotero/{safe}.bib")

    print(f"Zotero live-sync: pulled {len(pulled)} RH-relevant collections, {total} bib entries")
    for p in pulled:
        print(p)
    print("(re-run after editing Zotero to refresh; reconcile new keys into REFERENCES.md)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
