#!/usr/bin/env python3
"""litreview validator — chain-of-evidence check for the citation ledger.

Flags:
  - REFERENCES.md rows marked HAVE/OA but with no matching file in pdfs/;
  - PDFs in pdfs/ with no row in REFERENCES.md;
  - rows with an empty "USED FOR" cell (a source indexed but not tied to a gap/lemma).

Read-only. Run alongside orchestrator/spine.py.
    python3 docs/routeB_bus/litreview/litreview_check.py
"""
from __future__ import annotations
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REFS = HERE / "REFERENCES.md"
PDFS = HERE / "pdfs"


def main() -> int:
    text = REFS.read_text(encoding="utf-8")
    rows = re.findall(r"^\| (?!Key\b)(?!-)([^|]+)\|([^|]+)\|([^|]+)\|([^|]+)\|([^|]+)\|([^|]+)\|",
                      text, re.M)
    on_disk = {p.name for p in PDFS.glob("*") if p.is_file()} if PDFS.is_dir() else set()
    referenced = set()
    problems = []
    for key, bib, url, pdf, access, usedfor in rows:
        key = key.strip()
        pdf = pdf.strip()
        access = access.strip()
        usedfor = usedfor.strip()
        m = re.search(r"pdfs/([^\s`]+)", pdf)
        if m:
            fname = m.group(1)
            referenced.add(fname)
            if fname not in on_disk and "✓" in access:
                problems.append(f"MISSING PDF: {key} claims {fname} (OA) but not in pdfs/")
        if not usedfor or usedfor in ("—", "-"):
            problems.append(f"NO USAGE MAPPING: {key} indexed but 'USED FOR' empty")
    orphans = on_disk - referenced
    for o in sorted(orphans):
        problems.append(f"ORPHAN PDF: pdfs/{o} has no REFERENCES.md row")

    print(f"litreview: {len(rows)} indexed rows, {len(on_disk)} PDFs on disk")
    if problems:
        print("PROBLEMS:")
        for p in problems:
            print(f"  - {p}")
        return 1
    print("OK — every OA row has its PDF, every PDF is indexed, every row has a usage.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
