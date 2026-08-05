#!/usr/bin/env python3
"""Wave 2, step 2: migrate DOSSIERS and POSTMORTEMS into knowledge.db.

Sources:
  q3.lean.aristotle/docs/insights/*.md   194  long-form dossiers (canonical)
  q3.lean.aristotle/KB/insights/*.md      56  a stale 2026-02-09 snapshot of the above,
                                              differing only by a YAML frontmatter block;
                                              only 3 files exist ONLY here — those are carried
                                              over, the rest are skipped as duplicates
  q3.lean.aristotle/docs/ERRORS_DESTROYER.md  1  process postmortem (the KB copy differs by
                                              six lines of frontmatter — not migrated twice)

The directory mixes four units under one roof; `subtype` separates them so a query for a
dossier does not drown in playbooks and reference sheets. Full body text is stored: without it
the table answers "does a file exist" instead of "what did we conclude".
"""

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import kb  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
DOCS_INSIGHTS = REPO / "q3.lean.aristotle/docs/insights"
KB_INSIGHTS = REPO / "q3.lean.aristotle/KB/insights"
SRC_ERRORS = REPO / "q3.lean.aristotle/docs/ERRORS_DESTROYER.md"

DOSSIER_COLUMNS = ("slug", "title", "date", "status_token", "verdict", "subtype",
                   "tags", "priority", "body_md", "source_file")
PM_COLUMNS = ("id", "date", "context", "found_by", "what_happened", "root_cause",
              "rule", "checklist", "correct_path", "source_file")

DATE_IN_NAME = re.compile(r"(20\d\d)[_-](\d\d)[_-](\d\d)")


def rel(p: Path) -> str:
    return str(p.relative_to(REPO))


def norm(t):
    return " ".join(t.split()) if t else None


def subtype_of(name: str, body: str) -> str:
    n = name.lower()
    if "template" in n:
        return "template"
    if "playbook" in n or "workflow" in n or "discipline" in n or "recovery" in n:
        return "playbook"
    if "reference" in n or "constants" in n or "cheat" in n or n.startswith("index"):
        return "reference"
    return "dossier"


def parse_dossier(path: Path, source_label: str):
    text = path.read_text(errors="ignore")
    tags = priority = None
    fm = re.match(r"---\n(.*?)\n---\n", text, re.S)
    if fm:                                   # KB copies carry a YAML frontmatter layer
        block = fm.group(1)
        t = re.search(r"tags:\s*\[(.*?)\]", block)
        p = re.search(r"priority:\s*(\S+)", block)
        tags = t.group(1).strip() if t else None
        priority = p.group(1).strip() if p else None
        text = text[fm.end():]

    title = None
    m = re.search(r"^#\s+(.+)$", text, re.M)
    if m:
        title = norm(re.sub(r"\(\d{4}-\d\d-\d\d\)", "", m.group(1)))

    d = DATE_IN_NAME.search(path.stem)
    date = f"{d.group(1)}-{d.group(2)}-{d.group(3)}" if d else None
    if not date:
        dm = re.search(r"\*\*Дата:\*\*\s*(\S+)|\((\d{4}-\d\d-\d\d)\)", text)
        if dm:
            date = dm.group(1) or dm.group(2)

    def section(*names):
        for nm in names:
            sm = re.search(rf"^#{{2,3}}\s*{nm}\s*\n+(.+?)(?=\n#{{1,3}}\s|\Z)", text,
                           re.S | re.M | re.I)
            if sm:
                return norm(sm.group(1))[:600]
        return None

    return {
        "slug": path.stem, "title": title or path.stem, "date": date,
        "status_token": section("Status", "Статус"),
        "verdict": section("Verdict", "Вывод", "Meaning", "Current truth"),
        "subtype": subtype_of(path.name, text),
        "tags": tags, "priority": priority, "body_md": text,
        "source_file": source_label,
    }


def parse_postmortems():
    text = SRC_ERRORS.read_text()
    rows = []
    for m in re.finditer(r"^## (Ошибка #(\d+)[^\n]*)\n(.*?)(?=\n## |\Z)", text, re.S | re.M):
        title, num, body = m.group(1), m.group(2), m.group(3)
        if "шаблон" in title.lower() or "template" in title.lower():
            continue                                   # the fill-in form, never used

        def bold(label):
            bm = re.search(rf"\*\*{label}:?\*\*\s*(.+)", body)
            return norm(bm.group(1)) if bm else None

        def sect(name):
            sm = re.search(rf"^### {name}[^\n]*\n+(.+?)(?=\n### |\Z)", body, re.S | re.M)
            return norm(sm.group(1))[:1500] if sm else None

        rows.append({
            "id": f"ERR_{int(num):02d}", "date": bold("Дата"), "context": bold("Контекст"),
            "found_by": bold("Кто нашёл"), "what_happened": sect("Что произошло"),
            "root_cause": sect("Корневая причина"), "rule": sect("Правило"),
            "checklist": sect("Чеклист"), "correct_path": sect("Как должен был поступить"),
            "source_file": rel(SRC_ERRORS),
        })
    return rows


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    canonical = sorted(p for p in DOCS_INSIGHTS.glob("*.md"))
    dossiers = [parse_dossier(p, rel(DOCS_INSIGHTS)) for p in canonical]
    have = {d["slug"] for d in dossiers}

    orphans = []
    if KB_INSIGHTS.exists():
        for p in sorted(KB_INSIGHTS.glob("*.md")):
            if p.stem not in have:
                orphans.append(parse_dossier(p, rel(KB_INSIGHTS)))
    print(f"docs/insights            {len(dossiers):3d} dossiers (canonical)")
    print(f"KB/insights orphans      {len(orphans):3d} carried over "
          f"({len(list(KB_INSIGHTS.glob('*.md'))) - len(orphans)} skipped as duplicates)")
    dossiers += orphans

    pms = parse_postmortems()
    print(f"ERRORS_DESTROYER         {len(pms):3d} postmortem(s)")

    by_subtype = {}
    for d in dossiers:
        by_subtype[d["subtype"]] = by_subtype.get(d["subtype"], 0) + 1
    dated = sum(1 for d in dossiers if d["date"])
    with_status = sum(1 for d in dossiers if d["status_token"])
    print(f"\ntotal {len(dossiers)} dossiers · by subtype {by_subtype}")
    print(f"with a parsed date: {dated}/{len(dossiers)} · with a status line: "
          f"{with_status}/{len(dossiers)}")
    if args.dry_run:
        return 0

    conn = kb.connect()
    conn.executemany(
        f"INSERT OR REPLACE INTO dossier ({','.join(DOSSIER_COLUMNS)}) "
        f"VALUES ({','.join('?' * len(DOSSIER_COLUMNS))})",
        [tuple(d.get(c) for c in DOSSIER_COLUMNS) for d in dossiers])
    conn.execute("INSERT INTO dossier_fts(dossier_fts) VALUES('delete-all')")
    conn.execute("INSERT INTO dossier_fts(rowid, title, status_token, verdict, body_md) "
                 "SELECT rowid, title, status_token, verdict, body_md FROM dossier")
    conn.executemany(
        f"INSERT OR REPLACE INTO postmortem ({','.join(PM_COLUMNS)}) "
        f"VALUES ({','.join('?' * len(PM_COLUMNS))})",
        [tuple(r.get(c) for c in PM_COLUMNS) for r in pms])
    conn.executemany(
        "INSERT OR REPLACE INTO source_ledger (source_file, expected_rows, migrated_at, note) "
        "VALUES (?,?,?,?)",
        [(rel(DOCS_INSIGHTS), len(canonical), "2026-08-05", "wave 2 dossiers"),
         (rel(SRC_ERRORS), len(pms), "2026-08-05", "wave 2 postmortems")])
    conn.commit()
    print("migrated into", kb.DB_PATH)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
