#!/usr/bin/env python3
"""Wave 3: migrate Proshka verdicts — the kill knowledge that never reached any atlas.

Discovery (2026-08-05): 109 PROSHKA_*.md files exist but only 61 are distinct — 47 names
appear in two or more places (canon + mirror), 43 of those byte-identical. Of the 61:
  * 18 carry a structured `iteration:` M3 block (target / failed_strategy / new_gap_name /
    invariant_learned / forbidden_future_move / next_decisive_test) — the same shape as
    FAILED_STRATEGIES.yaml, which is exactly why they belong in `kill` as strategy rows;
  * 34 carry KILL / FATAL / REJECT markers at verdict level.

Until today only the single 2026-08-05 G6/S2 kill had been hand-copied into
ROUTE_KILL_REGISTRY.md. The rest lived only inside verdict prose — invisible to any query.

Dedup rules:
  * one stable row per semantic component of a distinct verdict NAME.  A verdict carrying
    both an `iteration:` block and a structured KILL emits two rows; collapsing those two
    statements loses the surviving strategy memory or the operational closeout;
  * a strategy already migrated from FAILED_STRATEGIES.yaml is NOT re-inserted — the verdict
    becomes an evidence row and an alias on the existing record instead.
"""

import argparse
import collections
import datetime
import hashlib
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import kb  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
# Verdict bodies live under the bus; the four PROSHKA_* config files are not verdicts.
CONFIG_NAMES = {"PROSHKA_ENTRYPOINT.md", "PROSHKA_MEMORY_PACK.md", "PROSHKA_POLICY.md",
                "PROSHKA_SYSTEM_PROMPT_v2.md", "PROSHKA_CONTEXT_SINGLE_SCALE_2026_01_24.md"}
IGNORED_PATH_PARTS = {".git", ".lake", ".qmd_cache", "_backups"}
DATE_RE = re.compile(r"(20\d\d)-(\d\d)-(\d\d)")


def norm(t, limit=1200):
    return " ".join(t.split())[:limit] if t else None


def collect_files():
    files = [p for p in REPO.rglob("PROSHKA_*.md")
             if not IGNORED_PATH_PARTS.intersection(p.parts) and p.name not in CONFIG_NAMES]
    by_name = collections.defaultdict(list)
    for p in files:
        by_name[p.name].append(p)
    # Canonical copy: prefer the bus mirror the read-only channels actually fetch.
    def rank(p: Path):
        s = str(p)
        return (0 if "/docs/routeB_bus/proshka/" in s else
                1 if "/docs/routeB_bus/" in s else
                2 if "/proshka/" in s else 3, len(s))
    return {n: sorted(v, key=rank) for n, v in by_name.items()}


def reconcile_projection(conn, live_names: set[str]) -> tuple[int, int]:
    """Remove derived-cache evidence and rows whose canonical verdict vanished.

    The migration is a projection of repository sources.  A machine-local qmd
    mirror must never become provenance, and a removed source must not survive
    only because that mirror happened to retain an old copy.
    """
    stale_evidence = []
    for kill_id, kind, ref in conn.execute(
        "SELECT kill_id, kind, ref FROM kill_evidence "
        "WHERE kind IN ('verdict', 'verdict_copy')"
    ):
        path = Path(ref)
        if ".qmd_cache" in path.parts or not (REPO / path).is_file():
            stale_evidence.append((kill_id, kind, ref))
    conn.executemany(
        "DELETE FROM kill_evidence WHERE kill_id=? AND kind=? AND ref=?",
        stale_evidence,
    )

    stale_sources = [
        source_file
        for (source_file,) in conn.execute(
            "SELECT source_file FROM source_ledger WHERE note='wave 3 verdicts'"
        )
        if Path(source_file).name not in live_names
    ]
    removed_kills = 0
    for source_file in stale_sources:
        kill_ids = [
            row[0]
            for row in conn.execute(
                "SELECT id FROM kill WHERE source_file=?", (source_file,)
            )
        ]
        for kill_id in kill_ids:
            conn.execute("DELETE FROM kill_evidence WHERE kill_id=?", (kill_id,))
            conn.execute("DELETE FROM kill_alias WHERE kill_id=?", (kill_id,))
            conn.execute(
                "DELETE FROM link WHERE (from_type='kill' AND from_id=?) "
                "OR (to_type='kill' AND to_id=?)",
                (kill_id, kill_id),
            )
            conn.execute("DELETE FROM kill WHERE id=?", (kill_id,))
            removed_kills += 1
        conn.execute("DELETE FROM source_ledger WHERE source_file=?", (source_file,))
    return len(stale_evidence), removed_kills


def parse_iteration(text):
    m = re.search(r"^iteration:\s*\n(.*?)(?=\n```|\n#{1,3} |\Z)", text, re.S | re.M)
    if not m:
        return None
    block = m.group(1)
    out = {}
    for fm in re.finditer(r"^\s{2,}(\w+):\s*(.+?)\s*$", block, re.M):
        out[fm.group(1)] = fm.group(2).strip()
    return out or None


def parse_closes_opens(text):
    """W9 supplier-ledger lines from a SOURCE RECORD header.

    CLOSES: names this node settles → its `provides`.
    OPENS:  new inputs it creates   → its `requires`.
    Both are comma- or list-separated catalog names. `none`/`-` counts as empty.
    Returns (closes, opens, lean_path, theorem) or None when neither line exists.
    """
    def grab(field):
        # Inline form: `CLOSES: A, B` / `CLOSES: []` / `CLOSES: none`.
        # `[ \t]*`, not `\s*`: `\s` swallows the newline and captures the first
        # item of a block list as if it were an inline value.
        m = re.search(rf"^\s*{field}:[ \t]*(\S.*?)\s*$", text, re.M)
        if m:
            raw = m.group(1).strip()
            if raw.lower() in ("none", "-", "[]", "нет"):
                return []
            return [t.strip().lstrip("- ").strip()
                    for t in re.split(r"[,;]", raw) if t.strip()]
        # Block-list form: `OPENS:` followed by `  - NAME` lines.
        m = re.search(rf"^\s*{field}:\s*\n((?:\s+-\s+\S.*\n?)+)", text, re.M)
        if m:
            return [ln.strip().lstrip("- ").strip()
                    for ln in m.group(1).splitlines() if ln.strip()]
        return None

    closes, opens_ = grab("CLOSES"), grab("OPENS")
    if closes is None and opens_ is None:
        return None
    lean = re.search(r"^\s*(?:LEAN_PATH:\s*\n?\s*|LEAN_PATH:\s*)"
                     r"(q3\.lean\.aristotle/\S+\.lean)", text, re.M)
    if not lean:
        lean = re.search(r"(q3\.lean\.aristotle/Q3/[\w/]+\.lean)", text)
    thm = re.search(r"^\s*-\s*(Q3\.RouteB\.\w+)", text, re.M)
    return (closes or [], opens_ or [],
            lean.group(1) if lean else None,
            thm.group(1) if thm else None)


def parse_verdict_kill(text):
    """Verdict-level kill markers, structured forms only.

    Prose mentions of KILL/FATAL are deliberately NOT harvested: in these verdicts the word
    also appears as "kill criterion", "kill-pass", "would kill" — migrating those would fill
    the table with claims nobody made. Files with prose-only mentions are reported instead.
    """
    for pat in (r"^PRIMARY:\s*(KILL[_A-Z0-9]*)",
                r"^\s*PRIMARY:\s*(KILL[_A-Z0-9]*)",
                r"SELECTED_RESULT:\s*\n\s*(KILL[_A-Z0-9]*)",
                r"^#\s*STATUS:\s*(FATAL[^\n]*)"):
        m = re.search(pat, text, re.M)
        if m:
            return m.group(1).strip(), None
    # `SOME_CLAIM: KILLED` — the subject is the field name itself.
    m = re.search(r"^([A-Z][A-Z_0-9]{3,}):\s*(KILLED|FATAL|REJECTED)\b", text, re.M)
    if m:
        return m.group(2), m.group(1)
    return None, None


def choose_kill_id(
    name: str,
    rel_canon: str,
    known_ids: dict[str, str | None],
) -> tuple[str, bool]:
    """Return a stable id and whether this verdict is already materialized.

    A repeated migration of the same named verdict must reuse its base id.
    A genuinely different verdict whose slug collides gets a deterministic
    content-independent suffix derived from its source name; repeated runs
    therefore reuse that same collision id as well.
    """
    base = kb.slugify(name.replace("PROSHKA_", "").replace(".md", ""), 60)
    source = known_ids.get(base)
    if source is None and base not in known_ids:
        return base, False
    if source and Path(source).name == Path(rel_canon).name:
        return base, True

    suffix = hashlib.sha256(name.encode("utf-8")).hexdigest()[:8].upper()
    candidate = f"{base[:51]}__{suffix}"
    candidate_source = known_ids.get(candidate)
    if candidate_source is None and candidate not in known_ids:
        return candidate, False
    if candidate_source and Path(candidate_source).name == Path(rel_canon).name:
        return candidate, True
    raise RuntimeError(f"stable verdict id collision: {name} -> {candidate}")


def choose_component_id(
    name: str,
    rel_canon: str,
    known_ids: dict[str, str | None],
    component: str,
    dual: bool,
) -> tuple[str, bool]:
    """Stable, class-aware row id for a verdict component.

    Historical single-component verdicts retain their old id.  For a dual verdict the
    iteration row retains the base id and the operational KILL gets an explicit suffix.
    """
    base, reused = choose_kill_id(name, rel_canon, known_ids)
    if component == "iteration" or not dual:
        return base, reused
    candidate = f"{base[:43]}__VERDICT_KILL"
    source = known_ids.get(candidate)
    if source is None and candidate not in known_ids:
        return candidate, False
    if source and Path(source).name == Path(rel_canon).name:
        return candidate, True
    suffix = hashlib.sha256((name + "\0kill").encode("utf-8")).hexdigest()[:8].upper()
    collision = f"{base[:32]}__VERDICT_KILL__{suffix}"
    collision_source = known_ids.get(collision)
    if collision_source is None and collision not in known_ids:
        return collision, False
    if collision_source and Path(collision_source).name == Path(rel_canon).name:
        return collision, True
    raise RuntimeError(f"stable verdict component id collision: {name} -> {collision}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--full", action="store_true",
                    help="печатать ВСЕ строки холостого прогона, без среза")
    ap.add_argument("--list-manual", action="store_true",
                    help="печатать все файлы с прозаическим убийством")
    args = ap.parse_args()

    by_name = collect_files()
    conn = kb.connect()
    known_strategies = {r[0] for r in conn.execute(
        "SELECT ref FROM kill_evidence WHERE kind='yaml_name'")}
    known_ids = {r[0]: r[1] for r in conn.execute("SELECT id, source_file FROM kill")}

    rows, evidence, aliases = [], [], []
    live_names = set()
    manual = []   # prose-only KILL mentions: reported, never invented into rows
    ledger_rows = []   # W9 CLOSES/OPENS → capability (provides/requires)
    known_ledger = {r[0] for r in conn.execute(
        "SELECT theorem FROM capability WHERE lens='supplier_ledger'")}
    n_iter = n_kill = n_reused = n_existing = 0

    for name, paths in sorted(by_name.items()):
        canon = paths[0]
        text = canon.read_text(errors="ignore")
        rel_canon = str(canon.relative_to(REPO))
        d = DATE_RE.search(name) or DATE_RE.search(text)
        date = f"{d.group(1)}-{d.group(2)}-{d.group(3)}" if d else None

        co = parse_closes_opens(text)
        if co is not None:
            closes, opens_, lean_path, thm = co
            subject = thm or name
            if subject not in known_ledger and (closes or opens_):
                ledger_rows.append({
                    "theorem": subject,
                    "file": lean_path or rel_canon,
                    "lens": "supplier_ledger",
                    "provides": "; ".join(closes) or "nothing_closed",
                    "requires": "; ".join(opens_),
                    "strength": "declared",
                    "run_id": "supplier_ledger_w9",
                })

        it = parse_iteration(text)
        verdict_kill, killed_subject = parse_verdict_kill(text)
        if not it and not verdict_kill:
            if re.search(r"\bKILL(ED)?\b|\bFATAL\b", text):
                manual.append((name, rel_canon))
            continue
        live_names.add(name)

        component_ids: list[str] = []
        iteration_reused = False
        if it and it.get("failed_strategy") in known_strategies:
            # Already migrated from FAILED_STRATEGIES.yaml — attach provenance, do not double.
            target = conn.execute(
                "SELECT kill_id FROM kill_evidence WHERE kind='yaml_name' AND ref=?",
                (it["failed_strategy"],)).fetchone()
            if target:
                n_reused += 1
                iteration_reused = True
                component_ids.append(target[0])
                evidence.append((target[0], "verdict", rel_canon))
                if it.get("new_gap_name"):
                    aliases.append((target[0], it["new_gap_name"],
                                    f"gap named by verdict {name}"))

        if it and not iteration_reused:
            kid, already_materialized = choose_component_id(
                name, rel_canon, known_ids, "iteration", bool(verdict_kill)
            )
            component_ids.append(kid)
            if already_materialized:
                n_existing += 1
            else:
                known_ids[kid] = rel_canon
                n_iter += 1
                reason = " | ".join(filter(None, [
                    f"TARGET: {it.get('target')}" if it.get("target") else None,
                    f"FAILED: {it.get('failed_strategy')}" if it.get("failed_strategy") else None,
                    f"INVARIANT: {it.get('invariant_learned')}"
                    if it.get("invariant_learned") else None,
                ]))
                rows.append({
                    "id": kid, "unit_type": "strategy",
                    "subject": it.get("failed_strategy") or it.get("target") or name,
                    "status": "standing",
                    "reason": norm(reason), "scope_negation": None, "rollback_target": None,
                    "replacement": norm(it.get("next_decisive_test") or it.get("new_gap_name")),
                    "forbidden_future_move": norm(it.get("forbidden_future_move")),
                    "stop_code": it.get("progress_class") or it.get("status"),
                    "track": "RouteB", "recorded_at": date, "source_file": rel_canon,
                })
                for key in ("cognitive_operator_used", "new_gap_name", "invariant_learned",
                            "route_score", "next_decisive_test"):
                    if it.get(key):
                        evidence.append((kid, key, it[key][:500]))
            if it.get("new_gap_name"):
                aliases.append((kid, it["new_gap_name"], f"gap named by verdict {name}"))

        if verdict_kill:
            kid, already_materialized = choose_component_id(
                name, rel_canon, known_ids, "kill", bool(it)
            )
            component_ids.append(kid)
            if already_materialized:
                n_existing += 1
            else:
                known_ids[kid] = rel_canon
                n_kill += 1
                headline = re.search(r"^#\s+(.+)$", text, re.M)
                rows.append({
                    "id": kid, "unit_type": "object" if killed_subject else "route",
                    "subject": killed_subject or (norm(headline.group(1)) if headline else name),
                    "status": "killed", "reason": f"verdict marker: {verdict_kill}",
                    "scope_negation": (
                        "Execution KILL of this exact verdict subject and source scope only; "
                        "it does not imply MATHEMATICALLY_DEAD and does not close a weaker "
                        "consumer-sufficient interface."
                    ),
                    "rollback_target": None, "replacement": None,
                    "forbidden_future_move": None, "stop_code": verdict_kill,
                    "track": "RouteB", "recorded_at": date, "source_file": rel_canon,
                })

        for kid in dict.fromkeys(component_ids):
            for p in paths:
                evidence.append((kid, "verdict_copy", str(p.relative_to(REPO))))

    print(f"distinct verdicts scanned : {len(by_name)}")
    print(f"  new strategy rows (M3)  : {n_iter}")
    print(f"  new verdict-kill rows   : {n_kill}")
    print(f"  reused existing strategy: {n_reused} (evidence attached, no duplicate row)")
    print(f"  reused existing verdict : {n_existing} (stable id, no __V row)")
    print(f"  evidence refs           : {len(evidence)}   aliases: {len(aliases)}")
    print(f"  supplier-ledger rows (W9): {len(ledger_rows)} CLOSES/OPENS → capability")
    print(f"  prose-only KILL mentions: {len(manual)} — NOT migrated, need a human read:")
    # Урезание печатается вслух. Молчаливый срез читается как полный список: 2026-08-13
    # холостой прогон заявил 9 новых строк и напечатал 6, и пропущенной сочли ту запись,
    # которая на деле мигрировала. Отчёт, который отвечает уже, чем читается, — дефект.
    for n, pth in manual[:(len(manual) if args.list_manual else 12)]:
        print(f"      · {n[:64]}")
    if len(manual) > 12 and not args.list_manual:
        print(f"      … и ещё {len(manual) - 12}; полный список: --list-manual")
    if args.dry_run:
        limit = len(rows) if args.full else 6
        for r in rows[:limit]:
            print(f"   · [{r['unit_type']}] {r['id'][:52]:52s} {(r['subject'] or '')[:60]}")
        if limit < len(rows):
            print(f"   … и ещё {len(rows) - limit} строк не показано — повторить с --full")
        return 0

    removed_evidence, removed_kills = reconcile_projection(conn, live_names)
    print(f"  removed derived/stale evidence: {removed_evidence}")
    print(f"  removed source-orphan rows    : {removed_kills}")

    kb.insert_kills(conn, rows, evidence=evidence, aliases=aliases)
    if ledger_rows:
        conn.executemany(
            "INSERT INTO capability (theorem, file, lens, provides, requires, strength, run_id) "
            "VALUES (:theorem, :file, :lens, :provides, :requires, :strength, :run_id)",
            ledger_rows)
    conn.executemany(
        "INSERT OR REPLACE INTO source_ledger (source_file, expected_rows, migrated_at, note) "
        "VALUES (?,?,?,?)",
        # count per file, not a hard 1: a verdict that carries both an M3 strategy
        # row and a verdict-kill row contributes two, and a hard 1 made the census
        # report every such file as DRIFT.
        [(src, n, datetime.date.today().isoformat(), "wave 3 verdicts")
         for src, n in collections.Counter(r["source_file"] for r in rows).items()])
    conn.commit()
    backfilled = kb.backfill_operational_scope_negations(conn)
    print(f"backfilled legacy operational scope negations: {backfilled}")
    print("migrated into", kb.DB_PATH)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
