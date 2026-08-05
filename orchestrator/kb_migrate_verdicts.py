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
  * one row per distinct verdict NAME; every path it appears at is recorded as evidence,
    so the canon/mirror split is preserved without duplicating knowledge;
  * a strategy already migrated from FAILED_STRATEGIES.yaml is NOT re-inserted — the verdict
    becomes an evidence row and an alias on the existing record instead.
"""

import argparse
import collections
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
DATE_RE = re.compile(r"(20\d\d)-(\d\d)-(\d\d)")


def norm(t, limit=1200):
    return " ".join(t.split())[:limit] if t else None


def collect_files():
    files = [p for p in REPO.rglob("PROSHKA_*.md")
             if ".git" not in str(p) and p.name not in CONFIG_NAMES]
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


def parse_iteration(text):
    m = re.search(r"^iteration:\s*\n(.*?)(?=\n```|\n#{1,3} |\Z)", text, re.S | re.M)
    if not m:
        return None
    block = m.group(1)
    out = {}
    for fm in re.finditer(r"^\s{2,}(\w+):\s*(.+?)\s*$", block, re.M):
        out[fm.group(1)] = fm.group(2).strip()
    return out or None


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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    by_name = collect_files()
    conn = kb.connect()
    known_strategies = {r[0] for r in conn.execute(
        "SELECT ref FROM kill_evidence WHERE kind='yaml_name'")}
    known_ids = {r[0] for r in conn.execute("SELECT id FROM kill")}

    rows, evidence, aliases, links = [], [], [], []
    manual = []   # prose-only KILL mentions: reported, never invented into rows
    n_iter = n_kill = n_reused = 0

    for name, paths in sorted(by_name.items()):
        canon = paths[0]
        text = canon.read_text(errors="ignore")
        rel_canon = str(canon.relative_to(REPO))
        d = DATE_RE.search(name) or DATE_RE.search(text)
        date = f"{d.group(1)}-{d.group(2)}-{d.group(3)}" if d else None

        it = parse_iteration(text)
        verdict_kill, killed_subject = parse_verdict_kill(text)
        if not it and not verdict_kill:
            if re.search(r"\bKILL(ED)?\b|\bFATAL\b", text):
                manual.append((name, rel_canon))
            continue

        if it and it.get("failed_strategy") in known_strategies:
            # Already migrated from FAILED_STRATEGIES.yaml — attach provenance, do not double.
            target = conn.execute(
                "SELECT kill_id FROM kill_evidence WHERE kind='yaml_name' AND ref=?",
                (it["failed_strategy"],)).fetchone()
            if target:
                n_reused += 1
                evidence.append((target[0], "verdict", rel_canon))
                if it.get("new_gap_name"):
                    aliases.append((target[0], it["new_gap_name"],
                                    f"gap named by verdict {name}"))
                continue

        kid = kb.slugify(name.replace("PROSHKA_", "").replace(".md", ""), 60)
        if kid in known_ids:
            kid = f"{kid}__V"
        known_ids.add(kid)

        if it:
            n_iter += 1
            reason = " | ".join(filter(None, [
                f"TARGET: {it.get('target')}" if it.get("target") else None,
                f"FAILED: {it.get('failed_strategy')}" if it.get("failed_strategy") else None,
                f"INVARIANT: {it.get('invariant_learned')}" if it.get("invariant_learned") else None]))
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
        else:
            n_kill += 1
            headline = re.search(r"^#\s+(.+)$", text, re.M)
            rows.append({
                "id": kid, "unit_type": "object" if killed_subject else "route",
                "subject": killed_subject or (norm(headline.group(1)) if headline else name),
                "status": "killed", "reason": f"verdict marker: {verdict_kill}",
                "scope_negation": None, "rollback_target": None, "replacement": None,
                "forbidden_future_move": None, "stop_code": verdict_kill,
                "track": "RouteB", "recorded_at": date, "source_file": rel_canon,
            })

        for p in paths:
            evidence.append((kid, "verdict_copy", str(p.relative_to(REPO))))

    print(f"distinct verdicts scanned : {len(by_name)}")
    print(f"  new strategy rows (M3)  : {n_iter}")
    print(f"  new verdict-kill rows   : {n_kill}")
    print(f"  reused existing strategy: {n_reused} (evidence attached, no duplicate row)")
    print(f"  evidence refs           : {len(evidence)}   aliases: {len(aliases)}")
    print(f"  prose-only KILL mentions: {len(manual)} — NOT migrated, need a human read:")
    for n, pth in manual[:12]:
        print(f"      · {n[:64]}")
    if args.dry_run:
        for r in rows[:6]:
            print(f"   · [{r['unit_type']}] {r['id'][:52]:52s} {(r['subject'] or '')[:60]}")
        return 0

    kb.insert_kills(conn, rows, evidence=evidence, aliases=aliases)
    conn.executemany(
        "INSERT OR REPLACE INTO source_ledger (source_file, expected_rows, migrated_at, note) "
        "VALUES (?,?,?,?)",
        [(r["source_file"], 1, "2026-08-05", "wave 3 verdicts") for r in rows])
    conn.commit()
    print("migrated into", kb.DB_PATH)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
