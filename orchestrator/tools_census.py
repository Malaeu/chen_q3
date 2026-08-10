#!/usr/bin/env python3
"""Machine census of every tool, database and state file in the repo.

Motivation (2026-08-05): twice in one session we nearly rebuilt something that already
existed (`Gammaℝ` in Mathlib, `riemannXi_eq_completedRiemannZeta` in the project), and the
existing discovery instrument `aristotle_db/aristotle_proofs.db` covered only 31% of RouteB.
A hand-written tool map would rot the same way, so this map is GENERATED instead.

Classification (formal, no judgement calls):
  PROBE  — lives inside a goal folder (ACTIVE/requests, docs/routeB_bus check_NNN, ...) or is
           named like a one-shot (`*_probe.py`, `check_NNN_*`, `validate_*`, `*_falsifier*`).
           These are an experiment log, not tooling: they are listed but not mapped.
  TOOL   — everything else that is executable: the permanent instrument set.
  TEST   — executable verification plant; not a user-facing instrument.
  MIGRATION — completed one-shot database migration; retained for provenance.
  DB     — sqlite databases.
  STATE  — json/yaml/csv state files above 2 KB.

Usage:
  ./orchestrator/tools_census.py                 # TSV inventory to stdout, summary to stderr
  ./orchestrator/tools_census.py --markdown      # regenerate docs/TOOLS.md
"""

import os
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

import yaml

REPO = Path(__file__).resolve().parent.parent
SKIP_DIRS = {
    ".git", ".lake", "node_modules", "__pycache__", ".venv", "venv", "venv_djo",
    ".mypy_cache", ".pytest_cache", "zotero", "literature", ".qmd_cache", "_backups",
    "aristotle_output",
}
SKIP_FILE = re.compile(r"BrangeHeatCert|PrimePowAuto")           # generated Lean certificates
PROBE_PATH = re.compile(r"ACTIVE/requests|archive|sandbox|research_swarm|full/")
PROBE_NAME = re.compile(r"_probe\.py$|^probe_|^check_\d|^validate_|falsifier|_plants?\.py$")
TEST_PATH = re.compile(r"(^|/)tests?/|(^|/)test_[^/]+\.py$")
MIGRATION_NAME = re.compile(r"(^|/)(?:kb_)?migrate_[^/]+\.py$|(^|/)kb_migrate_[^/]+\.py$")
ROUTEB_SCRIPT_PATH = re.compile(r"docs/routeB_bus/(?:phase\d+_scripts|check_[^/]+)/")
RULE_FILES = ["AGENTS.md", "docs/CODEX_CONTROL.md", "docs/SYSTEM_SPEC_2026-08-05.md",
              "docs/cartographer/TOOLS.yaml", "q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md",
              "q3.lean.aristotle/PROJECT_ORCHESTRATOR.md"]

TOOL_EXT = {".py", ".sh"}
DB_EXT = {".db", ".sqlite", ".sqlite3"}
STATE_EXT = {".json", ".yaml", ".yml", ".tsv", ".csv"}
ALIVE_SINCE = "2026-07-01"

# A LEDGER is any accumulating journal, regardless of format: the thing you consult to ask
# "have we already tried / solved / killed this?".  Owner correction 2026-08-05: the first
# version of this census counted only .db files as databases, so INSIGHTS.md (1802 dated
# entries), FAILURE_ATLAS.json and ROUTE_KILL_REGISTRY.md were invisible.
LEDGER_EXT = {".md", ".json", ".yaml", ".yml", ".csv"}
LEDGER_NAME = re.compile(
    r"INSIGHTS|ATLAS|REGISTRY|LEDGER|_LOG|LOG_|FAILED|FAILURE|MANIFEST|CHANGELOG|"
    r"MONITOR|PROTOKOLL|KILL|ERRORS_DESTROYER|SPINE|CHECKPOINTS|Progress_Log", re.I)
# Bus goal/answer cards are records, not journals — they are indexed by MANIFEST instead.
LEDGER_SKIP = re.compile(r"\.goal\.md$|\.answer\.md$|\.report\.md$|/litreview/|/insights/")
ENTRY_PATTERNS = [
    re.compile(r"^#{1,4}\s*\d{4}-\d{2}-\d{2}", re.M),      # ## 2026-08-05 — ...
    re.compile(r"^#{1,4}\s*.*\(\d{4}-\d{2}-\d{2}", re.M),  # ## Synthesis (2026-08-05, ...)
    re.compile(r"^\s*[-*]\s*\d{4}-\d{2}-\d{2}", re.M),     # - 2026-08-05 ...
    re.compile(r'^\s*"?date"?\s*[:=]', re.M),              # date: / "date":
    re.compile(r"^\s*\|\s*\d{4}-\d{2}-\d{2}", re.M),       # | 2026-08-05 | table rows
]
# Atlases and kill registries are tables WITHOUT dates, so the dated patterns miss them.
# Table rows only count for files that are NAMED as a journal — otherwise every ordinary doc
# containing a table would be misread as a ledger (that mistake gave 438 false ledgers).
TABLE_ROW = re.compile(r"^\s*\|(?![\s:-]*\|[\s:-]*$).+\|\s*$", re.M)
# Last resort for a file that is NAMED as a journal but holds neither dates nor tables:
# atlases are organised by headings (RH_TRICK_ATLAS: "## 3. Guth-Maynard ..."), and
# FAILURE_ATLAS.json / FAILED_STRATEGIES.yaml by array records.
NAMED_FALLBACK = [
    re.compile(r"^#{2,4}\s+\S", re.M),                 # ## card / ## obstruction
    re.compile(r"^\s*[-*]\s+\S", re.M),                # - record
    re.compile(r'^\s{0,6}"[\w_]+"\s*:', re.M),          # "id": ...   (json)
    re.compile(r"^\s{0,4}[\w_]+:\s", re.M),            # id: ...     (yaml)
]
MIN_ENTRIES = 8
MAX_LEDGER_BYTES = 20 * 1024 * 1024


def walk():
    for root, dirs, files in os.walk(REPO):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for f in files:
            if not SKIP_FILE.search(f):
                yield Path(root) / f


def git_last(rel):
    # A symlink carries the commit date of the link itself; date the target instead.
    p = REPO / rel
    if p.is_symlink():
        try:
            rel = p.resolve().relative_to(REPO)
        except Exception:
            pass
    try:
        out = subprocess.run(["git", "log", "-1", "--format=%ad", "--date=short", "--", str(rel)],
                             cwd=REPO, capture_output=True, text=True, timeout=20).stdout.strip()
        return out or "untracked"
    except Exception:
        return "error"


def purpose(path):
    """First docstring / header comment line — what the tool claims to do."""
    try:
        txt = path.read_text(errors="ignore")[:1200]
    except Exception:
        return ""
    m = re.search(r'"""(.+?)(?:\n|""")', txt, re.S)
    if m:
        return " ".join(m.group(1).split())[:110]
    for line in txt.splitlines():
        s = line.strip()
        if s.startswith("#") and not s.startswith("#!") and len(s) > 3:
            return s.lstrip("# ").strip()[:110]
    return ""


def classify(rel):
    text = str(rel)
    if TEST_PATH.search(text):
        return "TEST"
    if MIGRATION_NAME.search(text):
        return "MIGRATION"
    if PROBE_PATH.search(text) or ROUTEB_SCRIPT_PATH.search(text) or PROBE_NAME.search(rel.name):
        return "PROBE"
    return "TOOL"


def count_entries(path):
    """How many appended records does this journal hold? 0 means 'not a journal'."""
    try:
        if path.stat().st_size > MAX_LEDGER_BYTES:
            return 0
        txt = path.read_text(errors="ignore")
    except Exception:
        return 0
    return max(len(pat.findall(txt)) for pat in ENTRY_PATTERNS)


def is_ledger(rel, path):
    if LEDGER_SKIP.search(str(rel)):
        return 0
    n = count_entries(path)
    if LEDGER_NAME.search(rel.name):
        if n < 2:                       # named like a journal: table rows also count
            try:
                txt = path.read_text(errors="ignore")
                n = max([len(TABLE_ROW.findall(txt)) - 1]
                        + [len(pat.findall(txt)) for pat in NAMED_FALLBACK])
            except Exception:
                n = 0
        return n if n >= 2 else 0
    return n if n >= MIN_ENTRIES else 0


def collect():
    tools, probes, tests, migrations, dbs, empty_dbs, states, ledgers = [], [], [], [], [], [], [], []
    for p in walk():
        rel = p.relative_to(REPO)
        ext = p.suffix.lower()
        if ext in TOOL_EXT:
            kind = classify(rel)
            {"PROBE": probes, "TEST": tests, "MIGRATION": migrations, "TOOL": tools}[kind].append(rel)
            continue
        if ext in DB_EXT:
            (empty_dbs if p.stat().st_size == 0 else dbs).append(rel)
            continue
        if ext in LEDGER_EXT:
            n = is_ledger(rel, p)
            if n:
                ledgers.append((rel, n))
                continue
        if ext in STATE_EXT and p.stat().st_size > 2000:
            states.append(rel)
    return tools, probes, tests, migrations, dbs, empty_dbs, states, ledgers


def reference_counts(names):
    refs = Counter()
    if not names:
        return refs
    pat = "|".join(re.escape(n) for n in names)
    try:
        # Exclude our own generated output: docs/TOOLS.md lists every tool by name, so
        # counting it would give each tool a phantom reference and erase the orphan signal.
        out = subprocess.run(["rg", "--no-filename", "-o", "-e", pat,
                              "--glob", "!.git", "--glob", "!.lake", "--glob", "!*.olean",
                              "--glob", "!docs/TOOLS.md",
                              "--glob", "!CLAUDE.md", "--glob", "!**/CLAUDE.md",
                              "--glob", "!.claude/**", "--glob", "!**/tests/**",
                              "--glob", "!test_*.py",
                              str(REPO)], capture_output=True, text=True, timeout=600).stdout
        for line in out.splitlines():
            refs[line.strip()] += 1
    except Exception as e:
        print(f"[warn] reference scan failed: {e}", file=sys.stderr)
    return refs


def rule_mentions():
    blob = ""
    for f in RULE_FILES:
        p = REPO / f
        if p.exists():
            blob += p.read_text(errors="ignore")
    return blob


def build_rows():
    tools, probes, tests, migrations, dbs, empty_dbs, states, ledgers = collect()
    refs = reference_counts([p.name for p in tools + dbs])
    rules = rule_mentions()
    rows = []
    for rel in sorted(tools):
        p = REPO / rel
        rows.append({
            "kind": "TOOL", "path": str(rel), "last": git_last(rel),
            "refs": max(refs.get(rel.name, 0) - 1, 0),
            "in_rules": rel.name in rules,
            "purpose": purpose(p),
        })
    for rel in sorted(dbs):
        rows.append({
            "kind": "DB", "path": str(rel), "last": git_last(rel),
            "refs": max(refs.get(rel.name, 0) - 1, 0),
            "in_rules": rel.name in rules, "purpose": "",
        })
    for rel, n in sorted(ledgers, key=lambda x: -x[1]):
        rows.append({
            "kind": "LEDGER", "path": str(rel), "last": git_last(rel),
            "refs": n,                      # for ledgers this column holds the entry count
            "in_rules": rel.name in rules, "purpose": "",
        })
    return rows, probes, tests, migrations, empty_dbs, states


def manifest_summary():
    path = REPO / "docs" / "cartographer" / "TOOLS.yaml"
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    families = data.get("tool_families", {})
    tools = [tool for family in families.values() for tool in family.get("tools", [])]
    status = Counter(tool.get("status", "UNKNOWN") for tool in tools)
    front_doors = [family.get("front_door", "UNDECLARED") for family in families.values()]
    return len(families), len(tools), status, front_doors


def markdown(rows, probes, tests, migrations, empty_dbs, states):
    tools = [r for r in rows if r["kind"] == "TOOL"]
    dbs = [r for r in rows if r["kind"] == "DB"]
    alive = [r for r in tools if r["last"] >= ALIVE_SINCE]
    orphans = [r for r in alive if r["refs"] == 0]
    family_count, entry_count, manifest_status, front_doors = manifest_summary()

    out = []
    out.append("# TOOLS.md — generated map of the repo's instruments\n")
    out.append("> **GENERATED FILE — do not edit by hand.** Regenerate with "
               "`./orchestrator/tools_census.py --markdown`.\n")
    out.append("> Written because hand-maintained maps rot: MAP.md drifted two days, the "
               "frozen atlases two months, and `aristotle_proofs.db` covered 31% of RouteB.\n")
    out.append("## Summary\n")
    out.append(f"- **Operational contours:** {family_count}; registered tool contracts: {entry_count} "
               f"({', '.join(f'{k} {v}' for k, v in sorted(manifest_status.items()))})")
    out.append(f"- **Contour front doors:** {', '.join(f'`{door}`' for door in front_doors)}")
    out.append("- **Automatic startup front doors:** 1 (`codex-session-start`); Spine strict is its internal check")
    out.append(f"- **Executable implementation files:** {len(tools)} (touched since {ALIVE_SINCE}: {len(alive)})")
    out.append(f"- **One-shot probes** (goal-local experiment log, not tooling): {len(probes)}")
    out.append(f"- **Verification tests** (not tooling): {len(tests)}")
    out.append(f"- **Completed migration scripts** (provenance, not tooling): {len(migrations)}")
    out.append(f"- **Databases:** {len(dbs)}")
    out.append(f"- **Zero-byte database decoys:** {len(empty_dbs)}")
    out.append(f"- **Ledgers** (accumulating journals, any format): "
               f"{sum(1 for r in rows if r['kind']=='LEDGER')}")
    out.append(f"- **State files** (json/yaml/csv > 2 KB, not journals): {len(states)}")
    out.append(f"- Alive tools referenced by nothing (**orphans**): {len(orphans)}")
    out.append("- `In rules` below means a direct policy/startup mention; implementation helpers may be covered by a registered family.\n")

    out.append("## Databases\n")
    out.append("| Path | Last commit | Refs | In rules |")
    out.append("|---|---|---|---|")
    for r in dbs:
        out.append(f"| `{r['path']}` | {r['last']} | {r['refs']} | {'yes' if r['in_rules'] else 'NO'} |")
    out.append("")

    if empty_dbs:
        out.append("### Zero-byte decoys (not databases)\n")
        out.append("These files have no schema and no authority. Remove them; their canonical replacements are named in `TOOLS.yaml`.\n")
        for rel in sorted(empty_dbs):
            out.append(f"- `{rel}`")
        out.append("")

    ledgers = [r for r in rows if r["kind"] == "LEDGER"]
    led_alive = [r for r in ledgers if r["last"] >= ALIVE_SINCE]
    led_dead = [r for r in ledgers if r["last"] < ALIVE_SINCE]
    out.append("## Ledgers — accumulating journals (\"have we already tried this?\")\n")
    out.append(f"{len(ledgers)} journals, **{len(led_alive)} alive** / {len(led_dead)} frozen. "
               "A frozen ledger that is still cited as current is the project's recurring "
               "failure mode: it does not lie, it just stops answering.\n")
    out.append("### Alive\n")
    out.append("| Ledger | Entries | Last commit | In rules |")
    out.append("|---|---|---|---|")
    for r in sorted(led_alive, key=lambda x: -int(x["refs"])):
        out.append(f"| `{r['path']}` | {r['refs']} | {r['last']} | "
                   f"{'yes' if r['in_rules'] else '**NO**'} |")
    out.append("\n### Frozen (still on disk, often still cited)\n")
    out.append("| Ledger | Entries | Last commit |")
    out.append("|---|---|---|")
    # No silent truncation: a map that quietly drops rows reads as "this is everything".
    for r in sorted(led_dead, key=lambda x: x["last"], reverse=True):
        out.append(f"| `{r['path']}` | {r['refs']} | {r['last']} |")
    out.append("")

    out.append("## Permanent tools, most recently touched first\n")
    out.append("| Tool | Last | Refs | In rules | Purpose |")
    out.append("|---|---|---|---|---|")
    for r in sorted(tools, key=lambda x: x["last"], reverse=True):
        mark = "yes" if r["in_rules"] else "**NO**"
        out.append(f"| `{r['path']}` | {r['last']} | {r['refs']} | {mark} | {r['purpose']} |")
    out.append("")

    if orphans:
        out.append("## Orphans — alive but nothing references them\n")
        out.append("Either wire them into a contour or archive them; a tool nobody calls is a "
                   "tool nobody will find when it is needed.\n")
        for r in sorted(orphans, key=lambda x: x["last"], reverse=True):
            out.append(f"- `{r['path']}` (last {r['last']}) — {r['purpose']}")
        out.append("")

    out.append("## Note on probes\n")
    out.append(f"The {len(probes)} one-shot probes are deliberately **not** mapped here. They are "
               "goal-local evidence, not instruments; treating them as tooling is what makes the "
               "instrument set look unknowably large.\n")
    out.append(f"The {len(tests)} tests and {len(migrations)} completed migration scripts are likewise "
               "excluded from the operational instrument count.\n")
    return "\n".join(line.rstrip() for line in out) + "\n"


def main():
    if "-h" in sys.argv[1:] or "--help" in sys.argv[1:]:
        print(
            "usage: tools_census.py [--markdown]\n\n"
            "Without flags, print the TSV inventory. --markdown regenerates docs/TOOLS.md."
        )
        return 0
    unknown = [arg for arg in sys.argv[1:] if arg != "--markdown"]
    if unknown:
        print(f"unknown arguments: {' '.join(unknown)}", file=sys.stderr)
        return 2
    rows, probes, tests, migrations, empty_dbs, states = build_rows()
    if "--markdown" in sys.argv:
        target = REPO / "docs" / "TOOLS.md"
        target.write_text(markdown(rows, probes, tests, migrations, empty_dbs, states))
        print(f"wrote {target}")
        return 0
    print("KIND\tPATH\tLAST\tREFS\tIN_RULES\tPURPOSE")
    for r in rows:
        print(f"{r['kind']}\t{r['path']}\t{r['last']}\t{r['refs']}\t{r['in_rules']}\t{r['purpose']}")
    tools = [r for r in rows if r["kind"] == "TOOL"]
    alive = [r for r in tools if r["last"] >= ALIVE_SINCE]
    led = [r for r in rows if r['kind'] == 'LEDGER']
    print(f"\n== tools {len(tools)} (alive {len(alive)}) | probes {len(probes)} | "
          f"tests {len(tests)} | migrations {len(migrations)} | "
          f"dbs {sum(1 for r in rows if r['kind']=='DB')} | ledgers {len(led)} "
          f"(alive {sum(1 for r in led if r['last'] >= ALIVE_SINCE)}) | "
          f"empty_db_decoys {len(empty_dbs)} | states {len(states)}",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
