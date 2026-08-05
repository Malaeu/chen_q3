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

REPO = Path(__file__).resolve().parent.parent
SKIP_DIRS = {".git", ".lake", "node_modules", "__pycache__", ".venv", "zotero",
             "literature", ".qmd_cache", "_backups"}
SKIP_FILE = re.compile(r"BrangeHeatCert|PrimePowAuto")           # generated Lean certificates
PROBE_PATH = re.compile(r"ACTIVE/requests|archive|sandbox|research_swarm|full/")
PROBE_NAME = re.compile(r"_probe\.py$|^probe_|^check_\d|^validate_|falsifier|_plants?\.py$")
RULE_FILES = ["CLAUDE.md", "AGENTS.md", "docs/SYSTEM_SPEC_2026-08-05.md",
              "q3.lean.aristotle/PROJECT_ORCHESTRATOR.md", "orchestrator/CONDUCTOR.md"]

TOOL_EXT = {".py", ".sh"}
DB_EXT = {".db", ".sqlite", ".sqlite3"}
STATE_EXT = {".json", ".yaml", ".yml", ".tsv", ".csv"}
ALIVE_SINCE = "2026-07-01"


def walk():
    for root, dirs, files in os.walk(REPO):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for f in files:
            if not SKIP_FILE.search(f):
                yield Path(root) / f


def git_last(rel):
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
    if PROBE_PATH.search(str(rel)) or PROBE_NAME.search(rel.name):
        return "PROBE"
    return "TOOL"


def collect():
    tools, probes, dbs, states = [], [], [], []
    for p in walk():
        rel = p.relative_to(REPO)
        ext = p.suffix.lower()
        if ext in TOOL_EXT:
            (probes if classify(rel) == "PROBE" else tools).append(rel)
        elif ext in DB_EXT:
            dbs.append(rel)
        elif ext in STATE_EXT and p.stat().st_size > 2000:
            states.append(rel)
    return tools, probes, dbs, states


def reference_counts(names):
    refs = Counter()
    if not names:
        return refs
    pat = "|".join(re.escape(n) for n in names)
    try:
        out = subprocess.run(["rg", "--no-filename", "-o", "-e", pat,
                              "--glob", "!.git", "--glob", "!.lake", "--glob", "!*.olean",
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
    tools, probes, dbs, states = collect()
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
    return rows, probes, states


def markdown(rows, probes, states):
    tools = [r for r in rows if r["kind"] == "TOOL"]
    dbs = [r for r in rows if r["kind"] == "DB"]
    alive = [r for r in tools if r["last"] >= ALIVE_SINCE]
    orphans = [r for r in alive if r["refs"] == 0]
    unruled = [r for r in alive if not r["in_rules"]]

    out = []
    out.append("# TOOLS.md — generated map of the repo's instruments\n")
    out.append("> **GENERATED FILE — do not edit by hand.** Regenerate with "
               "`./orchestrator/tools_census.py --markdown`.\n")
    out.append("> Written because hand-maintained maps rot: MAP.md drifted two days, the "
               "frozen atlases two months, and `aristotle_proofs.db` covered 31% of RouteB.\n")
    out.append("## Summary\n")
    out.append(f"- **Permanent tools:** {len(tools)} (touched since {ALIVE_SINCE}: {len(alive)})")
    out.append(f"- **One-shot probes** (goal-local experiment log, not tooling): {len(probes)}")
    out.append(f"- **Databases:** {len(dbs)}")
    out.append(f"- **State files** (json/yaml/csv > 2 KB): {len(states)}")
    out.append(f"- Alive tools referenced by nothing (**orphans**): {len(orphans)}")
    out.append(f"- Alive tools not mentioned in any rule file: {len(unruled)}\n")

    out.append("## Databases\n")
    out.append("| Path | Last commit | Refs | In rules |")
    out.append("|---|---|---|---|")
    for r in dbs:
        out.append(f"| `{r['path']}` | {r['last']} | {r['refs']} | {'yes' if r['in_rules'] else 'NO'} |")
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
    return "\n".join(out) + "\n"


def main():
    rows, probes, states = build_rows()
    if "--markdown" in sys.argv:
        target = REPO / "docs" / "TOOLS.md"
        target.write_text(markdown(rows, probes, states))
        print(f"wrote {target}")
        return 0
    print("KIND\tPATH\tLAST\tREFS\tIN_RULES\tPURPOSE")
    for r in rows:
        print(f"{r['kind']}\t{r['path']}\t{r['last']}\t{r['refs']}\t{r['in_rules']}\t{r['purpose']}")
    tools = [r for r in rows if r["kind"] == "TOOL"]
    alive = [r for r in tools if r["last"] >= ALIVE_SINCE]
    print(f"\n== tools {len(tools)} (alive {len(alive)}) | probes {len(probes)} | "
          f"dbs {sum(1 for r in rows if r['kind']=='DB')} | states {len(states)}",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
