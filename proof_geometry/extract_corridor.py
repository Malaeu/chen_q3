#!/usr/bin/env python3
"""Extract the Goal 056/057 corridor into a directed AND-factor graph.

Target: Q3_PROOF_GEOMETRY_V0_BACKTEST. Read-only over project state; writes
only corridor_057.json next to itself.

Every structural fact is mechanical:
  - node list          <- docs/routeB_bus/GOAL057_B3_0*_CLOSEOUT_*.md filenames
  - node -> Lean file  <- "## Production object" section of each closeout
  - AND inputs         <- `import Q3....` lines of the production Lean file
  - chronology         <- git log Prove/Close commits mentioning `B3.0<node>`
  - killed branches    <- knowledge.db kill rows VERDICT_GOAL056_*
  - plant              <- synthetic, labelled, per directive

No field of this extraction encodes "which node was historically next"; the
chronology list is stored separately and consumed only by the backtest
evaluator as held-out truth.
"""

from __future__ import annotations

import json
import re
import sqlite3
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
BUS = REPO / "docs" / "routeB_bus"
LEAN_ROOT = REPO / "q3.lean.aristotle"
KNOWLEDGE_DB = LEAN_ROOT / "aristotle_db" / "knowledge.db"
OUT = Path(__file__).resolve().parent / "corridor_057.json"

CLOSEOUT_RE = re.compile(r"^GOAL057_B3_0([A-Z][A-Z0-9]*)_.*_CLOSEOUT_")
IMPORT_RE = re.compile(r"^import\s+(Q3[\w.]+)", re.M)
PROD_HEAD_RE = re.compile(r"^## Production (?:object|artifact)\s*$", re.M)
LEAN_PATH_RE = re.compile(r"`([^`]+\.lean)`")


def production_path(text: str, name: str) -> str:
    m = PROD_HEAD_RE.search(text)
    if not m:
        raise SystemExit(f"no production section in {name}")
    section = text[m.end():]
    nxt = section.find("\n## ")
    if nxt != -1:
        section = section[:nxt]
    pm = LEAN_PATH_RE.search(section)
    if not pm:
        raise SystemExit(f"no production object in {name}")
    return pm.group(1)


def git_log() -> list[tuple[str, str, str]]:
    out = subprocess.run(
        ["git", "log", "--reverse", "--format=%h|%cI|%s"],
        cwd=REPO, capture_output=True, text=True, check=True,
    ).stdout
    rows = []
    for line in out.splitlines():
        h, t, s = line.split("|", 2)
        rows.append((h, t, s))
    return rows


def module_to_path(module: str) -> str:
    return "q3.lean.aristotle/" + module.replace(".", "/") + ".lean"


def main() -> None:
    # 1. Corridor children from closeout files.
    children: dict[str, dict] = {}
    for f in sorted(BUS.glob("GOAL057_B3_0*_CLOSEOUT_*.md")):
        m = CLOSEOUT_RE.match(f.name)
        if not m:
            continue
        node = m.group(1)
        text = f.read_text(encoding="utf-8")
        children[node] = {
            "id": node,
            "kind": "theorem",
            "closeout": str(f.relative_to(REPO)),
            "lean_file": production_path(text, f.name),
            "status": "LEAN_PROVED",
            "scope": "FINITE_CELL",
            "verifier": "LEAN",
        }

    # 2. Chronology: last Prove/Close commit that names `B3.0<node>`.
    log = git_log()
    for node, rec in children.items():
        pat = re.compile(rf"\bB3\.0{re.escape(node)}\b")
        hits = [
            (h, t, s) for (h, t, s) in log
            if "Goal 057" in s and pat.search(s)
            and re.search(r"\]\s*(Prove|Close) ", s)
        ]
        if not hits:
            raise SystemExit(f"no Prove/Close commit found for node {node}")
        h, t, s = hits[-1]
        rec["close_commit"] = h
        rec["close_time"] = t
        rec["close_subject"] = s

    order = sorted(children.values(), key=lambda r: r["close_time"])
    for i, rec in enumerate(order):
        rec["close_index"] = i

    # 3. AND inputs from Lean imports.
    path_to_node = {rec["lean_file"]: rec["id"] for rec in children.values()}
    hyperedges: list[dict] = []
    consumed: set[str] = set()
    for rec in order:
        lf = REPO / rec["lean_file"]
        if not lf.is_file():
            raise SystemExit(f"production file missing on disk: {rec['lean_file']}")
        modules = IMPORT_RE.findall(lf.read_text(encoding="utf-8"))
        intra, corpus = [], []
        for mod in modules:
            p = module_to_path(mod)
            if p in path_to_node and path_to_node[p] != rec["id"]:
                intra.append(path_to_node[p])
            else:
                corpus.append(mod)
        consumed.update(intra)
        hyperedges.append({
            "id": f"INF_{rec['id']}",
            "inputs": sorted(set(intra)) + (["CORPUS"] if corpus or not intra else []),
            "output": rec["id"],
            "corpus_imports": corpus,
            "verifier": "LEAN",
            "killed": False,
            "risk_flags": [],
            "unverified_imports": 0,
            "cost": 1.0,
        })

    # 4. Roof: parent target consumes the sink children (AND).
    sinks = sorted(set(children) - consumed)
    hyperedges.append({
        "id": "INF_ROOF",
        "inputs": sinks,
        "output": "B3_0_TARGET",
        "corpus_imports": [],
        "verifier": "PLANNED",
        "killed": False,
        "risk_flags": [],
        "unverified_imports": 0,
        "cost": 1.0,
    })

    # 5. Killed Goal-056 branches from knowledge.db.
    kills: list[dict] = []
    con = sqlite3.connect(f"file:{KNOWLEDGE_DB}?mode=ro", uri=True)
    rows = con.execute(
        "SELECT id, subject, reason, recorded_at, source_file FROM kill "
        "WHERE id LIKE 'VERDICT_GOAL056%' ORDER BY id"
    ).fetchall()
    con.close()
    for kid, subject, reason, recorded_at, source_file in rows:
        node_id = f"KILL_{kid}"
        kills.append({
            "id": node_id,
            "kind": "theorem",
            "status": "KILLED",
            "scope": "ABSTRACT",
            "verifier": "KILLED",
            "kill_subject": subject,
            "kill_reason": (reason or "")[:400],
            "kill_recorded_at": recorded_at,
            "source_file": source_file,
        })
        hyperedges.append({
            "id": f"INF_{node_id}_SUPPLY",
            "inputs": ["CORPUS"],
            "output": node_id,
            "corpus_imports": [],
            "verifier": "KILLED",
            "killed": True,
            "risk_flags": ["killed_branch"],
            "unverified_imports": 0,
            "cost": 1.0,
        })
        hyperedges.append({
            "id": f"INF_{node_id}_BRIDGE",
            "inputs": [node_id],
            "output": "B3_0_TARGET",
            "corpus_imports": [],
            "verifier": "KILLED",
            "killed": True,
            "risk_flags": ["killed_branch"],
            "unverified_imports": 0,
            "cost": 1.0,
        })

    # 6. Plant: short fake path through a wrong-object conditional edge.
    plant = {
        "id": "PLANT_FAKE_SHORTCUT",
        "kind": "theorem",
        "status": "OPEN",
        "scope": "ABSTRACT",
        "verifier": "CONDITIONAL",
        "synthetic_plant": True,
    }
    hyperedges.append({
        "id": "INF_PLANT_SUPPLY",
        "inputs": ["CORPUS"],
        "output": "PLANT_FAKE_SHORTCUT",
        "corpus_imports": [],
        "verifier": "CONDITIONAL",
        "killed": False,
        "risk_flags": ["wrong_object"],
        "unverified_imports": 1,
        "cost": 1.0,
        "synthetic_plant": True,
    })
    hyperedges.append({
        "id": "INF_PLANT_BRIDGE",
        "inputs": ["PLANT_FAKE_SHORTCUT"],
        "output": "B3_0_TARGET",
        "corpus_imports": [],
        "verifier": "CONDITIONAL",
        "killed": False,
        "risk_flags": ["wrong_object"],
        "unverified_imports": 1,
        "cost": 1.0,
        "synthetic_plant": True,
    })

    # 7. Checkpoints (held-out truth, consumed only by the evaluator).
    wall = next(
        (h, t, s) for (h, t, s) in git_log()
        if "Record Goal 057 B3.0 release wall" in s
    )
    checkpoints = [{
        "index": 0,
        "after": None,
        "time": wall[1],
        "historical_next": order[0]["id"],
    }]
    for i in range(len(order) - 1):
        checkpoints.append({
            "index": i + 1,
            "after": order[i]["id"],
            "time": order[i]["close_time"],
            "historical_next": order[i + 1]["id"],
        })

    payload = {
        "schema": "Q3_PROOF_GEOMETRY_CORRIDOR_V0",
        "corridor": "GOAL056_S2_WALL__GOAL057_B3_0_LADDER",
        "target": "B3_0_TARGET",
        "corpus": "CORPUS",
        "nodes": (
            [{"id": "CORPUS", "kind": "corpus", "status": "LEAN_PROVED",
              "verifier": "LEAN"},
             {"id": "B3_0_TARGET", "kind": "goal", "status": "OPEN",
              "verifier": "PLANNED"}]
            + order + kills + [plant]
        ),
        "hyperedges": hyperedges,
        "checkpoints": checkpoints,
        "sink_children": sinks,
        "provenance": {
            "closeouts": len(children),
            "kill_rows": len(kills),
            "wall_commit": wall[0],
            "note": "structure from Lean imports + closeouts + knowledge.db; "
                    "chronology from git; plant synthetic per directive",
        },
    }
    OUT.write_text(json.dumps(payload, indent=2, ensure_ascii=False),
                   encoding="utf-8")
    print(f"wrote {OUT.relative_to(REPO)}: "
          f"{len(payload['nodes'])} nodes, {len(hyperedges)} hyperedges, "
          f"{len(checkpoints)} checkpoints, sinks={sinks}")


if __name__ == "__main__":
    main()
