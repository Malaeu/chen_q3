#!/usr/bin/env python3
"""Dirichlet potential probe over the explored proof state. Read-only, advisory-only.

Instantiates the maze/heat-equation prioritization idea on the only layer where
it is currently well-posed: the Lean import DAG of a proof root. Boundary
conditions: the open project axioms are the hot absorbing "doors", the fully
proved Mathlib/std floor is the cold absorbing ground. The potential
u_D(v) = P(a uniform random descent along dependencies from v is absorbed at
door D) is harmonic on interior nodes, and temperature(v) = sum_D u_D(v) is the
probability that a descent from v hits any open assumption at all.

The second layer (goal/route graph: kills, walls, fronts) is where the idea
would actually earn money, and this tool measures whether that layer is
machine-readable enough to pose the same Dirichlet problem there. Today it is
not; the tool prints the exact missing structure instead of faking edges.

ADVISORY_ONLY: every number printed here is a prioritization signal over the
already-explored graph. It is not proof evidence, not a route selection, and
must never be cited as support for a mathematical claim (CODEX_CONTROL §13).
"""

from __future__ import annotations

import argparse
import json
import sqlite3
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
GRAPHS = REPO / "q3.lean.aristotle" / "ACTIVE" / "graphs"
KNOWLEDGE_DB = REPO / "q3.lean.aristotle" / "aristotle_db" / "knowledge.db"

ROOT_ALIASES = {
    "main": "Q3.Main.RH_of_Weil_and_Q3",
    "atom": "Q3.RH_of_shifted_atom_route",
}


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


# ── Layer 1: Lean import DAG ─────────────────────────────────────────────────

def lean_layer(root_key: str, graphs_dir: Path) -> dict:
    taint = load_json(graphs_dir / "TAINT_GRAPH.json")
    deps_tree = load_json(graphs_dir / "DEPS_TREE_MAIN.json")

    root_id = ROOT_ALIASES.get(root_key, root_key)
    status = next((r for r in taint["root_status"] if r["root_id"] == root_id), None)
    if status is None:
        raise SystemExit(f"root {root_id!r} not present in TAINT_GRAPH root_status")
    entry = status["entry_file"]

    nodes = {n["id"]: n for n in taint["nodes"] if root_id in n["root_ids"]}
    if entry not in nodes:
        raise SystemExit(f"entry file {entry!r} missing from closure nodes")

    root_deps = next((r for r in deps_tree["roots"] if r["id"] == root_id), None)
    if root_deps is None:
        raise SystemExit(f"root {root_id!r} not present in DEPS_TREE_MAIN roots")
    doors: dict[str, list[str]] = {}
    for dep in root_deps["deps"]:
        if dep["classification"] == "PROJECT_AXIOM" and dep.get("file"):
            doors.setdefault(dep["file"], []).append(dep["name"])

    # u[v][door_file] via memoized descent on the DAG; absorption on arrival at
    # a door file, ground absorption at files with no in-closure dependencies.
    memo: dict[str, dict[str, float]] = {}

    def solve(v: str) -> dict[str, float]:
        if v in memo:
            return memo[v]
        if v in doors:
            memo[v] = {v: 1.0}
            return memo[v]
        outs = [d for d in nodes[v]["dependencies"] if d in nodes]
        acc: dict[str, float] = {}
        if outs:
            w = 1.0 / len(outs)
            for d in outs:
                for door, p in solve(d).items():
                    acc[door] = acc.get(door, 0.0) + w * p
        memo[v] = acc
        return acc

    for v in nodes:
        solve(v)

    temperature = {v: sum(memo[v].values()) for v in nodes}
    hot = sorted(
        ((t, v) for v, t in temperature.items() if v not in doors and t > 0),
        reverse=True,
    )
    return {
        "root_id": root_id,
        "entry_file": entry,
        "closure_size": len(nodes),
        "tainted_files": status["tainted_files"],
        "doors": {f: names for f, names in doors.items()},
        "entry_exposure": temperature[entry],
        "entry_door_split": memo[entry],
        "ground_mass": 1.0 - temperature[entry],
        "hottest_files": [(v, t) for t, v in hot[:12]],
    }


# ── Layer 2: goal/route graph readiness ──────────────────────────────────────

def goal_layer(graphs_dir: Path) -> dict:
    autopsy = load_json(graphs_dir / "AUTOPSY_MAP.json")
    walls = autopsy.get("walls", [])
    events = autopsy.get("events", [])
    fronts = {f for w in walls for f in w.get("fronts", [])}
    unclassified = sum(
        1 for w in walls if w.get("fronts") == ["UNCLASSIFIED_FRONT"]
    )

    out = {
        "walls": len(walls),
        "autopsy_events": len(events),
        "fronts_seen": sorted(fronts),
        "walls_with_unclassified_front": unclassified,
        "kb": {},
        "link_rows": None,
        "well_posed": False,
        "missing": [],
    }
    if KNOWLEDGE_DB.is_file():
        con = sqlite3.connect(f"file:{KNOWLEDGE_DB}?mode=ro", uri=True)
        for table in ("kill", "move", "dossier", "journal_entry", "link"):
            try:
                out["kb"][table] = con.execute(
                    f'SELECT COUNT(*) FROM "{table}"'
                ).fetchone()[0]
            except sqlite3.Error:
                out["kb"][table] = None
        out["link_rows"] = out["kb"].get("link")
        con.close()

    cold_nodes = (out["kb"].get("kill") or 0) + len(walls)
    edges = out["link_rows"] or 0
    if unclassified == len(walls) and walls:
        out["missing"].append(
            "front classification: every wall sits in UNCLASSIFIED_FRONT, so no "
            "front->target path exists to carry a potential"
        )
    if edges < cold_nodes:
        out["missing"].append(
            f"edge structure: {edges} link rows for {cold_nodes} cold nodes "
            "(kills+walls) — the graph has boundary conditions but almost no "
            "interior, so the Dirichlet problem has nothing to diffuse through"
        )
    out["well_posed"] = not out["missing"]
    return out


# ── Report ───────────────────────────────────────────────────────────────────

def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", default="main",
                    help="proof root: 'main', 'atom', or a literal root_id")
    ap.add_argument("--graphs-dir", type=Path, default=GRAPHS)
    ap.add_argument("--json", action="store_true", help="emit JSON to stdout")
    args = ap.parse_args()

    lean = lean_layer(args.root, args.graphs_dir)
    goal = goal_layer(args.graphs_dir)

    if args.json:
        print(json.dumps({"lean_layer": lean, "goal_layer": goal}, indent=2))
        return

    print("=== proof potential probe (ADVISORY_ONLY, read-only) ===")
    print(f"root:            {lean['root_id']}")
    print(f"entry:           {lean['entry_file']}")
    print(f"closure:         {lean['closure_size']} files, "
          f"tainted={lean['tainted_files']}")
    print(f"doors (open project axioms):")
    for f, names in lean["doors"].items():
        print(f"  {f}  <- {', '.join(names)}")
    print(f"entry exposure:  {lean['entry_exposure']:.4f} "
          "(P that a uniform dependency descent hits an open assumption)")
    for f, p in sorted(lean["entry_door_split"].items(), key=lambda kv: -kv[1]):
        print(f"  via {f}: {p:.4f}")
    print(f"ground mass:     {lean['ground_mass']:.4f} "
          "(absorbed in fully proved floor)")
    print("hottest interior files (temperature = axiom exposure of their cone):")
    for v, t in lean["hottest_files"]:
        print(f"  {t:.4f}  {v}")

    print()
    print("=== goal/route layer readiness (where the idea would matter) ===")
    print(f"cold set on disk: {goal['kb'].get('kill')} kills in knowledge.db, "
          f"{goal['walls']} walls, {goal['autopsy_events']} autopsy events")
    print(f"fronts seen:      {goal['fronts_seen']}")
    print(f"link rows:        {goal['link_rows']}")
    print(f"well_posed:       {goal['well_posed']}")
    for m in goal["missing"]:
        print(f"  MISSING: {m}")


if __name__ == "__main__":
    try:
        main()
    except BrokenPipeError:  # tolerate `| head` in pipelines
        import os
        import sys

        try:
            sys.stdout.close()
        except Exception:
            pass
        os._exit(0)
