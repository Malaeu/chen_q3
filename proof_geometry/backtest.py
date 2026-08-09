#!/usr/bin/env python3
"""Blinded historical backtest for Q3_PROOF_GEOMETRY_V0.

Replays the Goal 056/057 corridor checkpoint by checkpoint. At each
checkpoint the model sees: the AND-factor graph, which nodes were closed by
then, the killed branches, and the plant. It does NOT see the historical
next-node choice; that list is consumed only here, as held-out truth.

Single-run policy: parameters in flow.PRECOMMIT are frozen before the first
run of this script; results are reported as they come out, including failure
codes. Re-running to tune weights is forbidden by the directive.

Success (all three required):
  1. historical next node in flow top-3 at >= 70% of checkpoints;
  2. flow top-3 rate strictly beats every baseline;
  3. plant never in flow top-3 and always scored below the historical next.

Failure codes:
  Q3_PROOF_GEOMETRY_NO_PREDICTIVE_GAIN
  Q3_PROOF_GEOMETRY_AND_STRUCTURE_LOST
  Q3_PROOF_GEOMETRY_FAKE_SHORTCUT_ACCEPTED
"""

from __future__ import annotations

import json
from pathlib import Path

import flow

HERE = Path(__file__).resolve().parent
CORRIDOR = HERE / "corridor_057.json"
RESULTS = HERE / "results_057.json"


def ranked(values: dict[str, float], descending: bool) -> list[str]:
    return sorted(values, key=lambda v: ((-values[v]) if descending else values[v], v))


def position(order: list[str], node: str) -> int:
    return order.index(node) + 1


def main() -> None:
    data = json.loads(CORRIDOR.read_text(encoding="utf-8"))
    goal = data["target"]
    corpus = data["corpus"]
    edges = data["hyperedges"]
    nodes = [n["id"] for n in data["nodes"]]
    children = [n["id"] for n in data["nodes"]
                if n["kind"] == "theorem" and "close_index" in n]
    kills = [n["id"] for n in data["nodes"] if n.get("status") == "KILLED"]
    plant = "PLANT_FAKE_SHORTCUT"
    close_order = sorted(
        (n["close_index"], n["id"]) for n in data["nodes"] if "close_index" in n
    )

    # AND-structure guard: the representation must be a factor graph with real
    # multi-input conjunctions, or the whole exercise is the C04 failure.
    multi = [e for e in edges if len(e["inputs"]) >= 2]
    if not multi or any(not e["inputs"] for e in edges):
        verdict = {"success": False,
                   "failure_codes": ["Q3_PROOF_GEOMETRY_AND_STRUCTURE_LOST"]}
        RESULTS.write_text(json.dumps(verdict, indent=2), encoding="utf-8")
        raise SystemExit("AND structure lost")

    methods = ["flow", "shortest_path", "pagerank", "topo_depth", "random"]
    per_cp = []
    for cp in data["checkpoints"]:
        k = cp["index"]
        closed = {corpus} | {nid for i, nid in close_order if i < k}
        candidates = sorted(
            [c for c in children if c not in closed] + kills + [plant]
        )
        truth = cp["historical_next"]

        u = flow.solve_potential(nodes, edges, cold=closed, goal=goal)
        fs = flow.flow_scores(candidates, edges, u)
        orders = {
            "flow": ranked(fs, descending=True),
            "shortest_path": ranked(
                flow.shortest_path_rank(candidates, edges, goal), descending=False),
            "pagerank": ranked(
                flow.pagerank_rank(candidates, edges), descending=True),
            "topo_depth": ranked(
                flow.topo_depth_rank(candidates, edges, corpus), descending=False),
            "random": ranked(flow.random_rank(candidates, k), descending=False),
        }
        row = {
            "checkpoint": k,
            "after": cp["after"],
            "historical_next": truth,
            "n_candidates": len(candidates),
            "positions": {m: position(orders[m], truth) for m in methods},
            "plant_positions": {m: position(orders[m], plant) for m in methods},
            "flow_score_next": fs[truth],
            "flow_score_plant": fs[plant],
            "flow_top3": orders["flow"][:3],
        }
        per_cp.append(row)

    n = len(per_cp)
    top3 = {m: sum(1 for r in per_cp if r["positions"][m] <= 3) / n
            for m in methods}
    plant_in_flow_top3 = [r["checkpoint"] for r in per_cp
                          if r["plant_positions"]["flow"] <= 3]
    plant_not_below_next = [r["checkpoint"] for r in per_cp
                            if r["flow_score_plant"] >= r["flow_score_next"]]

    failure_codes = []
    if top3["flow"] < 0.70 or any(
        top3["flow"] <= top3[m] for m in methods if m != "flow"
    ):
        failure_codes.append("Q3_PROOF_GEOMETRY_NO_PREDICTIVE_GAIN")
    if plant_in_flow_top3 or plant_not_below_next:
        failure_codes.append("Q3_PROOF_GEOMETRY_FAKE_SHORTCUT_ACCEPTED")

    result = {
        "schema": "Q3_PROOF_GEOMETRY_V0_BACKTEST_RESULT",
        "corridor": data["corridor"],
        "checkpoints": n,
        "top3_rate": top3,
        "plant_in_flow_top3_at": plant_in_flow_top3,
        "plant_not_below_next_at": plant_not_below_next,
        "success": not failure_codes,
        "failure_codes": failure_codes,
        "precommit": flow.PRECOMMIT,
        "per_checkpoint": per_cp,
    }
    RESULTS.write_text(json.dumps(result, indent=2, ensure_ascii=False),
                       encoding="utf-8")

    print(f"=== Q3_PROOF_GEOMETRY_V0_BACKTEST — {data['corridor']} ===")
    print(f"checkpoints: {n}, candidates per checkpoint: "
          f"{per_cp[0]['n_candidates']}..{per_cp[-1]['n_candidates']}")
    print("top-3 hit rate:")
    for m in methods:
        print(f"  {m:14s} {top3[m]:.3f}")
    print(f"plant in flow top-3 at checkpoints: {plant_in_flow_top3 or 'never'}")
    print(f"plant >= next score at checkpoints: {plant_not_below_next or 'never'}")
    print(f"SUCCESS: {result['success']}")
    for c in failure_codes:
        print(f"FAILURE_CODE: {c}")
    print("\nper-checkpoint (flow rank of truth | truth | flow top-3):")
    for r in per_cp:
        print(f"  cp{r['checkpoint']:02d} after={str(r['after']):6s} "
              f"rank={r['positions']['flow']:2d}  next={r['historical_next']:5s} "
              f"top3={r['flow_top3']}")


if __name__ == "__main__":
    main()
