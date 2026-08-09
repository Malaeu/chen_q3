#!/usr/bin/env python3
"""Weighted bipartite (factor-graph) heat potential + baselines for V0.

AND-structure contract (Q3_PROOF_GEOMETRY_AND_STRUCTURE_LOST guard):
theorem nodes never connect to theorem nodes directly; every logical step is a
factor vertex joining ALL of its inputs and its single output. The potential
of a factor averages over all terminals, and the step gradient subtracts the
mean potential of ALL inputs — a step with one missing input cannot pretend to
be ready.

PRECOMMITTED parameters: frozen before the first backtest run and never tuned
afterwards (directive: no tuning weights after viewing held-out checkpoints).
"""

from __future__ import annotations

import math
import random

PRECOMMIT = {
    # conductance c_e = maturity[verifier] * exp(-alpha*(cost-1)
    #                                           - beta*len(risk_flags)
    #                                           - gamma*unverified_imports)
    "alpha": 1.0,
    "beta": 2.0,
    "gamma": 1.0,
    "killed_conductance": 0.0,
    "maturity": {
        "LEAN": 1.00,
        "ARB_INTERVAL": 0.95,
        "PAPER": 0.85,
        "PLANNED": 1.00,   # a planned in-discipline step, not yet attempted
        "CONDITIONAL": 0.55,
        "HEURISTIC": 0.20,
        "KILLED": 0.00,
    },
    "score": "max over producing edges of c_e * (u(out) - mean u(inputs)) / cost",
    "solver_tol": 1e-12,
    "solver_max_iter": 200_000,
    "top_k": 3,
    "tie_break": "lexicographic node id",
    "pagerank_damping": 0.85,
    "pagerank_iters": 200,
    "random_seed": 57,
    "baseline_orders": {
        "shortest_path": "ascending logical-step distance to target",
        "pagerank": "descending PageRank mass on the consumption digraph",
        "topo_depth": "ascending longest-path depth from CORPUS",
        "random": "seeded shuffle per checkpoint",
    },
    "beats": "strict > on top-3 hit rate against every baseline",
}


def conductance(edge: dict) -> float:
    if edge["killed"]:
        return PRECOMMIT["killed_conductance"]
    c = PRECOMMIT["maturity"][edge["verifier"]]
    c *= math.exp(
        -PRECOMMIT["alpha"] * (edge.get("cost", 1.0) - 1.0)
        - PRECOMMIT["beta"] * len(edge.get("risk_flags", []))
        - PRECOMMIT["gamma"] * edge.get("unverified_imports", 0)
    )
    return c


def solve_potential(nodes: list[str], edges: list[dict],
                    cold: set[str], goal: str) -> dict[str, float]:
    """Dirichlet problem on the star-expanded factor graph.

    cold nodes: u=0; goal: u=1; theorem and factor vertices harmonic.
    Deterministic Gauss-Seidel sweep in sorted vertex order.
    """
    adj: dict[str, list[tuple[str, float]]] = {n: [] for n in nodes}
    factor_ids = []
    for e in edges:
        c = conductance(e)
        fid = "F::" + e["id"]
        factor_ids.append(fid)
        adj[fid] = []
        if c <= 0.0:
            continue
        for t in list(e["inputs"]) + [e["output"]]:
            adj[fid].append((t, c))
            adj[t].append((fid, c))

    u = {v: 0.0 for v in list(adj)}
    u[goal] = 1.0
    fixed = set(cold) | {goal}
    order = sorted(v for v in adj if v not in fixed)
    for _ in range(PRECOMMIT["solver_max_iter"]):
        delta = 0.0
        for v in order:
            nb = adj[v]
            tot = sum(w for _, w in nb)
            if tot <= 0.0:
                continue
            new = sum(w * u[t] for t, w in nb) / tot
            delta = max(delta, abs(new - u[v]))
            u[v] = new
        if delta < PRECOMMIT["solver_tol"]:
            break
    return u


def flow_scores(candidates: list[str], edges: list[dict],
                u: dict[str, float]) -> dict[str, float]:
    by_output: dict[str, list[dict]] = {}
    for e in edges:
        by_output.setdefault(e["output"], []).append(e)
    scores = {}
    for v in candidates:
        best = 0.0
        for e in by_output.get(v, []):
            c = conductance(e)
            if c <= 0.0:
                continue
            mean_in = (sum(u[t] for t in e["inputs"]) / len(e["inputs"])
                       if e["inputs"] else 0.0)
            best = max(best, c * (u[v] - mean_in) / e.get("cost", 1.0))
        scores[v] = best
    return scores


# ── Baselines ────────────────────────────────────────────────────────────────

def consumption_digraph(edges: list[dict]) -> dict[str, set[str]]:
    """X -> Y iff X is an input of a non-killed step producing Y."""
    g: dict[str, set[str]] = {}
    for e in edges:
        if e["killed"]:
            continue
        for src in e["inputs"]:
            g.setdefault(src, set()).add(e["output"])
        g.setdefault(e["output"], set())
    return g


def shortest_path_rank(candidates: list[str], edges: list[dict],
                       goal: str) -> dict[str, float]:
    g = consumption_digraph(edges)
    dist = {}
    for v in candidates:
        seen, frontier, d = {v}, [v], 0
        found = math.inf
        while frontier:
            if goal in frontier:
                found = d
                break
            nxt = []
            for x in frontier:
                for y in g.get(x, ()):
                    if y not in seen:
                        seen.add(y)
                        nxt.append(y)
            frontier, d = nxt, d + 1
        dist[v] = found
    return dist  # ascending better


def pagerank_rank(candidates: list[str], edges: list[dict]) -> dict[str, float]:
    g = consumption_digraph(edges)
    nodes = sorted(g)
    n = len(nodes)
    pr = {v: 1.0 / n for v in nodes}
    d = PRECOMMIT["pagerank_damping"]
    for _ in range(PRECOMMIT["pagerank_iters"]):
        nxt = {v: (1.0 - d) / n for v in nodes}
        for v in nodes:
            outs = g[v]
            if outs:
                share = pr[v] / len(outs)
                for y in outs:
                    nxt[y] += d * share
            else:
                for y in nodes:
                    nxt[y] += d * pr[v] / n
        pr = nxt
    return {v: pr.get(v, 0.0) for v in candidates}  # descending better


def topo_depth_rank(candidates: list[str], edges: list[dict],
                    corpus: str) -> dict[str, float]:
    g = consumption_digraph(edges)
    memo: dict[str, float] = {corpus: 0.0}
    rg: dict[str, set[str]] = {v: set() for v in g}
    for x, outs in g.items():
        for y in outs:
            rg.setdefault(y, set()).add(x)

    def depth(v: str, stack: frozenset = frozenset()) -> float:
        if v in memo:
            return memo[v]
        if v in stack:
            return 0.0
        preds = rg.get(v, ())
        val = (max((depth(p, stack | {v}) for p in preds), default=-math.inf)
               + 1.0) if preds else math.inf
        memo[v] = val
        return val

    return {v: depth(v) for v in candidates}  # ascending better


def random_rank(candidates: list[str], checkpoint_index: int) -> dict[str, float]:
    rng = random.Random(PRECOMMIT["random_seed"] + checkpoint_index)
    order = sorted(candidates)
    rng.shuffle(order)
    return {v: float(i) for i, v in enumerate(order)}  # ascending better
