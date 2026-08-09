#!/usr/bin/env python3
"""GOAL057_SOURCE_WEIL_EVEN_SECTOR_SPECTRAL_CUT_PREFLIGHT — executable.

READ_ONLY_EXPERIMENTAL. No proof claim, no Lean edits, no route promotion.
Thresholds come verbatim from the owner directive; the few free instrument
choices are pinned in PRECOMMIT.md and in PIN below, frozen before the first
real-matrix run. Plants run before the real matrix is interpreted. The stop
rule halts at (13,60) on failure without evaluating N=90,120.
"""

from __future__ import annotations

import hashlib
import json
import random
import time
from pathlib import Path

import mpmath as mp

import ccm_source as src

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
RESULTS = HERE / "results_spectral_cut.json"

# Directive thresholds (frozen by the verdict, not tunable here).
THRESH = {
    "mass_min": "0.95",
    "rho_max": "0.25",
    "schur_improvement_min": "2.0",   # s_candidate <= s_best_elementary / 2
    "jaccard_min": "0.80",
    "cells": [[13, 60], [13, 90], [13, 120]],
}

# Precommitted instrument pins (see PRECOMMIT.md).
PIN = {
    "dps_base": 30,
    "dps_double": 60,
    "floor_exponent_offset": 15,      # floor = 10^-(dps-15)
    "lowhigh_threshold": 10,          # frozen |n|<=10 elementary split
    "candidate_rule": "min-conductance Fiedler sweep cut",
    "retained_side": "side holding >=0.5 of even-sector trial mass",
    "schur_direction": "smaller s is better",
    "doubling_rel_tol": "1e-6",
    "conductance_meaningful_max": "0.25",
    "pswf_K_full": 240,
    "panels_scale": 4,
    "seed": 57,
    "literal_spot_pairs": 12,
    "ode_residual_max": "1e-6",
}


def floor_eps():
    return mp.mpf(10) ** (-(mp.mp.dps - PIN["floor_exponent_offset"]))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


SOURCE_PINS = [
    "q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean",
    "q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean",
    "q3.lean.aristotle/Q3/Proofs/RouteB/ProlateLayer.lean",
    "q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage1.lean",
    "q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage2.lean",
    "q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage3.lean",
    "q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilFiniteFourierLedger.lean",
    "q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteRieszOperator.lean",
]


# ── even sector algebra ──────────────────────────────────────────────────────

def even_sector(K_full, N):
    """K+ in the orthonormal even basis b_0=e_0, b_j=(e_j+e_-j)/sqrt(2)."""
    c = N  # index of mode 0
    dim = N + 1
    Kp = mp.zeros(dim)
    s2 = mp.sqrt(mp.mpf(2))
    Kp[0, 0] = K_full[c, c]
    for j in range(1, dim):
        v = s2 * K_full[c, c + j]
        Kp[0, j] = Kp[j, 0] = v
    for i in range(1, dim):
        for j in range(i, dim):
            v = K_full[c + i, c + j] + K_full[c + i, c - j]
            Kp[i, j] = Kp[j, i] = v
    return Kp


def parity_cross_max(K_full, N):
    c = N
    worst = mp.mpf(0)
    for i in range(1, N + 1):
        for j in range(0, N + 1):
            a = K_full[c + i, c + j] - K_full[c - i, c - j]
            b = K_full[c + i, c - j] - K_full[c - i, c + j]
            worst = max(worst, abs(a + b) / 2)
    return worst


def trial_even_row(crow, N):
    """Even-sector coordinates of the kTrial row and the even-mass fraction."""
    s2 = mp.sqrt(mp.mpf(2))
    q = [mp.re(crow[0])] + [s2 * mp.re(crow[j]) for j in range(1, N + 1)]
    even_mass = mp.fsum(x ** 2 for x in q)  # ||c||=1 already
    norm = mp.sqrt(even_mass)
    return [x / norm for x in q], even_mass


# ── graph layer (proposal only) ──────────────────────────────────────────────

def affinity(Kp):
    dim = Kp.rows
    W = mp.zeros(dim)
    for i in range(dim):
        for j in range(dim):
            if i != j:
                W[i, j] = abs(Kp[i, j]) ** 2
    return W


def fiedler_order(W):
    dim = W.rows
    d = [mp.fsum(W[i, j] for j in range(dim)) for i in range(dim)]
    Ln = mp.zeros(dim)
    for i in range(dim):
        for j in range(dim):
            if i == j:
                Ln[i, j] = 1 - W[i, j] / d[i] if d[i] > 0 else mp.mpf(1)
            else:
                Ln[i, j] = -W[i, j] / (mp.sqrt(d[i] * d[j])) if d[i] > 0 and d[j] > 0 else mp.mpf(0)
    E, Q = mp.eigsy(Ln)
    order_ev = sorted(range(dim), key=lambda i: E[i])
    f_idx = order_ev[1]
    fied = [Q[i, f_idx] / (mp.sqrt(d[i]) if d[i] > 0 else 1) for i in range(dim)]
    return sorted(range(dim), key=lambda i: fied[i]), d


def sweep_cuts(order, W, d):
    """All prefix cuts with conductance; returns list of (frozenset S, phi)."""
    dim = len(order)
    total = mp.fsum(d)
    out = []
    for k in range(1, dim):
        S = frozenset(order[:k])
        volS = mp.fsum(d[i] for i in S)
        cut = mp.fsum(W[i, j] for i in S for j in range(dim) if j not in S)
        denom = min(volS, total - volS)
        phi = cut / denom if denom > 0 else mp.inf
        out.append((S, phi))
    return out


# ── operator judges ──────────────────────────────────────────────────────────

def judges(Kp, q_even, S):
    dim = Kp.rows
    S = sorted(S)
    T = [i for i in range(dim) if i not in set(S)]
    mu_S = mp.fsum(q_even[i] ** 2 for i in S)
    if mu_S < mp.mpf("0.5"):
        S, T = T, S
        mu_S = 1 - mu_S
    E = mp.matrix(len(S), len(T))
    for a, i in enumerate(S):
        for b, j in enumerate(T):
            E[a, b] = Kp[i, j]
    B = mp.matrix(len(T), len(T))
    for a, i in enumerate(T):
        for b, j in enumerate(T):
            B[a, b] = Kp[i, j]
    a_val = mp.fsum(q_even[i] * Kp[i, j] * q_even[j]
                    for i in range(dim) for j in range(dim))
    if len(T) == 0:
        return None
    U, Ssv, V = mp.svd_r(E.T if len(S) < len(T) else E)
    eps = max(Ssv)
    specB = mp.eigsy(B, eigvals_only=True)
    delta = min(abs(a_val - lam) for lam in specB)
    return {
        "S": [int(i) for i in S],
        "T_size": len(T),
        "mu": mu_S,
        "a": a_val,
        "epsilon": eps,
        "delta": delta,
        "rho": eps / delta if delta > 0 else mp.inf,
        "s": eps ** 2 / delta if delta > 0 else mp.inf,
        "specB_min": min(specB),
        "specB_max": max(specB),
    }


def jstr(x):
    return mp.nstr(x, 12) if isinstance(x, (mp.mpf, mp.mpc)) else x


def serialize(d):
    if isinstance(d, dict):
        return {k: serialize(v) for k, v in d.items()}
    if isinstance(d, (list, tuple)):
        return [serialize(v) for v in d]
    if isinstance(d, (mp.mpf, mp.mpc)):
        return mp.nstr(d, 12)
    return d


# ── plants ───────────────────────────────────────────────────────────────────

def run_pipeline(Kp):
    W = affinity(Kp)
    order, d = fiedler_order(W)
    cuts = sweep_cuts(order, W, d)
    S_best, phi_best = min(cuts, key=lambda t: (t[1], sorted(t[0])))
    return S_best, phi_best, cuts


def plant_block_diag():
    dim, split = 20, 12
    M = mp.zeros(dim)
    for i in range(dim):
        for j in range(dim):
            same = (i < split) == (j < split)
            if same and i != j:
                M[i, j] = mp.cos(mp.mpf(7 * i + 13 * j) / 10) + \
                    mp.cos(mp.mpf(7 * j + 13 * i) / 10) + 3
            elif i == j:
                M[i, j] = 5
    rng = random.Random(PIN["seed"])
    perm = list(range(dim))
    rng.shuffle(perm)
    Mp = mp.zeros(dim)
    for i in range(dim):
        for j in range(dim):
            Mp[i, j] = M[perm[i], perm[j]]
    S_best, phi, _ = run_pipeline(Mp)
    recovered = frozenset(perm[i] for i in S_best)
    planted = frozenset(range(split))
    ok = recovered in (planted, frozenset(range(dim)) - planted)
    return {"pass": bool(ok), "phi": jstr(phi)}


def plant_one_bridge():
    dim, split = 20, 12
    M = mp.zeros(dim)
    for i in range(dim):
        for j in range(dim):
            same = (i < split) == (j < split)
            if same and i != j:
                M[i, j] = mp.cos(mp.mpf(7 * i + 13 * j) / 10) + \
                    mp.cos(mp.mpf(7 * j + 13 * i) / 10) + 3
            elif i == j:
                M[i, j] = 5
    M[3, 15] = M[15, 3] = mp.mpf("0.9")
    S_best, phi, _ = run_pipeline(M)
    planted = frozenset(range(split))
    ok_cut = S_best in (planted, frozenset(range(dim)) - planted)
    cross = [(i, j) for i in S_best for j in range(dim)
             if j not in S_best and abs(M[i, j]) > 0]
    ok_bridge = set(map(frozenset, cross)) == {frozenset((3, 15))}
    return {"pass": bool(ok_cut and ok_bridge), "phi": jstr(phi)}


def plant_permutation(Kp):
    dim = Kp.rows
    rng = random.Random(PIN["seed"] + 1)
    perm = list(range(dim))
    rng.shuffle(perm)
    Kperm = mp.zeros(dim)
    for i in range(dim):
        for j in range(dim):
            Kperm[i, j] = Kp[perm[i], perm[j]]
    S0, _, _ = run_pipeline(Kp)
    S1, _, _ = run_pipeline(Kperm)
    mapped = frozenset(perm[i] for i in S1)
    ok = mapped in (S0, frozenset(range(dim)) - S0)
    return {"pass": bool(ok)}


def plant_sign_conjugation(Kp, q_even):
    dim = Kp.rows
    rng = random.Random(PIN["seed"] + 2)
    signs = [rng.choice((-1, 1)) for _ in range(dim)]
    Kc = mp.zeros(dim)
    for i in range(dim):
        for j in range(dim):
            Kc[i, j] = signs[i] * signs[j] * Kp[i, j]
    S0, _, _ = run_pipeline(Kp)
    S1, _, _ = run_pipeline(Kc)
    same_cut = S1 in (S0, frozenset(range(dim)) - S0)
    j0 = judges(Kp, q_even, S0)
    qc = [signs[i] * q_even[i] for i in range(dim)]
    j1 = judges(Kc, qc, S1 if same_cut else S0)
    tol = mp.mpf("1e-20")
    ok = same_cut and abs(j0["epsilon"] - j1["epsilon"]) < tol and \
        abs(j0["delta"] - j1["delta"]) < tol
    return {"pass": bool(ok)}


def plant_prime_sign(m_project):
    """Mutated prime sign must be rejected by the literal source-lock gate."""
    sm = src.SourceMatrix(m_project, 6)
    rng = random.Random(PIN["seed"] + 3)
    pairs = [(rng.randint(-6, 6), rng.randint(-6, 6)) for _ in range(6)]
    detected = False
    for n, m in pairs:
        mut = sm.tau(n, m, prime_sign=+1)
        lit = sm.tau_literal(n, m)
        if abs(mut - lit) > mp.mpf(10) ** (-(mp.mp.dps - 18)) * (1 + abs(lit)):
            detected = True
            break
    return {"pass": bool(detected)}


# ── phase 0 gates ────────────────────────────────────────────────────────────

def phase0(sm, trial, modes, K_full, crow, N):
    eps0 = floor_eps()
    gates = {}
    gates["repository_pin"] = {p: sha256(REPO / p) for p in SOURCE_PINS}
    gates["carrier_mode_order"] = modes == list(range(-N, N + 1))
    sym = max(abs(K_full[i, j] - K_full[j, i])
              for i in range(2 * N + 1) for j in range(i, 2 * N + 1))
    gates["symmetry_residual"] = {"max": jstr(sym), "pass": sym <= eps0}
    jkkj = parity_cross_max(K_full, N)
    gates["J_commutation_residual"] = {"max": jstr(jkkj), "pass": jkkj <= eps0}
    rng = random.Random(PIN["seed"] + 4)
    worst = mp.mpf(0)
    for _ in range(PIN["literal_spot_pairs"]):
        n, m = rng.randint(-N, N), rng.randint(-N, N)
        opt = sm.tau(n, m)
        lit = sm.tau_literal(n, m)
        worst = max(worst, abs(opt - lit) / (1 + abs(lit)))
    gates["literal_formula_spot_check"] = {
        "max_rel": jstr(worst),
        "pass": worst <= mp.mpf(10) ** (-(mp.mp.dps - 18)),
    }
    ode0 = src.pswf_ode_residual(trial.chi0, trial.d0, trial.c)
    ode4 = src.pswf_ode_residual(trial.chi4, trial.d4, trial.c)
    gates["pswf_ode_residual"] = {
        "psi0": jstr(ode0), "psi4": jstr(ode4),
        "pass": max(ode0, ode4) <= mp.mpf(PIN["ode_residual_max"]),
    }
    ortho = mp.fsum(trial.d0.get(k, mp.mpf(0)) * trial.d4.get(k, mp.mpf(0))
                    for k in set(trial.d0) | set(trial.d4))
    gates["pswf_orthogonality"] = {"inner": jstr(ortho), "pass": abs(ortho) <= eps0}
    e0 = trial.e.get(0, mp.mpf(0))
    gates["hTrial_vanishing_integral"] = {"e0": jstr(e0), "pass": abs(e0) <= eps0}
    nrm = mp.sqrt(mp.fsum(abs(z) ** 2 for z in crow.values()))
    gates["trial_unit_normalization"] = {
        "norm": jstr(nrm), "raw_gTrial_norm": jstr(trial.raw_norm),
        "pass": abs(nrm - 1) <= eps0 and trial.raw_norm > 0,
    }
    gates["orientation_W02_minus_WR_minus_Prime"] = {
        "note": "checked by literal_formula_spot_check against the Lean "
                "formula tau = W02 - WR - Prime; mutation plant flips it",
        "pass": bool(gates["literal_formula_spot_check"]["pass"]),
    }
    gates["all_pass"] = all(
        (g["pass"] if isinstance(g, dict) and "pass" in g else True)
        for g in gates.values() if not isinstance(g, str)
    ) and gates["carrier_mode_order"]
    return gates


# ── cell evaluation ──────────────────────────────────────────────────────────

def eval_cell(m_project, N):
    t0 = time.time()
    sm = src.SourceMatrix(m_project, N)
    modes, K_full = sm.full_matrix()
    trial = src.SourceTrial(m_project, PIN["pswf_K_full"])
    crow = trial.coefficient_row(N, panels_scale=PIN["panels_scale"])
    gates = phase0(sm, trial, modes, K_full, crow, N)
    out = {"cell": [m_project, N], "dps": mp.mp.dps, "gates": gates}
    if not gates["all_pass"]:
        out["failure"] = "GOAL057_SPECTRAL_CUT_SOURCE_LOCK_FAIL"
        return out

    Kp = even_sector(K_full, N)
    q_even, even_mass = trial_even_row(crow, N)
    out["even_sector"] = {
        "dim": N + 1,
        "trial_even_mass_fraction": jstr(even_mass),
        "parity_cross_max": jstr(parity_cross_max(K_full, N)),
        "parity_control_note": "exact J-symmetry; parity split is control only",
    }

    S_best, phi_best, cuts = run_pipeline(Kp)
    jc = judges(Kp, q_even, S_best)
    out["candidate"] = {"phi": jstr(phi_best), **serialize(jc)}
    out["candidate"]["retained_labels"] = jc["S"]

    frozen = {}
    half = frozenset(range(0, (N + 1 + 1) // 2))
    frozen["contiguous_half"] = judges(Kp, q_even, half)
    lowhigh = frozenset(range(0, PIN["lowhigh_threshold"] + 1))
    frozen["lowhigh_split"] = judges(Kp, q_even, lowhigh)
    out["frozen_baselines"] = serialize(frozen)

    best_elem_s = min(frozen["contiguous_half"]["s"], frozen["lowhigh_split"]["s"])
    crit = {
        "not_parity_only": True,
        "mass": jc["mu"] >= mp.mpf(THRESH["mass_min"]),
        "rho": jc["rho"] <= mp.mpf(THRESH["rho_max"]),
        "schur_2x": jc["s"] * mp.mpf(THRESH["schur_improvement_min"]) <= best_elem_s,
        "phi_meaningful": phi_best <= mp.mpf(PIN["conductance_meaningful_max"]),
    }
    out["criteria"] = {k: bool(v) for k, v in crit.items()}
    out["best_elementary_s"] = jstr(best_elem_s)
    out["elapsed_sec"] = round(time.time() - t0, 1)
    return out


def main():
    mp.mp.dps = PIN["dps_base"]
    report = {"target": "GOAL057_SOURCE_WEIL_EVEN_SECTOR_SPECTRAL_CUT_PREFLIGHT",
              "mode": "READ_ONLY_EXPERIMENTAL",
              "thresholds": THRESH, "pins": PIN, "plants": {}, "cells": [],
              "failure_codes": [], "success": False}

    print("== plants (pipeline self-tests, before real-matrix interpretation)")
    report["plants"]["block_diagonal"] = plant_block_diag()
    report["plants"]["one_bridge"] = plant_one_bridge()
    report["plants"]["prime_sign_mutation"] = plant_prime_sign(13)
    for k, v in report["plants"].items():
        print(f"   {k}: {'PASS' if v['pass'] else 'FAIL'}")
    if not all(v["pass"] for v in report["plants"].values()):
        report["failure_codes"].append("GOAL057_SPECTRAL_CUT_BASIS_ARTEFACT")
        RESULTS.write_text(json.dumps(report, indent=2))
        print("plants failed — instrument invalid, stopping")
        return

    print("== cell (13,60) at dps", mp.mp.dps)
    cell = eval_cell(13, 60)
    report["cells"].append(cell)
    if "failure" in cell:
        report["failure_codes"].append(cell["failure"])
        RESULTS.write_text(json.dumps(report, indent=2))
        print("phase-0 gates failed:", cell["failure"])
        return

    # real-matrix invariance plants at (13,60)
    sm = src.SourceMatrix(13, 60)
    _, K_full = sm.full_matrix()
    Kp = even_sector(K_full, 60)
    trial = src.SourceTrial(13, PIN["pswf_K_full"])
    crow = trial.coefficient_row(60, panels_scale=PIN["panels_scale"])
    q_even, _ = trial_even_row(crow, 60)
    report["plants"]["label_permutation"] = plant_permutation(Kp)
    report["plants"]["sign_conjugation"] = plant_sign_conjugation(Kp, q_even)
    for k in ("label_permutation", "sign_conjugation"):
        print(f"   {k}: {'PASS' if report['plants'][k]['pass'] else 'FAIL'}")
    if not all(v["pass"] for v in report["plants"].values()):
        report["failure_codes"].append("GOAL057_SPECTRAL_CUT_BASIS_ARTEFACT")
        RESULTS.write_text(json.dumps(report, indent=2))
        return

    crit = report["cells"][0]["criteria"]
    print("   criteria:", crit)
    if not all(crit.values()):
        # Instrument-defect fix (2026-08-09, Proshka postmortem): the
        # precommitted precision-doubling gate must run on the failure path
        # too, not only on success — a stop code reported at a single
        # precision level is not a validated stop code. The original
        # (13,60) run predates this fix; its doubling was executed
        # separately by same_cell_check.py.
        print("== precision doubling on failure path, dps", PIN["dps_double"])
        mp.mp.dps = PIN["dps_double"]
        src._GAUSS_CACHE.clear()
        report["doubling_on_failure"] = eval_cell(13, 60)
        mp.mp.dps = PIN["dps_base"]
        code = ("GOAL057_SPECTRAL_CUT_NO_STABLE_LOW_CONDUCTANCE_CUT"
                if not crit["phi_meaningful"] else
                "GOAL057_SPECTRAL_CUT_LOW_CONDUCTANCE_WITHOUT_SCHUR_POWER")
        report["failure_codes"].append(code)
        report["stop_rule"] = "failed at (13,60); N=90,120 not evaluated"
        RESULTS.write_text(json.dumps(report, indent=2))
        print("STOP at (13,60):", code)
        return

    print("== precision doubling at dps", PIN["dps_double"])
    mp.mp.dps = PIN["dps_double"]
    src._GAUSS_CACHE.clear()
    cell2 = eval_cell(13, 60)
    mp.mp.dps = PIN["dps_base"]
    report["doubling"] = cell2
    tol = mp.mpf(PIN["doubling_rel_tol"])
    stable = (cell2["candidate"]["retained_labels"] ==
              report["cells"][0]["candidate"]["retained_labels"])
    for key in ("epsilon", "delta", "mu"):
        a = mp.mpf(report["cells"][0]["candidate"][key])
        b = mp.mpf(cell2["candidate"][key])
        if abs(a - b) / (1 + abs(b)) > tol:
            stable = False
    if not stable:
        report["failure_codes"].append("GOAL057_SPECTRAL_CUT_NUMERICALLY_UNRESOLVED")
        RESULTS.write_text(json.dumps(report, indent=2))
        print("doubling unstable")
        return

    print("== N ladder 90, 120")
    retained_sets = {60: set(report["cells"][0]["candidate"]["retained_labels"])}
    for N in (90, 120):
        cell_n = eval_cell(13, N)
        report["cells"].append(cell_n)
        if "failure" in cell_n:
            report["failure_codes"].append(cell_n["failure"])
            RESULTS.write_text(json.dumps(report, indent=2))
            return
        retained_sets[N] = set(cell_n["candidate"]["retained_labels"])
    jac = {}
    for a, b in ((60, 90), (90, 120)):
        restr = {x for x in retained_sets[b] if x <= a}
        inter = len(retained_sets[a] & restr)
        union = len(retained_sets[a] | restr)
        jac[f"{a}_{b}"] = mp.mpf(inter) / union if union else mp.mpf(0)
    report["jaccard"] = {k: jstr(v) for k, v in jac.items()}
    ladder_ok = all(v >= mp.mpf(THRESH["jaccard_min"]) for v in jac.values())
    ladder_crit_ok = all(all(c["criteria"].values()) for c in report["cells"])
    if not (ladder_ok and ladder_crit_ok):
        report["failure_codes"].append(
            "GOAL057_SPECTRAL_CUT_NO_STABLE_LOW_CONDUCTANCE_CUT")
    report["success"] = not report["failure_codes"]
    if report["success"]:
        report["verdict"] = "GOAL057_SOURCE_WEIL_SPECTRAL_CUT_PREFLIGHT_PASS"
    RESULTS.write_text(json.dumps(report, indent=2))
    print("SUCCESS:", report["success"], report["failure_codes"])


if __name__ == "__main__":
    main()
