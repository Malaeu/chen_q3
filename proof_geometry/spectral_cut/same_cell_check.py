#!/usr/bin/env python3
"""GOAL057_SOURCE_TRIAL_RAYLEIGH_RESIDUAL_SAME_CELL_CHECK — executable.

READ_ONLY_EXPERIMENTAL. Implements the Proshka directive of 2026-08-09:
same cell (13,60), same frozen retained set S={0..27}, no new Fiedler run,
no new cut, no threshold change, no N=90/120.

Phase 0  next-cheapest decisive test: residual on the existing-instrument
         objects rebuilt at dps=30 (frozen K+, frozen q, frozen S).
Phase A  precision ladder dps=60,90: a, epsilon, Spec(B), delta, rho, s.
Phase B  residual + component cancellation ledger at each precision:
         r_full=||K+q - a q||, r_T=||P_T K+ q||, ||K+||_op,
         nu = r_full/max(1,||K+||_op), a = a_W02 - a_WR - a_Prime.
Phase C  only if a is zero-consistent at both dps levels: independent
         same-cell trial reconstruction via Chebyshev collocation in s=t^2
         (no import of the Legendre PSWF eigenvectors), same hTrial
         combination, same E*, same interval, same mode order, same l2
         normalization; projective overlap against the Legendre-path row;
         a_ind, r_ind on the SAME source matrix K+.

Terminal codes (exactly one; priority pinned in CHECK_PIN before the run):
  GOAL057_SPECTRAL_CUT_INSTRUMENT_MISMATCH
  GOAL057_SOURCE_TRIAL_NEAR_KERNEL_FINITE_CELL_DOSSIER
  GOAL057_SMALL_RAYLEIGH_NOT_SMALL_RESIDUAL
  GOAL057_SPECTRAL_CUT_KILL_RATIFIED_AFTER_INDEPENDENT_CHECK
"""

from __future__ import annotations

import json
import platform
import sys
import time
from pathlib import Path

import mpmath as mp

import ccm_source as src
from preflight import SOURCE_PINS, even_sector, sha256, trial_even_row

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results_same_cell_check.json"

FROZEN_S = list(range(28))          # from the directive, verbatim
CELL_M, CELL_N = 13, 60

CHECK_PIN = {
    "dps_quick": 30,
    "dps_ladder": [60, 90],
    "dps_independent": 40,
    "panels_scale_rule": "4 * dps / 30",
    "stability_rel_tol": "1e-8",     # directive, for eps/delta/rho/s
    "a_zero_consistent_rule": "|a| <= 10^-(dps-10) at every ladder level",
    "nu_near_kernel_max": "1e-8",    # directive R2
    "nu_cancellation_min": "1e-4",   # directive R3
    "overlap_gap_max": "1e-8",       # directive R4, on the full complex row
    "terminal_priority": [
        "INSTRUMENT_MISMATCH if ladder unstable, or independent row "
        "disagrees, or independent solver self-checks fail",
        "NEAR_KERNEL_DOSSIER if nu<=1e-8 at top precision and independent "
        "reconstruction agrees",
        "SMALL_RAYLEIGH_NOT_SMALL_RESIDUAL if nu>=1e-4",
        "KILL_RATIFIED otherwise (includes ZERO_CONSISTENT_UNRESOLVED nu "
        "band, marked as such, with rho>=1 stable)",
    ],
    "colloc_nodes": 96,
    "colloc_chi_window": "0 < chi < 20c, |Im|<=1e-15 rel, tail small",
    "phaseC_zero_counts": {"psi0": 0, "psi4": 2},
}


# ── shared object construction (existing instrument path) ────────────────────

def build_objects(dps):
    mp.mp.dps = dps
    src._GAUSS_CACHE.clear()
    sm = src.SourceMatrix(CELL_M, CELL_N)
    modes, K_full = sm.full_matrix()
    Kp = even_sector(K_full, CELL_N)
    trial = src.SourceTrial(CELL_M, 240)
    crow = trial.coefficient_row(
        CELL_N, panels_scale=max(4, 4 * dps // 30))
    q, even_mass = trial_even_row(crow, CELL_N)
    return sm, Kp, crow, q, even_mass


def frozen_judges(Kp, q):
    dim = Kp.rows
    S = FROZEN_S
    T = [i for i in range(dim) if i not in set(S)]
    a = mp.fsum(q[i] * Kp[i, j] * q[j] for i in range(dim) for j in range(dim))
    E = mp.matrix(len(T), len(S))
    for r, i in enumerate(T):
        for c, j in enumerate(S):
            E[r, c] = Kp[i, j]
    _, sv, _ = mp.svd_r(E)
    eps = max(sv)
    B = mp.matrix(len(T), len(T))
    for r, i in enumerate(T):
        for c, j in enumerate(T):
            B[r, c] = Kp[i, j]
    specB = mp.eigsy(B, eigvals_only=True)
    delta = min(abs(a - lam) for lam in specB)
    Kq = [mp.fsum(Kp[i, j] * q[j] for j in range(dim)) for i in range(dim)]
    r_full = mp.sqrt(mp.fsum((Kq[i] - a * q[i]) ** 2 for i in range(dim)))
    r_T = mp.sqrt(mp.fsum(Kq[i] ** 2 for i in T))
    specK = mp.eigsy(Kp, eigvals_only=True)
    K_op = max(abs(specK[0]), abs(specK[len(specK) - 1]))
    return {
        "a": a, "epsilon": eps, "delta": delta,
        "rho": eps / delta, "schur_s": eps ** 2 / delta,
        "specB_min": min(specB), "specB_max": max(specB),
        "r_full": r_full, "r_T": r_T, "K_op": K_op,
        "nu": r_full / max(mp.mpf(1), K_op),
        "mu_S": mp.fsum(q[i] ** 2 for i in S),
    }


def component_ledger(sm, q):
    """Rayleigh split a = a_W02 - a_WR - a_Prime on the even sector."""
    N, L = CELL_N, sm.L
    dim = 2 * N + 1
    mats = {}
    for name in ("w02", "wr", "prime"):
        M = mp.zeros(dim)
        for i in range(dim):
            n = i - N
            for j in range(i, dim):
                m = j - N
                if name == "w02":
                    v = src.w02_entry(L, n, m)
                elif name == "wr":
                    v = sm.wr_entry(n, m)
                else:
                    v = src.prime_entry(sm.m, L, n, m)
                M[i, j] = v
                M[j, i] = v
        mats[name] = even_sector(M, N)
    dimp = N + 1
    out = {}
    for name, Mp in mats.items():
        out["a_" + name] = mp.fsum(
            q[i] * Mp[i, j] * q[j] for i in range(dimp) for j in range(dimp))
    out["ledger_identity_residual"] = abs(
        (out["a_w02"] - out["a_wr"] - out["a_prime"]) -
        mp.fsum(q[i] * (mats["w02"][i, j] - mats["wr"][i, j] -
                        mats["prime"][i, j]) * q[j]
                for i in range(dimp) for j in range(dimp)))
    return out


# ── Phase C: independent trial reconstruction (Chebyshev collocation) ────────

def clenshaw(coeffs, x):
    b1 = b2 = mp.mpf(0)
    for k in range(len(coeffs) - 1, 0, -1):
        b1, b2 = coeffs[k] + 2 * x * b1 - b2, b1
    return coeffs[0] + x * b1 - b2


class ChebPSWF:
    """Even PSWF via collocation on the s=t^2 form:
    -[4s(1-s) f'' + (2-6s) f'] + c^2 s f = chi f, f(s)=psi(sqrt(s))."""

    def __init__(self, c, M=110):
        self.c, self.M = c, M
        nodes = [mp.cos(mp.pi * (2 * i + 1) / (2 * M)) for i in range(M)]
        A = mp.matrix(M, M)
        Bm = mp.matrix(M, M)
        for i, x in enumerate(nodes):
            s = (x + 1) / 2
            for j in range(M):
                T = mp.chebyt(j, x)
                dT = j * mp.chebyu(j - 1, x) if j >= 1 else mp.mpf(0)
                if j >= 1:
                    ddT = j * (j * T - x * mp.chebyu(j - 1, x)) / (x ** 2 - 1)
                else:
                    ddT = mp.mpf(0)
                A[i, j] = (-(4 * s * (1 - s) * 4 * ddT +
                             (2 - 6 * s) * 2 * dT) + c ** 2 * s * T)
                Bm[i, j] = T
        G = mp.inverse(Bm) * A
        E, ER = mp.eig(G)
        cands = []
        for k in range(M):
            lam = E[k]
            if abs(mp.im(lam)) > mp.mpf("1e-15") * (1 + abs(lam)):
                continue
            lam_r = mp.re(lam)
            if not (0 < lam_r < 20 * c):
                continue
            coeffs = [mp.re(ER[i, k]) for i in range(M)]
            tail = max(abs(v) for v in coeffs[-8:]) / max(abs(v) for v in coeffs)
            if tail > mp.mpf("1e-12"):
                continue
            cands.append((lam_r, coeffs))
        cands.sort(key=lambda t: t[0])
        self.pairs = cands

    def eigenfunction(self, zero_count):
        """Pick by number of sign changes of psi on (0,1); normalize
        int_{-1}^{1} psi^2 dt = 1; fix sign psi(0)>0."""
        for lam, coeffs in self.pairs:
            grid = [mp.mpf(i) / 400 for i in range(1, 400)]
            vals = [clenshaw(coeffs, 2 * s - 1) for s in grid]
            scale = max(abs(v) for v in vals)
            signs = [v for v in vals if abs(v) > scale * mp.mpf("1e-8")]
            changes = sum(1 for u, v in zip(signs[:-1], signs[1:]) if u * v < 0)
            if changes == zero_count:
                nrm2 = mp.quad(
                    lambda s: clenshaw(coeffs, 2 * s - 1) ** 2 / mp.sqrt(s),
                    [0, mp.mpf(1) / 2, 1])
                coeffs = [v / mp.sqrt(nrm2) for v in coeffs]
                if clenshaw(coeffs, mp.mpf(-1)) < 0:  # psi(0)=f(s=0)
                    coeffs = [-v for v in coeffs]
                integral = mp.quad(
                    lambda s: clenshaw(coeffs, 2 * s - 1) / mp.sqrt(s),
                    [0, mp.mpf(1) / 2, 1])
                return lam, coeffs, integral
        raise RuntimeError(f"no eigenfunction with {zero_count} zeros found")


def independent_row(dps):
    """Fully independent trial chain: collocation PSWF, own E*, own
    piecewise adaptive quadrature for the coefficient row."""
    mp.mp.dps = dps
    lam_win = mp.sqrt(mp.mpf(CELL_M))
    L = mp.log(mp.mpf(CELL_M))
    c = 2 * mp.pi * CELL_M
    solver = ChebPSWF(c, CHECK_PIN["colloc_nodes"])
    chi0, f0, I0raw = solver.eigenfunction(CHECK_PIN["phaseC_zero_counts"]["psi0"])
    chi4, f4, I4raw = solver.eigenfunction(CHECK_PIN["phaseC_zero_counts"]["psi4"])
    # h_n(x) = psi_n(x/lam)/sqrt(lam); I_n = int h_n = sqrt(lam) * int psi_n dt
    I0 = mp.sqrt(lam_win) * I0raw
    I4 = mp.sqrt(lam_win) * I4raw
    den = mp.sqrt(I0 ** 2 + I4 ** 2)

    def h_trial(x):
        if abs(x) >= lam_win:
            return mp.mpf(0)
        s = (x / lam_win) ** 2
        v0 = clenshaw(f0, 2 * s - 1)
        v4 = clenshaw(f4, 2 * s - 1)
        return (I4 * v0 - I0 * v4) / (den * mp.sqrt(lam_win))

    def e_star(u):
        kmax = int(mp.floor(lam_win / u))
        if kmax < 1:
            return mp.mpf(0)
        return mp.sqrt(u) * mp.fsum(h_trial(k * u) for k in range(1, kmax + 1))

    brk = sorted(set([mp.mpf(0), mp.mpf(1)] +
                     [1 - mp.log(k) / L for k in range(2, CELL_M + 1)]))
    row = {}
    for n in range(0, CELL_N + 1):
        acc = mp.mpf(0) * 1j
        for aa, bb in zip(brk[:-1], brk[1:]):
            acc += mp.quad(
                lambda v: mp.exp(-2j * mp.pi * n * v) *
                e_star(mp.exp(L * v) / lam_win), [aa, bb], maxdegree=8)
        row[n] = mp.sqrt(L) * acc
        if n:
            row[-n] = mp.conj(row[n])
    nrm = mp.sqrt(mp.fsum(abs(z) ** 2 for z in row.values()))
    row = {n: z / nrm for n, z in row.items()}
    return {"chi0": chi0, "chi4": chi4, "I0": I0, "I4": I4, "row": row,
            "solver_pairs_found": len(solver.pairs)}


# ── report plumbing ──────────────────────────────────────────────────────────

def jstr(x):
    return mp.nstr(x, 15) if isinstance(x, (mp.mpf, mp.mpc)) else x


def serialize(d):
    if isinstance(d, dict):
        return {k: serialize(v) for k, v in d.items()}
    if isinstance(d, (list, tuple)):
        return [serialize(v) for v in d]
    if isinstance(d, (mp.mpf, mp.mpc)):
        return mp.nstr(d, 15)
    return d


def zero_consistent(a, dps):
    return abs(a) <= mp.mpf(10) ** (-(dps - 10))


def main():
    t0 = time.time()
    report = {
        "target": "GOAL057_SOURCE_TRIAL_RAYLEIGH_RESIDUAL_SAME_CELL_CHECK",
        "mode": "READ_ONLY_EXPERIMENTAL",
        "cell": [CELL_M, CELL_N],
        "frozen_S": FROZEN_S,
        "no_new_fiedler": True,
        "check_pin": CHECK_PIN,
        "environment": {
            "command": "python3 same_cell_check.py",
            "python": sys.version.split()[0],
            "mpmath": mp.__version__,
            "platform": platform.platform(),
        },
        "source_hashes": {p: sha256((HERE.parents[1] / p)) for p in SOURCE_PINS},
        "phases": {},
    }

    # Phase 0 — next cheapest decisive test at dps 30
    print("== phase 0: residual on existing-instrument objects, dps 30")
    sm, Kp, crow, q, even_mass = build_objects(CHECK_PIN["dps_quick"])
    j30 = frozen_judges(Kp, q)
    report["phases"]["quick_dps30"] = serialize(j30)
    print(f"   a={jstr(j30['a'])}  r_full={jstr(j30['r_full'])}  "
          f"nu={jstr(j30['nu'])}  rho={jstr(j30['rho'])}")

    # Phase A/B — precision ladder with ledger
    ladder = {}
    for dps in CHECK_PIN["dps_ladder"]:
        print(f"== phase A/B at dps {dps}")
        sm, Kp_d, crow_d, q_d, _ = build_objects(dps)
        jd = frozen_judges(Kp_d, q_d)
        led = component_ledger(sm, q_d)
        ladder[dps] = {"judges": jd, "ledger": led}
        report["phases"][f"ladder_dps{dps}"] = serialize(
            {"judges": jd, "ledger": led})
        print(f"   a={jstr(jd['a'])}  eps={jstr(jd['epsilon'])}  "
              f"delta={jstr(jd['delta'])}  rho={jstr(jd['rho'])}  "
              f"nu={jstr(jd['nu'])}")
        print(f"   ledger: W02={jstr(led['a_w02'])}  WR={jstr(led['a_wr'])}  "
              f"Prime={jstr(led['a_prime'])}")
        RESULTS.write_text(json.dumps(report, indent=2))

    d1, d2 = CHECK_PIN["dps_ladder"]
    tol = mp.mpf(CHECK_PIN["stability_rel_tol"])
    stable = True
    for key in ("epsilon", "delta", "rho", "schur_s", "r_full", "nu"):
        x, y = ladder[d1]["judges"][key], ladder[d2]["judges"][key]
        if abs(x - y) / (1 + abs(y)) > tol:
            stable = False
    a_zero = (zero_consistent(ladder[d1]["judges"]["a"], d1) and
              zero_consistent(ladder[d2]["judges"]["a"], d2))
    if not a_zero:
        x, y = ladder[d1]["judges"]["a"], ladder[d2]["judges"]["a"]
        if abs(x - y) / (1 + abs(y)) > tol:
            stable = False
    rho_ge_1_both = all(ladder[d]["judges"]["rho"] >= 1 for d in (d1, d2))
    report["ladder_stable"] = bool(stable)
    report["a_zero_consistent"] = bool(a_zero)
    report["rho_ge_1_both_levels"] = bool(rho_ge_1_both)

    # Phase C — only on confirmed zero-consistency
    phaseC = None
    if a_zero and stable:
        print("== phase C: independent same-cell trial reconstruction")
        phaseC = independent_row(CHECK_PIN["dps_independent"])
        mp.mp.dps = CHECK_PIN["dps_ladder"][0]
        qL = {}
        _, Kp60, crow60, q60, _ = build_objects(CHECK_PIN["dps_ladder"][0])
        for n, z in crow60.items():
            qL[n] = z
        ov = abs(mp.fsum(mp.conj(qL[n]) * phaseC["row"][n]
                         for n in qL))
        gap = 1 - ov
        q_ind_even, _ = trial_even_row(phaseC["row"], CELL_N)
        j_ind = frozen_judges(Kp60, q_ind_even)
        report["phases"]["independent"] = serialize({
            "chi0": phaseC["chi0"], "chi4": phaseC["chi4"],
            "I0": phaseC["I0"], "I4": phaseC["I4"],
            "solver_pairs_found": phaseC["solver_pairs_found"],
            "projective_overlap": ov, "overlap_gap": gap,
            "a_independent": j_ind["a"], "r_full_independent": j_ind["r_full"],
            "nu_independent": j_ind["nu"], "rho_independent": j_ind["rho"],
        })
        print(f"   overlap gap={jstr(gap)}  a_ind={jstr(j_ind['a'])}  "
              f"nu_ind={jstr(j_ind['nu'])}")
        agree = gap <= mp.mpf(CHECK_PIN["overlap_gap_max"])
        report["independent_agrees"] = bool(agree)
    else:
        report["independent_agrees"] = None

    # Terminal code, priority pinned in CHECK_PIN
    nu_top = ladder[d2]["judges"]["nu"]
    if not stable or (phaseC is not None and not report["independent_agrees"]):
        code = "GOAL057_SPECTRAL_CUT_INSTRUMENT_MISMATCH"
    elif a_zero and phaseC is not None and report["independent_agrees"] and \
            nu_top <= mp.mpf(CHECK_PIN["nu_near_kernel_max"]):
        code = "GOAL057_SOURCE_TRIAL_NEAR_KERNEL_FINITE_CELL_DOSSIER"
    elif nu_top >= mp.mpf(CHECK_PIN["nu_cancellation_min"]):
        code = "GOAL057_SMALL_RAYLEIGH_NOT_SMALL_RESIDUAL"
    else:
        code = "GOAL057_SPECTRAL_CUT_KILL_RATIFIED_AFTER_INDEPENDENT_CHECK"
        report["nu_band"] = "ZERO_CONSISTENT_UNRESOLVED (1e-8 < nu < 1e-4)"
    if code != "GOAL057_SPECTRAL_CUT_INSTRUMENT_MISMATCH":
        report["kill_ratified"] = bool(rho_ge_1_both)
    report["terminal_code"] = code
    report["elapsed_sec"] = round(time.time() - t0, 1)
    RESULTS.write_text(json.dumps(report, indent=2))
    print("TERMINAL:", code, "| kill_ratified:",
          report.get("kill_ratified"), "| %.0fs" % report["elapsed_sec"])


if __name__ == "__main__":
    main()
