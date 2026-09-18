"""P_M3_11: rigorous arb certificate of the tail lemma on the barycentre of t under the ray measure.

alpha_n(t) = phi_n(t + i theta) e^{p (t + i theta)},   tau_n = (int_0^inf t alpha_n dt) / (int_0^inf alpha_n dt)

Identity used (recorded in the registration before the run): the p-derivative of the ray brings down (t + i theta),
so d_p I_n = int (t + i theta) alpha_n dt, hence

    tau_n = d_p I_n / I_n - i theta = l_n - i theta,      Re tau_n = Re l_n.

No separate moment integral is needed; the existing arb ray machinery gives orders 0 and 1 with the analytic tail.

Lemma to certify, for T > 30, 0 <= sigma <= 1/2, 1 <= n <= sqrt(T/(2 pi sin 2 theta)):

    Re tau_n >= t_0(n,T) - 6/T,      t_0(n,T) = (1/2) log(T / (2 pi n^2 sin 2 theta)).

  python check_tau_lemma.py --dps 80 --Tmin 30 --Tmax 80 --workers 8 --out tau_lemma_arb.json
"""
from __future__ import annotations
import argparse, json, os, sys, time
from fractions import Fraction
from multiprocessing import Pool
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import check_contour as cc

def point(task):
    dps = task["dps"]; acb, arb = cc._arb_setup(dps)
    cc.ADAPTIVE_R = 0.0
    T = arb(task["T"]); theta = arb.pi()/4 - 1/(T + 1); c = (2*theta).cos()
    fr = Fraction(task["sigma"]); sigma = arb(fr.numerator)/fr.denominator
    _, _, M, N = cc.cutoff(float(task["T"])); p = acb(sigma, T); L = arb(4)
    n = task["n"]; a = arb.pi()*n*n
    tb = cc._tail_bound_arb(arb, theta, T, sigma, a, c, L).upper(); ball = acb(arb(0, tb), arb(0, tb))
    r = cc._ray_integrals_arb(acb, arb, p, theta, a, L, +1)
    I0 = r[0] + ball; I1 = r[1] + ball
    tau = I1/I0 - acb(0, 1)*theta          # tau_n = l_n - i theta
    re_tau = tau.real
    s2 = (2*theta).sin()
    t0 = (T/(2*arb.pi()*n*n*s2)).log()/2
    rhs = t0 - 6/T
    margin = re_tau - rhs
    n_max = (T/(2*arb.pi()*s2)).sqrt()
    return {"n": n, "sigma": task["sigma"], "T": task["T"], "N": N,
            "Re_tau": re_tau.str(24, radius=False), "Re_tau_lower": re_tau.lower().str(24, radius=False),
            "t0": t0.str(20, radius=False), "rhs_t0_minus_6overT": rhs.str(20, radius=False),
            "margin_lower": margin.lower().str(20, radius=False),
            "holds": bool(margin.lower() > 0), "fails": bool(margin.upper() < 0),
            "undecided": bool(not (margin.lower() > 0) and not (margin.upper() < 0)),
            "n_within_bulk": bool(arb(n) <= n_max), "n_max_bulk": n_max.str(10, radius=False),
            "abs_I0": abs(I0).str(10, radius=False)}

def _worker(t):
    try: return point(t), None
    except Exception as e: return t, repr(e)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=80); ap.add_argument("--workers", type=int, default=max(1, os.cpu_count()//2))
    ap.add_argument("--Tmin", type=float, default=30.0); ap.add_argument("--Tmax", type=float, default=80.0)
    ap.add_argument("--Tstep", type=float, default=0.25); ap.add_argument("--nmax", type=int, default=2)
    ap.add_argument("--out", default=str(HERE/"tau_lemma_arb.json"))
    a = ap.parse_args()
    Ts = [round(a.Tmin + a.Tstep*k, 6) for k in range(1, int((a.Tmax - a.Tmin)/a.Tstep) + 1)]
    sigmas = ["1/64", "1/32", "1/16", "1/8", "1/4", "3/8", "1/2"]
    tasks = [{"n": n, "sigma": s, "T": T, "dps": a.dps} for T in Ts for s in sigmas for n in range(1, a.nmax+1)]
    total = len(tasks); t0 = time.time(); res = []; fails = []
    print(f"tau lemma: {total} balls (T {Ts[0]}..{Ts[-1]} step {a.Tstep}, {len(sigmas)} sigmas, n <= {a.nmax}), arb dps {a.dps}, workers {a.workers}", flush=True)
    with Pool(a.workers) as pool:
        for i, (r, err) in enumerate(pool.imap_unordered(_worker, tasks, chunksize=2), 1):
            if err: fails.append({"task": r, "error": err}); label = f"FAIL {err[:60]}"
            else:
                res.append(r); label = f"n={r['n']} sigma={r['sigma']} T={r['T']} Re_tau={r['Re_tau'][:9]} t0={r['t0'][:8]} {'OK' if r['holds'] else ('FAILS' if r['fails'] else 'UNDECIDED')}"
            if i % 25 == 0 or i == total:
                el = time.time()-t0; eta = el/i*(total-i)
                print(f"[{i}/{total}] {i*100//total}% | ETA {int(eta//60)}m{int(eta%60):02d}s | {label}", flush=True)
    res.sort(key=lambda r: (r["n"], float(Fraction(r["sigma"])), r["T"]))
    holds = sum(1 for r in res if r["holds"]); bad = [r for r in res if r["fails"]]; und = [r for r in res if r["undecided"]]
    worst = min(res, key=lambda r: mp.mpf(r["margin_lower"]))
    by = {}
    for n in range(1, a.nmax+1):
        for s in sigmas:
            v = [r for r in res if r["n"] == n and r["sigma"] == s]
            if v:
                w = min(v, key=lambda r: mp.mpf(r["margin_lower"]))
                by[f"n={n},sigma={s}"] = {"min_margin_lower": w["margin_lower"][:12], "at_T": w["T"], "Re_tau": w["Re_tau"][:10], "t0": w["t0"][:10]}
    out = {"meta": {"prediction": "P_M3_11", "lemma": "Re tau_n >= t_0(n,T) - 6/T, t_0 = (1/2) log(T/(2 pi n^2 sin 2 theta))",
                    "identity": "tau_n = d_p I_n / I_n - i theta (the p-derivative brings down t + i theta)",
                    "dps": a.dps, "T_range": [Ts[0], Ts[-1]], "T_step": a.Tstep, "sigmas": sigmas, "n_max": a.nmax,
                    "cutoff": "adaptive (6.3) r=0", "n_points": len(res), "n_failures": len(fails),
                    "runtime_seconds": round(time.time()-t0, 1),
                    "certification": "each Re tau_n is an arb ball; a cell counts only if the whole margin ball is positive"},
           "verdict": {"holds": holds, "of": len(res), "fails": len(bad), "undecided": len(und),
                       "IF_A_lemma_certified": bool(holds == len(res)),
                       "worst_cell": {k: worst[k] for k in ("n", "sigma", "T", "Re_tau", "t0", "rhs_t0_minus_6overT", "margin_lower")},
                       "failing_cells": [{k: r[k] for k in ("n", "sigma", "T", "margin_lower")} for r in bad[:20]],
                       "undecided_cells": [{k: r[k] for k in ("n", "sigma", "T", "margin_lower")} for r in und[:20]]},
           "min_margin_by_cell": by, "points": res, "failures": fails}
    Path(a.out).write_text(json.dumps(out, indent=1))
    print(json.dumps(out["verdict"], indent=1)[:2500]); print(json.dumps(by, indent=1)[:1500])
    print(f"written {a.out}", flush=True)

if __name__ == "__main__":
    main()
