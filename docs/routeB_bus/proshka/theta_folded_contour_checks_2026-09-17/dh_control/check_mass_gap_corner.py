"""P_M3_10: rigorous arb lower envelope of the mass gap ratio

    G(sigma, T) = (1 - M_-/M_+) / sigma ,   M_pm = lambda_pm ||P_pm e||^2

on the compact corner T in [sqrt(20), 30], sigma in {1/64, 1/32, 1/16, 1/8, 1/4, 3/8, 1/2},
adaptive cutoff (6.3) r = 0. Every value is an arb ball built from the ray integrals plus the analytic
tail ball, so a cell counts only if the whole ball lies above the threshold 1/4.

Context: MAC stated the mass-gap task on a domain wider than its data and quoted the grid minimum 1.24 as the
infimum; Linux refuted that constant with sigma = 1/2, T = sqrt(20) giving 0.375897 (float). This run puts a
certified interval around the corner.

  python check_mass_gap_corner.py --dps 80 --workers 8 --out mass_gap_corner_arb.json
"""
from __future__ import annotations
import argparse, json, os, sys, time
from fractions import Fraction
from multiprocessing import Pool
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent)); sys.path.insert(0, str(HERE))
import check_contour as cc
import check_head_masses as hm

THRESHOLD = Fraction(1, 4)

def point(task):
    dps = task["dps"]; acb, arb = cc._arb_setup(dps)
    cc.ADAPTIVE_R = 0.0
    T = arb(task["T"]); t1 = T + 1; theta = arb.pi()/4 - 1/t1; c = (2*theta).cos()
    fr = Fraction(task["sigma"]); sigma = arb(fr.numerator)/fr.denominator
    _, _, M, N = cc.cutoff(float(task["T"])); p = acb(sigma, T); L = arb(4); t0 = time.time()
    u, v = [], []
    for n in range(1, N+1):
        a = arb.pi()*n*n
        tb = cc._tail_bound_arb(arb, theta, T, sigma, a, c, L).upper(); ball = acb(arb(0, tb), arb(0, tb))
        for sign in (+1, -1):
            r = cc._ray_integrals_arb(acb, arb, p, theta, a, L, sign)
            u.append(r[0] + ball); v.append(r[1] + ball)
    m = hm.masses_from(u, v, conj=lambda z: z.conjugate(),
                       re=lambda z: z.real if isinstance(z, acb) else z,
                       im=lambda z: z.imag if isinstance(z, acb) else arb(0),
                       sqrt=lambda x: x.sqrt(), fsum=lambda xs: sum(xs[1:], xs[0]))
    Mp, Mm = m["M_plus"], m["M_minus"]
    q = Mm/Mp
    G = (1 - q)/sigma
    thr = arb(THRESHOLD.numerator)/THRESHOLD.denominator
    above = bool((G - thr).lower() > 0)
    below = bool((G - thr).upper() < 0)
    return {"sigma": task["sigma"], "T": task["T"], "N": N, "M": M, "dps": dps,
            "M_plus": str(Mp), "M_minus": str(Mm), "q": str(q), "G": str(G),
            "G_lower": G.lower().str(30, radius=False), "G_upper": G.upper().str(30, radius=False),
            "ball_above_1/4": above, "ball_below_1/4": below,
            "undecided": (not above and not below), "runtime_seconds": round(time.time()-t0, 2)}

def _worker(t):
    try: return point(t), None
    except Exception as e: return t, repr(e)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=80); ap.add_argument("--workers", type=int, default=max(1, os.cpu_count()//2))
    ap.add_argument("--Tmax", type=float, default=30.0); ap.add_argument("--out", default=str(HERE/"mass_gap_corner_arb.json"))
    a = ap.parse_args()
    T0 = float(mp.sqrt(20))
    Ts = [round(T0 + 0.05*k, 6) for k in range(int((6.0 - T0)/0.05) + 1)]
    Ts += [round(x, 6) for x in [6.0 + 0.25*k for k in range(1, int((a.Tmax - 6.0)/0.25) + 1)]]
    sigmas = ["1/64", "1/32", "1/16", "1/8", "1/4", "3/8", "1/2"]
    tasks = [{"sigma": s, "T": T, "dps": a.dps} for T in Ts for s in sigmas]
    total = len(tasks); t0 = time.time(); res = []; fails = []
    print(f"mass gap corner: {total} points (T {Ts[0]}..{Ts[-1]}, {len(sigmas)} sigmas), threshold {THRESHOLD}, arb dps {a.dps}, workers {a.workers}", flush=True)
    with Pool(a.workers) as pool:
        for i, (r, err) in enumerate(pool.imap_unordered(_worker, tasks, chunksize=1), 1):
            if err: fails.append({"task": r, "error": err}); label = f"FAIL {err[:60]}"
            else:
                res.append(r); label = f"sigma={r['sigma']} T={r['T']} N={r['N']} G_lower={r['G_lower'][:12]} {'OK' if r['ball_above_1/4'] else ('BELOW' if r['ball_below_1/4'] else 'UNDECIDED')}"
            el = time.time()-t0; eta = el/i*(total-i)
            print(f"[{i}/{total}] {i*100//total}% | ETA {int(eta//60)}m{int(eta%60):02d}s | {label}", flush=True)
    res.sort(key=lambda r: (float(Fraction(r["sigma"])), r["T"]))
    lows = [(mp.mpf(r["G_lower"]), r) for r in res]
    worst = min(lows, key=lambda x: x[0])
    n_above = sum(1 for r in res if r["ball_above_1/4"]); n_below = sum(1 for r in res if r["ball_below_1/4"])
    n_und = sum(1 for r in res if r["undecided"])
    by_sigma = {}
    for s in sigmas:
        v = [(mp.mpf(r["G_lower"]), r["T"]) for r in res if r["sigma"] == s]
        if v: mn = min(v); by_sigma[s] = {"min_G_lower": mp.nstr(mn[0], 8), "at_T": mn[1]}
    out = {"meta": {"prediction": "P_M3_10", "threshold": str(THRESHOLD), "dps": a.dps, "T_range": [Ts[0], Ts[-1]],
                    "T_step": "0.05 on [sqrt(20), 6], 0.25 above", "sigmas": sigmas, "cutoff": "adaptive (6.3) r=0",
                    "n_points": len(res), "n_failures": len(fails), "runtime_seconds": round(time.time()-t0, 1),
                    "certification": "each G is an arb ball; a cell counts only if the whole ball is above 1/4"},
           "verdict": {"balls_above_1/4": n_above, "balls_below_1/4": n_below, "undecided": n_und,
                       "certified_lower_envelope": mp.nstr(worst[0], 10),
                       "worst_cell": {"sigma": worst[1]["sigma"], "T": worst[1]["T"], "N": worst[1]["N"], "G": worst[1]["G"]},
                       "IF_A_envelope_ge_quarter": bool(worst[0] >= mp.mpf(1)/4)},
           "min_by_sigma": by_sigma, "points": res, "failures": fails}
    Path(a.out).write_text(json.dumps(out, indent=1))
    print(json.dumps(out["verdict"], indent=1)); print(json.dumps(by_sigma, indent=1))
    print(f"written {a.out}", flush=True)

if __name__ == "__main__":
    main()
