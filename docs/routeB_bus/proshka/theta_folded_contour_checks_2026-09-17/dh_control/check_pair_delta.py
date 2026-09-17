"""Pair pullback rank discriminator (PROSHKA_RAY_BLOCK_WINDOW_INERTIA_2026-09-17, (6)-(9)).

For a pair p_+ = sigma + i gamma, p_- = -sigma + i gamma let r_N(p) in C^{2N} be the column of ray values
r_{n,+}(p) = I_n(p, theta), r_{n,-}(p) = I_n(-p, -theta) (n = 1..N), u = conj(r_N(p_+)), v = conj(r_N(p_-)).
  Delta_{pair,N} = |u|^2 |v|^2 - |u^* v|^2      (Gram determinant; > 0 <=> rank R_{rho,N} = 2, (9))
  Delta_hat      = Delta / (|u|^2 |v|^2) = sin^2 angle(u, v) in [0, 1]   (scale-free)
At sigma = 0 the rows coincide and Delta = 0 exactly; Delta_hat = O(sigma^2).

  --spira : DH rays at the Spira point (pair s_0, 1 - conj(s_0)), theta = theta(T0), N = 10..60      (P_M3_3)
  --map   : zeta rays, sigma in {1/64, 1/8, 1/4, 0.45}, gamma = 14..60 step 0.5, N = N(gamma)         (P_M3_4)
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
import check_dh_control as dh

def rays(kind, p, theta, N, kappa=None):
    out = []
    for n in range(1, N+1):
        if kind == "zeta": out += [cc.ray(n, p, theta), cc.ray(n, -p, -theta)]
        else: out += [dh.ray_dh(n, p, theta, kappa), dh.ray_dh(n, -p, -theta, kappa)]
    return out

def delta_from(rp, rm):
    u = [mp.conj(x) for x in rp]; v = [mp.conj(x) for x in rm]
    U2 = mp.fsum(abs(x)**2 for x in u); V2 = mp.fsum(abs(x)**2 for x in v)
    s = mp.fsum(mp.conj(a)*b for a, b in zip(u, v))
    D = U2*V2 - abs(s)**2
    return {"U2": U2, "V2": V2, "abs_s": abs(s), "Delta": D, "Delta_hat": D/(U2*V2)}

def point(task):
    mp.mp.dps = task["dps"]; cc.ADAPTIVE_R = 0.0; t0 = time.time()
    sigma = mp.mpf(Fraction(task["sigma"])) if "/" in str(task["sigma"]) else mp.mpf(task["sigma"])
    gamma = mp.mpf(task["gamma"]); N = task["N"]
    theta = mp.pi/4 - 1/(mp.mpf(task["T_theta"]) + 1)
    kappa = dh.kappa_mp() if task["kind"] == "dh" else None
    pp = sigma + 1j*gamma; pm = -sigma + 1j*gamma
    d = delta_from(rays(task["kind"], pp, theta, N, kappa), rays(task["kind"], pm, theta, N, kappa))
    out = {"kind": task["kind"], "sigma": str(task["sigma"]), "gamma": task["gamma"], "N": N, "theta": theta, "dps": task["dps"],
           "U2": d["U2"], "V2": d["V2"], "abs_uv": d["abs_s"], "Delta": d["Delta"], "Delta_hat": d["Delta_hat"],
           "Delta_hat_over_sigma2": d["Delta_hat"]/sigma**2, "Delta_positive": bool(d["Delta"] > 0), "runtime_seconds": round(time.time()-t0, 2)}
    return {k: (cc._nstr(v, max(25, task["dps"]-10)) if not isinstance(v, (bool, int, float, str)) else v) for k, v in out.items()}

def _worker(t):
    try: return point(t), None
    except Exception as e: return t, repr(e)

def run(tasks, workers, out, meta):
    total = len(tasks); res = {"points": [], "failures": [], "meta": dict(meta)}; t0 = time.time()
    print(f"pair delta: {total} tasks, workers {workers}", flush=True)
    with Pool(workers) as pool:
        for i, (r, err) in enumerate(pool.imap_unordered(_worker, tasks, chunksize=1), 1):
            if err: res["failures"].append({"task": r, "error": err}); label = f"FAIL {err[:60]}"
            else: res["points"].append(r); label = f"sigma={r['sigma']} gamma={r['gamma']} N={r['N']} Delta={r['Delta'][:11]} Delta_hat={r['Delta_hat'][:11]}"
            el = time.time()-t0; eta = el/i*(total-i)
            print(f"[{i}/{total}] {i*100//total}% | ETA {int(eta//60)}m{int(eta%60):02d}s | {label}", flush=True)
    res["points"].sort(key=lambda r: (str(r["sigma"]), float(r["gamma"]), r["N"]))
    res["meta"].update({"n_points": len(res["points"]), "n_failures": len(res["failures"]), "runtime_seconds": round(time.time()-t0, 1)})
    Path(out).write_text(json.dumps(res, indent=1)); print(f"written {out}", flush=True)
    return res

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--spira", action="store_true"); ap.add_argument("--map", action="store_true")
    ap.add_argument("--dps", type=int, default=50); ap.add_argument("--workers", type=int, default=max(1, os.cpu_count()//2)); ap.add_argument("--out", default=None)
    a = ap.parse_args()
    if a.spira:
        ref = json.load(open(HERE/"dh_control_reference.json")); T0 = float(ref["T0"]); sigma0 = str(ref["sigma0"])
        tasks = [{"kind": "dh", "sigma": sigma0, "gamma": T0, "N": N, "T_theta": T0, "dps": a.dps} for N in range(10, 61)]
        res = run(tasks, a.workers, a.out or str(HERE/"pair_delta_spira.json"),
                  {"part": "P_M3_3", "object": "Delta_{pair,N} at the Spira point of DH", "s0": ref["s0"], "sigma0": sigma0, "T0": T0, "N_range": "10..60", "dps": a.dps})
        pts = res["points"]; Ds = [mp.mpf(p["Delta"]) for p in pts]
        print("all Delta > 0:", all(D > 0 for D in Ds), "monotone increasing:", all(Ds[i] < Ds[i+1] for i in range(len(Ds)-1)))
        for p in pts[::5]: print(f"N={p['N']:<3} Delta={p['Delta'][:14]} Delta_hat={p['Delta_hat'][:14]}")
    elif a.map:
        cc.ADAPTIVE_R = 0.0; tasks = []
        for sg in ["1/64", "1/8", "1/4", "0.45"]:
            for k in range(93):
                g = 14.0 + 0.5*k; _, _, M, N = cc.cutoff(g)
                tasks.append({"kind": "zeta", "sigma": sg, "gamma": g, "N": N, "T_theta": g, "dps": a.dps})
        res = run(tasks, a.workers, a.out or str(HERE/"pair_delta_map.json"),
                  {"part": "P_M3_4", "object": "Delta(sigma, gamma, N(gamma)) for the zeta rays", "sigmas": ["1/64", "1/8", "1/4", "0.45"], "gamma": "14..60 step 0.5", "cutoff": "adaptive (6.3) r=0", "dps": a.dps})
        for sg in ["1/64", "1/8", "1/4", "0.45"]:
            v = [(float(p["gamma"]), mp.mpf(p["Delta_hat"]), mp.mpf(p["Delta_hat_over_sigma2"])) for p in res["points"] if p["sigma"] == sg]
            print(f"sigma={sg}: Delta>0 at {sum(1 for p in res['points'] if p['sigma']==sg and p['Delta_positive'])}/{len(v)}; Delta_hat min {mp.nstr(min(x[1] for x in v),5)} at gamma={min(v,key=lambda x:x[1])[0]}, max {mp.nstr(max(x[1] for x in v),5)}; Delta_hat/sigma^2 min {mp.nstr(min(x[2] for x in v),5)} max {mp.nstr(max(x[2] for x in v),5)}")
    else: ap.print_help()
