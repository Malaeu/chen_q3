"""Part A'' (v2): fixed-N flip scan. Freeze N0 = M_0(T0)-1 and theta0 = theta(T0); scan T in [T0, T0+40]
step 0.05 at sigma in {1/64, 1/8}; first T_flip with h_{N0}(sigma+iT; theta0) < 0; arb ball at the flip;
zero count of the entire function J_{N0}(.; theta0) on rectangles [0,1/2] x [T0+10k, T0+10(k+1)] (k=0..3) and the
mirror rectangles [-1/2,0] x ... by the argument principle, evaluated as the winding number of J along the boundary
with phase unwrapping under step control (every phase step < pi/2, else the step is halved), which is the discrete
form of (1/2 pi i) oint J'/J dp; the result is an integer by construction, the max phase step is reported as the check.

  python check_fixed_n_flip.py --dps 50 --workers 6 --out fixed_n_flip.json
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

T0S = [14.0, 20.0, 30.0, 40.0]
SIGMAS = ["1/64", "1/8"]
STEP = 0.05; SPAN = 40.0
EPS = 0.01

def frozen(T0):
    cc.ADAPTIVE_R = 0.0
    theta0, c0, M0, N0 = cc.cutoff(T0)
    return theta0, c0, M0, N0

def scan_chunk(task):
    """h_{N0}(sigma+iT; theta0) for a chunk of T values (mpmath dps)."""
    mp.mp.dps = task["dps"]
    theta0, c0, M0, N0 = frozen(task["T0"]); theta0 = mp.mpf(theta0)
    sigma = mp.mpf(Fraction(task["sigma"]))
    out = []
    for T in task["Ts"]:
        p = sigma + 1j*mp.mpf(T)
        J = list(mp.diffs(lambda x: cc.head(x, theta0, N0), p, 1))
        h = 4*mp.re(J[1]*mp.conj(J[0]))
        out.append({"T": T, "h": mp.nstr(h, 25), "absJ": mp.nstr(abs(J[0]), 12)})
    return {"T0": task["T0"], "sigma": task["sigma"], "N0": N0, "theta0": mp.nstr(theta0, 25), "rows": out}

def arb_sign_at(T0, sigma_str, T, dps=80):
    """Rigorous sign of h_{N0}(sigma+iT; theta0) with frozen theta0, N0 (ray integrals + tail balls)."""
    acb, arb = cc._arb_setup(dps)
    theta0f, _, M0, N0 = frozen(T0)
    theta = arb.pi()/4 - 1/(arb(T0) + 1); c = (2*theta).cos()
    fr = Fraction(sigma_str); sigma = arb(fr.numerator)/fr.denominator
    p = acb(sigma, arb(T)); L = arb(4)
    J = [acb(0), acb(0)]
    for n in range(1, N0+1):
        a = arb.pi()*n*n
        tb = cc._tail_bound_arb(arb, theta, arb(T), sigma, a, c, L).upper(); ball = acb(arb(0, tb), arb(0, tb))
        r1 = cc._ray_integrals_arb(acb, arb, p, theta, a, L, +1); r2 = cc._ray_integrals_arb(acb, arb, p, theta, a, L, -1)
        for j in range(2): J[j] = J[j] + r1[j] + r2[j] + ball + ball
    h = 4*(J[1]*J[0].conjugate()).real
    if h.lower() > 0: cert = "POSITIVE"
    elif h.upper() < 0: cert = "NEGATIVE"
    else: cert = "UNDECIDED"
    return {"h_arb": str(h), "sign_certificate": cert}

def winding(task):
    """Zero count of J_{N0}(.;theta0) inside the rectangle [s_lo, s_hi] x [t_lo, t_hi] via phase tracking."""
    mp.mp.dps = task["dps"]
    theta0, c0, M0, N0 = frozen(task["T0"]); theta0 = mp.mpf(theta0)
    s_lo, s_hi, t_lo, t_hi = task["rect"]
    def Jf(sig, T): return cc.head(mp.mpf(sig) + 1j*mp.mpf(T), theta0, N0)
    # boundary counter-clockwise: bottom (s_lo->s_hi, t_lo), right (t_lo->t_hi, s_hi), top (s_hi->s_lo, t_hi), left (t_hi->t_lo, s_lo)
    def side(f, a, b, h0):
        pts = []; x = a; n = max(2, int(abs(b-a)/h0)); hstep = (b-a)/n
        vals = [f(a + k*hstep) for k in range(n+1)]
        xs = [a + k*hstep for k in range(n+1)]
        # refine until every phase step < pi/2
        i = 0; maxstep = 0
        while i < len(vals)-1:
            d = mp.arg(vals[i+1]/vals[i])
            if abs(d) > mp.pi/2 and abs(xs[i+1]-xs[i]) > 1e-6:
                xm = (xs[i]+xs[i+1])/2; xs.insert(i+1, xm); vals.insert(i+1, f(xm)); continue
            maxstep = max(maxstep, abs(d)); i += 1
        return vals, maxstep
    total = mp.mpf(0); maxstep = 0; nev = 0
    for f, a, b, h0 in [(lambda x: Jf(x, t_lo), s_lo, s_hi, 0.01), (lambda x: Jf(s_hi, x), t_lo, t_hi, 0.02),
                        (lambda x: Jf(x, t_hi), s_hi, s_lo, 0.01), (lambda x: Jf(s_lo, x), t_hi, t_lo, 0.02)]:
        vals, ms = side(f, a, b, h0); nev += len(vals); maxstep = max(maxstep, ms)
        total += mp.fsum(mp.arg(vals[i+1]/vals[i]) for i in range(len(vals)-1))
    w = total/(2*mp.pi)
    return {"T0": task["T0"], "N0": N0, "rect": task["rect"], "winding_raw": mp.nstr(w, 12), "zeros": int(mp.nint(w)),
            "integer_residual": mp.nstr(abs(w - mp.nint(w)), 6), "max_phase_step": mp.nstr(maxstep, 6), "evaluations": nev,
            "reliable": bool(maxstep < mp.pi/2 and abs(w - mp.nint(w)) < 1e-6)}

def _worker(args):
    fn, task = args
    try: return fn, globals()[fn](task), None
    except Exception as e: return fn, task, repr(e)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=50); ap.add_argument("--wind-dps", type=int, default=30)
    ap.add_argument("--workers", type=int, default=max(1, os.cpu_count()//2)); ap.add_argument("--out", default=str(HERE/"fixed_n_flip.json"))
    a = ap.parse_args()
    tasks = []
    nT = int(round(SPAN/STEP)) + 1
    for T0 in T0S:
        for sg in SIGMAS:
            Ts = [round(T0 + k*STEP, 6) for k in range(nT)]
            for i in range(0, nT, 50):
                tasks.append(("scan_chunk", {"T0": T0, "sigma": sg, "Ts": Ts[i:i+50], "dps": a.dps}))
        for k in range(4):
            # sigma offset EPS: J_{N0}(iT) is real (3.6), its on-line zeros sit exactly on the sigma=0 side and would give
            # irreducible phase jumps of pi; the rectangles start at sigma=EPS so that only zeros with Re p > EPS are counted.
            tasks.append(("winding", {"T0": T0, "rect": [EPS, 0.5, T0 + 10*k, T0 + 10*(k+1)], "dps": a.wind_dps}))
            tasks.append(("winding", {"T0": T0, "rect": [-0.5, -EPS, T0 + 10*k, T0 + 10*(k+1)], "dps": a.wind_dps}))
    total = len(tasks); t0 = time.time()
    scans = {}; winds = []; fails = []
    print(f"fixed-N flip: {total} tasks ({sum(1 for f,_ in tasks if f=='scan_chunk')} scan chunks, {sum(1 for f,_ in tasks if f=='winding')} rectangles), workers {a.workers}", flush=True)
    with Pool(a.workers) as pool:
        for i, (fn, r, err) in enumerate(pool.imap_unordered(_worker, tasks, chunksize=1), 1):
            if err: fails.append({"fn": fn, "task": {k: v for k, v in r.items() if k != "Ts"}, "error": err}); label = f"FAIL {err[:60]}"
            elif fn == "scan_chunk":
                key = (r["T0"], r["sigma"]); scans.setdefault(key, {"N0": r["N0"], "theta0": r["theta0"], "rows": []}); scans[key]["rows"].extend(r["rows"])
                label = f"scan T0={r['T0']} sigma={r['sigma']} up to T={r['rows'][-1]['T']}"
            else:
                winds.append(r); label = f"winding T0={r['T0']} rect={r['rect']} zeros={r['zeros']} maxstep={r['max_phase_step']}"
            el = time.time()-t0; eta = el/i*(total-i)
            print(f"[{i}/{total}] {i*100//total}% | ETA {int(eta//60)}m{int(eta%60):02d}s | {label}", flush=True)
    # flips + arb confirmation
    results = []
    for (T0, sg), d in sorted(scans.items()):
        rows = sorted(d["rows"], key=lambda r: r["T"])
        flip = next((r for r in rows if mp.mpf(r["h"]) < 0), None)
        entry = {"T0": T0, "sigma": sg, "N0": d["N0"], "theta0": d["theta0"], "n_scan": len(rows),
                 "n_negative": sum(1 for r in rows if mp.mpf(r["h"]) < 0),
                 "T_flip": flip["T"] if flip else None, "Delta_T": (flip["T"] - T0) if flip else None,
                 "h_at_flip": flip["h"] if flip else None, "rows": rows}
        if flip:
            print(f"arb at flip T0={T0} sigma={sg} T={flip['T']} ...", flush=True)
            entry["arb_at_flip"] = arb_sign_at(T0, sg, flip["T"], 80)
            # also the last positive point before the flip
            idx = rows.index(flip)
            if idx > 0: entry["arb_before_flip"] = dict(T=rows[idx-1]["T"], **arb_sign_at(T0, sg, rows[idx-1]["T"], 80))
        results.append(entry)
    out = {"meta": {"T0s": T0S, "sigmas": SIGMAS, "step": STEP, "span": SPAN, "dps_scan": a.dps, "dps_winding": a.wind_dps,
                    "cutoff_frozen": "N0 = M_0(T0)-1 with (6.3) r=0, theta0 = pi/4 - 1/(T0+1)", "rect_sigma_offset": EPS, "runtime_seconds": time.time()-t0, "n_failures": len(fails)},
           "scans": results, "windings": sorted(winds, key=lambda w: (w["T0"], w["rect"][0], w["rect"][2])), "failures": fails}
    Path(a.out).write_text(json.dumps(out, indent=1))
    for e in results: print(f"T0={e['T0']} sigma={e['sigma']} N0={e['N0']} T_flip={e['T_flip']} dT={e['Delta_T']} arb={e.get('arb_at_flip',{}).get('sign_certificate')}")
    for w in out["windings"]: print(f"T0={w['T0']} rect={w['rect']} zeros={w['zeros']} residual={w['integer_residual']} maxstep={w['max_phase_step']}")
    print(f"written {a.out}", flush=True)

if __name__ == "__main__":
    main()
