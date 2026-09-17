"""Part A' (v2): the two spectral masses of the head on the original vector e=(1,...,1).

Object (Proshka HEAD_SIGN adjudication (4.2)-(4.4)): rays u = (I_n(p,th), I_n(-p,-th))_{n<=N} in C^{2N},
v = d/dp u (theta, N fixed; reflected ray gets its sign from the chain rule), s = u^* v, U=|u|, V=|v|.
A = 2(conj(u) v^T + conj(v) u^T) is Hermitian of rank 2 with lambda_+- = 2 Re s +- 2 sqrt(U^2 V^2 - (Im s)^2).
With x = conj(u), y = conj(v):  A e = 2(D x + J y),  A^2 e = 4[ x (D s + J V^2) + y (D U^2 + J conj(s)) ],
J = e.u, D = e.v.  Spectral projectors P_+ = A(A - lambda_- I)/(lambda_+(lambda_+ - lambda_-)),
P_- = A(A - lambda_+ I)/(lambda_-(lambda_- - lambda_+)) give P_+- e = alpha_+- x + beta_+- y with
  alpha_+- = (4 D s + 4 J V^2 - 2 lambda_-+ D) / (lambda_+-(lambda_+- - lambda_-+)),
  beta_+-  = (4 D U^2 + 4 J conj(s) - 2 lambda_-+ J) / (lambda_+-(lambda_+- - lambda_-+)),
  |alpha x + beta y|^2 = |alpha|^2 U^2 + |beta|^2 V^2 + 2 Re(conj(alpha) beta conj(s)).
Masses M_+ = lambda_+ |P_+ e|^2, M_- = |lambda_-| |P_- e|^2, q = M_-/M_+; identity M_+ - M_- = h_N = 4 Re(D conj J).

  python check_head_masses.py --zeta --dps 50 --workers 6 --out head_masses_zeta.json
  python check_head_masses.py --dh   --dps 50 --workers 6 --out head_masses_dh.json
  python check_head_masses.py --arb  --dps 80 --workers 4 --out head_masses_arb.json   # sign of M_+ - M_- - E_N at 10 points
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

def rays_mp(kind, p, theta, N, kappa=None):
    u, v = [], []
    for n in range(1, N+1):
        for sign in (+1, -1):
            if kind == "zeta":
                f = lambda x, n=n, sg=sign: cc.ray(n, sg*x, sg*theta)
            else:
                f = lambda x, n=n, sg=sign: dh.ray_dh(n, sg*x, sg*theta, kappa)
            d = list(mp.diffs(f, p, 1))
            u.append(d[0]); v.append(d[1])
    return u, v

def masses_from(u, v, conj=mp.conj, re=mp.re, im=mp.im, sqrt=mp.sqrt, fsum=None):
    fsum = fsum or (lambda xs: mp.fsum(xs))
    s = fsum([conj(ui)*vi for ui, vi in zip(u, v)])
    U2 = fsum([re(conj(ui)*ui) for ui in u]); V2 = fsum([re(conj(vi)*vi) for vi in v])
    J = fsum(u); D = fsum(v)
    disc = U2*V2 - im(s)**2
    root = sqrt(disc)
    lp = 2*(re(s) + root); lm = 2*(re(s) - root)
    def proj_norm2(lam, lam_other):
        den = lam*(lam - lam_other)
        alpha = (4*D*s + 4*J*V2 - 2*lam_other*D)/den
        beta = (4*D*U2 + 4*J*conj(s) - 2*lam_other*J)/den
        return re(conj(alpha)*alpha)*U2 + re(conj(beta)*beta)*V2 + 2*re(conj(alpha)*beta*conj(s))
    Pp = proj_norm2(lp, lm); Pm = proj_norm2(lm, lp)
    Mp = lp*Pp; Mm = -lm*Pm
    h_direct = 4*re(D*conj(J))
    return {"s": s, "U2": U2, "V2": V2, "J": J, "D": D, "lambda_plus": lp, "lambda_minus": lm,
            "P_plus_e_norm2": Pp, "P_minus_e_norm2": Pm, "M_plus": Mp, "M_minus": Mm,
            "h_from_masses": Mp - Mm, "h_direct": h_direct}

def point_mp(task):
    dps = task["dps"]; mp.mp.dps = dps
    kind = task["kind_fn"]; kappa = dh.kappa_mp() if kind == "dh" else None
    cc.ADAPTIVE_R = 0.0
    T = mp.mpf(task["T"]); sg = task["sigma"]; sigma = mp.mpf(Fraction(sg)) if "/" in sg else mp.mpf(sg)
    theta, c, M, N = cc.cutoff(T)
    p = sigma + 1j*T; t0 = time.time()
    u, v = rays_mp(kind, p, theta, N, kappa)
    m = masses_from(u, v)
    if kind == "zeta":
        E = sigma*cc.e_N_of(T, theta, c, M)
    else:
        _, _, E = dh.budgets_dh(theta, c, M, sigma, T)
    q = m["M_minus"]/m["M_plus"]
    out = {"sigma": sg, "T": task["T"], "kind": task["kind"], "gamma": task.get("gamma"), "dps": dps, "cutoff_rule": "adaptive_6.3_r=0",
           "M": M, "N": N, "lambda_plus": m["lambda_plus"], "lambda_minus": m["lambda_minus"],
           "P_plus_e_norm2": m["P_plus_e_norm2"], "P_minus_e_norm2": m["P_minus_e_norm2"],
           "M_plus": m["M_plus"], "M_minus": m["M_minus"], "q": q, "E_N": E, "E_over_M_plus": E/m["M_plus"],
           "h_from_masses": m["h_from_masses"], "h_direct": m["h_direct"],
           "identity_rel_err": abs(m["h_from_masses"] - m["h_direct"])/max(abs(m["h_direct"]), mp.mpf(10)**-300),
           "one_minus_q": 1 - q, "runtime_seconds": time.time()-t0}
    return {k: cc._nstr(v) for k, v in out.items()}

def point_arb(task):
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
    m = masses_from(u, v, conj=lambda z: z.conjugate(), re=lambda z: z.real if isinstance(z, acb) else z,
                    im=lambda z: z.imag if isinstance(z, acb) else arb(0), sqrt=lambda x: x.sqrt(), fsum=lambda xs: sum(xs[1:], xs[0]))
    eN = 28672*c**-5*arb(M)**3*(-arb.pi()*c*M*M - 2*theta*T).exp(); E = sigma*eN
    margin = m["M_plus"] - m["M_minus"] - E
    def cert(x):
        if x.lower() > 0: return "POSITIVE"
        if x.upper() < 0: return "NEGATIVE"
        return "UNDECIDED"
    return {"sigma": task["sigma"], "T": task["T"], "dps": dps, "M": M, "N": N,
            "M_plus": str(m["M_plus"]), "M_minus": str(m["M_minus"]), "q": str(m["M_minus"]/m["M_plus"]),
            "h_from_masses": str(m["h_from_masses"]), "h_direct": str(m["h_direct"]), "E_N": str(E),
            "sign_certificate_Mplus_minus_Mminus_minus_E": cert(margin), "sign_certificate_h_direct_minus_E": cert(m["h_direct"] - E),
            "runtime_seconds": time.time()-t0}

def _worker(args):
    fn, task = args
    try: return globals()[fn](task), None
    except Exception as e: return task, repr(e)

def run(tasks, fn, workers, out, meta):
    total = len(tasks); res = {"points": [], "failures": [], "meta": dict(meta)}; t0 = time.time()
    print(f"{fn}: {total} tasks, workers {workers}", flush=True)
    with Pool(workers) as pool:
        for i, (r, err) in enumerate(pool.imap_unordered(_worker, [(fn, t) for t in tasks], chunksize=1), 1):
            if err: res["failures"].append({"task": r, "error": err}); label = f"FAIL {err[:70]}"
            else:
                res["points"].append(r); label = f"sigma={r['sigma']} T={r['T']} q={str(r['q'])[:12]}" + (f" cert={r['sign_certificate_Mplus_minus_Mminus_minus_E']}" if "sign_certificate_Mplus_minus_Mminus_minus_E" in r else "")
            el = time.time()-t0; eta = el/i*(total-i)
            print(f"[{i}/{total}] {i*100//total}% | ETA {int(eta//60)}m{int(eta%60):02d}s | {label}", flush=True)
            if i % 25 == 0: Path(out).write_text(json.dumps(res, indent=1))
    res["points"].sort(key=lambda r: (float(r["T"]), str(r["sigma"])))
    res["meta"].update({"n_points": len(res["points"]), "n_failures": len(res["failures"]), "runtime_seconds": time.time()-t0})
    Path(out).write_text(json.dumps(res, indent=1)); print(f"written {out} in {time.time()-t0:.0f}s", flush=True)

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--zeta", action="store_true"); ap.add_argument("--dh", action="store_true"); ap.add_argument("--arb", action="store_true")
    ap.add_argument("--dps", type=int, default=50); ap.add_argument("--workers", type=int, default=max(1, os.cpu_count()//2)); ap.add_argument("--out", default=None)
    a = ap.parse_args()
    if a.zeta:
        pts = dh.build_zeta_grid()
        run([dict(pt, dps=a.dps, kind_fn="zeta") for pt in pts], "point_mp", a.workers, a.out or str(HERE/"head_masses_zeta.json"),
            {"part": "A'", "function": "zeta", "cutoff": "adaptive (6.3) r=0", "dps": a.dps})
    elif a.dh:
        ref = json.load(open(HERE/"dh_control_reference.json")); T0 = float(ref["T0"])
        pts = dh.build_dh_control_grid(T0)
        run([dict(pt, dps=a.dps, kind_fn="dh") for pt in pts], "point_mp", a.workers, a.out or str(HERE/"head_masses_dh.json"),
            {"part": "A'", "function": "DH", "cutoff": "adaptive (6.3) r=0", "dps": a.dps, "T0": T0})
    elif a.arb:
        zs = cc.zeta_zero_heights(60.0)[:5]
        pts = [{"sigma": "1/64", "T": round(z, 6)} for z in zs] + [{"sigma": "1/4", "T": T} for T in (14.0, 20.0, 30.0, 40.0, 60.0)]
        run([dict(pt, dps=a.dps) for pt in pts], "point_arb", a.workers, a.out or str(HERE/"head_masses_arb.json"),
            {"part": "A'-rigorous", "note": "masses from arb ray-integral balls; certificate of M_+ - M_- - E_N; regression against L_N of the adaptive table", "dps": a.dps})
    else: ap.print_help()
