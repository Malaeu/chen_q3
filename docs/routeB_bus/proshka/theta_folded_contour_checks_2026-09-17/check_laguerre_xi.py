"""Rigorous (python-flint / arb) Laguerre inequality for xi on the critical line.

X(T) = F(iT) = xi(1/2+iT) is real. L1[X](T) = X'^2 - X X'' is the sigma->0 slope of
H(sigma+iT)/(4 sigma). Under RH (xi in Laguerre-Polya) L1 >= 0 for all T; this script
certifies the sign at finite T only. Derivatives are computed by the Cauchy integral
F^{(j)}(p) = j!/(2 pi r^j) int_0^{2pi} F(p + r e^{it}) e^{-ijt} dt with acb.integral
(rigorous error balls), F from acb zeta/gamma. No mpmath, no floating point in the certificate.

    python check_laguerre_xi.py --Tmin 4.5 --Tmax 60 --Tstep 0.25 --zeros --dps 60 --out laguerre_xi_arb.json
"""
from __future__ import annotations
import argparse, json, os, time
from multiprocessing import Pool
from pathlib import Path

def zeta_zero_heights(Tmax):
    import mpmath as mp
    mp.mp.dps = 30
    zs = []; k = 1
    while True:
        g = mp.zetazero(k).imag
        if g > Tmax: break
        zs.append(float(mp.nstr(g, 20))); k += 1
    return zs

def point(task):
    from flint import acb, arb, ctx
    ctx.dps = task["dps"]
    T = arb(task["T"]); p = acb(0, T); r = arb(1)/2
    t0 = time.time()
    def F(w):
        s = acb(arb(1)/2, 0) + w
        return s*(s-1)*(arb.pi()**(-s/2))*(s/2).gamma()*s.zeta()/2
    def deriv(j):
        def f(t, analytic):
            w = p + r*(acb(0, 1)*t).exp()
            return F(w)*(acb(0, -j)*t).exp()
        I = acb.integral(f, 0, 2*arb.pi())
        fact = 1
        for k in range(2, j+1): fact *= k
        return I*fact/(2*arb.pi()*r**j)
    F0, F1, F2 = deriv(0), deriv(1), deriv(2)
    X = F0.real; Xp = (acb(0, 1)*F1).real; Xpp = (-F2).real
    leak = max(abs(F0.imag).upper(), abs((acb(0, 1)*F1).imag).upper(), abs(F2.imag).upper())
    L1 = Xp*Xp - X*Xpp
    def cert(x):
        if x.lower() > 0: return "POSITIVE"
        if x.upper() < 0: return "NEGATIVE"
        return "UNDECIDED"
    return {"T": task["T"], "kind": task["kind"], "gamma": task["gamma"], "dps": task["dps"],
            "X": str(X), "X_prime": str(Xp), "X_double_prime": str(Xpp), "imag_leak": str(leak),
            "L1_xi": str(L1), "L1_xi_mid": str(L1.mid()), "L1_xi_rad": str(L1.rad()),
            "sign_certificate_L1_xi": cert(L1), "runtime_seconds": time.time()-t0,
            "certificate_scope": "finite point only; no continuum claim"}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--Tmin", type=float, default=4.5); ap.add_argument("--Tmax", type=float, default=60.0)
    ap.add_argument("--Tstep", type=float, default=0.25); ap.add_argument("--zeros", action="store_true")
    ap.add_argument("--zero-offsets", dest="zero_offsets", default="-0.05,0,0.05")
    ap.add_argument("--dps", type=int, default=60); ap.add_argument("--workers", type=int, default=max(1, os.cpu_count()//4))
    ap.add_argument("--out", default="laguerre_xi_arb.json")
    a = ap.parse_args()
    Ts = []; k = 0
    while True:
        T = a.Tmin + k*a.Tstep
        if T > a.Tmax + 1e-12: break
        Ts.append({"T": round(T, 6), "kind": "grid", "gamma": None, "dps": a.dps}); k += 1
    if a.zeros:
        for g in zeta_zero_heights(a.Tmax):
            for off in (float(x) for x in a.zero_offsets.split(",")):
                if a.Tmin <= g+off <= a.Tmax:
                    Ts.append({"T": round(g+off, 6), "kind": "zero", "gamma": g, "dps": a.dps})
    total = len(Ts); res = []; t0 = time.time()
    print(f"laguerre xi: {total} T values, dps {a.dps}, workers {a.workers}", flush=True)
    with Pool(a.workers) as pool:
        for i, r in enumerate(pool.imap_unordered(point, Ts), 1):
            res.append(r); el = time.time()-t0; eta = el/i*(total-i)
            print(f"[{i}/{total}] {i*100//total}% | ETA {int(eta//60)}m{int(eta%60):02d}s | T={r['T']} L1_xi={r['L1_xi_mid'][:14]} cert={r['sign_certificate_L1_xi']}", flush=True)
    res.sort(key=lambda r: float(r["T"]))
    out = {"meta": {"Tmin": a.Tmin, "Tmax": a.Tmax, "Tstep": a.Tstep, "zeros": a.zeros, "dps": a.dps,
                    "method": "Cauchy integral radius 1/2 via acb.integral; F=xi(1/2+p) from acb zeta/gamma",
                    "n": total, "runtime_seconds": time.time()-t0,
                    "summary": {"POSITIVE": sum(1 for r in res if r["sign_certificate_L1_xi"] == "POSITIVE"),
                                "NEGATIVE": sum(1 for r in res if r["sign_certificate_L1_xi"] == "NEGATIVE"),
                                "UNDECIDED": sum(1 for r in res if r["sign_certificate_L1_xi"] == "UNDECIDED")},
                    "certificate_scope": "finite T values only"},
           "points": res}
    Path(a.out).write_text(json.dumps(out, indent=1))
    print("summary:", json.dumps(out["meta"]["summary"]), flush=True)
    print(f"written {a.out}", flush=True)

if __name__ == "__main__":
    main()
