"""The signed cluster correction E_coh of PROSHKA_VERDICT_COHERENT_MEANS_SIGN_TRANSFER_2026-09-18, measured on the
real gamma rays in arb.

    alpha = tau_X = X_t/X,   beta = tau_Y = Y_t/Y,   m = (Re alpha + Re beta)/2
    h_N/4 = m(|X|^2 - |Y|^2) + E_coh                                        (identity, checked here)
    E_coh = ((Re alpha - Re beta)/2)|X+Y|^2 - (Im alpha + Im beta) Im(X conj Y)
    kappa = M_+ / (4 m |X|^2),      epsilon = -E_coh / (sigma m |X|^2)

Proshka's sufficient budget (his section 4), to be tested here on the real rays:
    m >= 3/20,   E_coh >= -(1/5) sigma m |X|^2  (i.e. epsilon <= 1/5),   0 < kappa <= 6/5
    ==>  G >= (5/6)[2(1 - e^{-3/10}) - 1/5] > 421/1614 > 1/4.

Convention note (verified against his table): with I_n^-(p) = I_n(-p, -theta) as coded, the chain rule gives
d_p[I_n^-] = -(dI_n)(-p,-theta), so beta = -Yt_code/Y, where Yt_code is what the ray machinery returns.

  python check_coherent_correction.py --dps 80 --workers 8 --out coherent_correction_arb.json
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

def point(task):
    dps = task["dps"]; acb, arb = cc._arb_setup(dps)
    cc.ADAPTIVE_R = 0.0
    T = arb(task["T"]); theta = arb.pi()/4 - 1/(T + 1); c = (2*theta).cos()
    fr = Fraction(task["sigma"]); sigma = arb(fr.numerator)/fr.denominator
    _, _, M, N = cc.cutoff(float(task["T"])); p = acb(sigma, T); L = arb(4); t0 = time.time()
    X = acb(0); Y = acb(0); Xt = acb(0); Yt = acb(0); u = []; v = []
    for n in range(1, N+1):
        a = arb.pi()*n*n
        tb = cc._tail_bound_arb(arb, theta, T, sigma, a, c, L).upper(); ball = acb(arb(0, tb), arb(0, tb))
        rp = cc._ray_integrals_arb(acb, arb, p, theta, a, L, +1); rm = cc._ray_integrals_arb(acb, arb, p, theta, a, L, -1)
        X = X + rp[0] + ball; Xt = Xt + rp[1] + ball
        Y = Y + rm[0] + ball; Yt = Yt + rm[1] + ball
        u += [rp[0] + ball, rm[0] + ball]; v += [rp[1] + ball, rm[1] + ball]
    mm = hm.masses_from(u, v, conj=lambda z: z.conjugate(), re=lambda z: z.real if isinstance(z, acb) else z,
                        im=lambda z: z.imag if isinstance(z, acb) else arb(0), sqrt=lambda x: x.sqrt(),
                        fsum=lambda xs: sum(xs[1:], xs[0]))
    Mp = mm["M_plus"]
    alpha = Xt/X; beta = (acb(0) - Yt)/Y
    m_mean = (alpha.real + beta.real)/2
    X2 = (X*X.conjugate()).real; Y2 = (Y*Y.conjugate()).real
    J = X + Y; J2 = (J*J.conjugate()).real
    ImXY = (X*Y.conjugate()).imag
    E_coh = (alpha.real - beta.real)/2*J2 - (alpha.imag + beta.imag)*ImXY
    Jp = Xt + Yt; h = 4*(Jp*J.conjugate()).real
    ident = h/4 - (m_mean*(X2 - Y2) + E_coh)                     # must be 0
    kappa = Mp/(4*m_mean*X2)
    eps = (acb(0).real - E_coh)/(sigma*m_mean*X2)
    G = h/(sigma*Mp)
    def s(x, d=16):
        try: return x.str(d, radius=False)
        except Exception: return str(x)
    return {"sigma": task["sigma"], "T": task["T"], "N": N,
            "m": s(m_mean), "Re_alpha": s(alpha.real), "Re_beta": s(beta.real),
            "Im_alpha": s(alpha.imag), "Im_beta": s(beta.imag),
            "E_coh": s(E_coh), "epsilon": s(eps), "kappa": s(kappa), "G": s(G),
            "identity_residual_over_h": s(abs(ident)/abs(h), 6),
            "budget_m_ge_3/20": bool((m_mean - arb(3)/20).lower() > 0),
            "budget_eps_le_1/5": bool((arb(1)/5 - eps).lower() > 0),
            "budget_kappa_le_6/5": bool((arb(6)/5 - kappa).lower() > 0 and kappa.lower() > 0),
            "E_coh_negative": bool(E_coh.upper() < 0),
            "runtime_seconds": round(time.time()-t0, 2)}

def _worker(t):
    try: return point(t), None
    except Exception as e: return t, repr(e)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=80); ap.add_argument("--workers", type=int, default=max(1, os.cpu_count()//2))
    ap.add_argument("--out", default=str(HERE/"coherent_correction_arb.json"))
    a = ap.parse_args()
    T0 = float(mp.sqrt(20))
    Ts = [round(T0 + 0.25*k, 6) for k in range(0, 23)] + [12.0, 14.75, 16.0, 20.0, 25.0, 30.0, 40.0, 60.0, 80.0]
    sigmas = ["1/64", "1/32", "1/16", "1/8", "1/4", "3/8", "1/2"]
    tasks = [{"sigma": s, "T": T, "dps": a.dps} for T in Ts for s in sigmas]
    total = len(tasks); t0 = time.time(); res = []; fails = []
    print(f"coherent correction: {total} points, arb dps {a.dps}, workers {a.workers}", flush=True)
    with Pool(a.workers) as pool:
        for i, (r, err) in enumerate(pool.imap_unordered(_worker, tasks, chunksize=1), 1):
            if err: fails.append({"task": r, "error": err}); label = f"FAIL {err[:60]}"
            else:
                res.append(r)
                flags = ("m" if r["budget_m_ge_3/20"] else "-") + ("e" if r["budget_eps_le_1/5"] else "-") + ("k" if r["budget_kappa_le_6/5"] else "-")
                label = f"sigma={r['sigma']} T={r['T']} eps={r['epsilon'][:10]} kappa={r['kappa'][:8]} [{flags}]"
            if i % 20 == 0 or i == total:
                el = time.time()-t0; eta = el/i*(total-i)
                print(f"[{i}/{total}] {i*100//total}% | ETA {int(eta//60)}m{int(eta%60):02d}s | {label}", flush=True)
    res.sort(key=lambda r: (float(Fraction(r["sigma"])), r["T"]))
    def f(x): return mp.mpf(x)
    worst_eps = max(res, key=lambda r: f(r["epsilon"])); worst_k = max(res, key=lambda r: f(r["kappa"]))
    worst_m = min(res, key=lambda r: f(r["m"])); worst_E = min(res, key=lambda r: f(r["E_coh"]))
    out = {"meta": {"source": "PROSHKA_VERDICT_COHERENT_MEANS_SIGN_TRANSFER_2026-09-18", "dps": a.dps,
                    "n_points": len(res), "n_failures": len(fails), "runtime_seconds": round(time.time()-t0, 1),
                    "identity_max_residual": mp.nstr(max(f(r["identity_residual_over_h"]) for r in res), 4),
                    "budget": "m >= 3/20, epsilon <= 1/5, 0 < kappa <= 6/5  ==>  G > 421/1614 > 1/4"},
           "verdict": {"m_ge_3/20": f"{sum(1 for r in res if r['budget_m_ge_3/20'])}/{len(res)}",
                       "epsilon_le_1/5": f"{sum(1 for r in res if r['budget_eps_le_1/5'])}/{len(res)}",
                       "kappa_le_6/5": f"{sum(1 for r in res if r['budget_kappa_le_6/5'])}/{len(res)}",
                       "all_three": f"{sum(1 for r in res if r['budget_m_ge_3/20'] and r['budget_eps_le_1/5'] and r['budget_kappa_le_6/5'])}/{len(res)}",
                       "E_coh_negative_at": f"{sum(1 for r in res if r['E_coh_negative'])}/{len(res)}",
                       "max_epsilon": {"value": worst_eps["epsilon"], "sigma": worst_eps["sigma"], "T": worst_eps["T"]},
                       "max_kappa": {"value": worst_k["kappa"], "sigma": worst_k["sigma"], "T": worst_k["T"]},
                       "min_m": {"value": worst_m["m"], "sigma": worst_m["sigma"], "T": worst_m["T"]},
                       "min_E_coh": {"value": worst_E["E_coh"], "sigma": worst_E["sigma"], "T": worst_E["T"]}},
           "points": res, "failures": fails}
    Path(a.out).write_text(json.dumps(out, indent=1))
    print(json.dumps(out["verdict"], indent=1)); print("identity max residual:", out["meta"]["identity_max_residual"])
    print(f"written {a.out}", flush=True)

if __name__ == "__main__":
    main()
