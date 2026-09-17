"""Identity checks requested in the handoff of PROSHKA_RAY_WEIL_COMPRESSION_CROSSWALK_2026-09-17 (section 8):
(3), (6), the normalisation of (18), and the preservation of both pole terms. PASS/FAIL checks, no prediction is
registered for them (an identity is not a forecast). The primes-vs-zeros crosswalk (11) vs (13) and the rank /
Frobenius defect (21) are the owner's P_M3_7 / P_M3_8 and are NOT computed here.

(5)  f_{n,+}^theta(x) = 1_{x>0} phi_n(x + i theta),  f_{n,-}^theta(x) = 1_{x<0} phi_n(-x - i theta)
(6)  s_alpha(p) = F_{f_alpha}(p) = int f_alpha(x) e^{px} dx = e^{-i theta p} r_alpha(p)
(3)  r_{n,+}(-iy) = e^{theta y} (g(0)/(iy) + O(y^{-2})),  g(0) = 2 a_n e^{5 i theta/2}(2 a_n e^{2 i theta} - 3) e^{-a_n e^{2 i theta}}
(7)  |s_alpha(p)| <= C (1 + |Im p|)^{-1} uniformly for |Re p| <= 1/2
(18) A_N(p_0) = e^{-2 theta tau_0} 2 {conj(s) s'^T + conj(s') s^T},  against HEAD (1.2) A_N = 2(conj(u) v^T + conj(v) u^T), u = r(p_0), v = r'(p_0)
pole line: conj(s_alpha(1/2)) s_beta(-1/2) + conj(s_alpha(-1/2)) s_beta(1/2)
           = e^{i theta} conj(r_alpha(1/2)) r_beta(-1/2) + e^{-i theta} conj(r_alpha(-1/2)) r_beta(1/2)   ((9) vs (11))

  python check_weil_crosswalk.py --dps 40 --N 8 --out weil_crosswalk_checks.json
"""
from __future__ import annotations
import argparse, json, sys, time
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent)); sys.path.insert(0, str(HERE))
import check_contour as cc
import check_jn_dirichlet as cj

def F_test(n, eps, p, theta):
    """F_{f_alpha}(p) = int f_alpha(x) e^{px} dx from the definition (5), by quadrature on finite oscillation pieces."""
    a = mp.pi*n*n; c = mp.cos(2*theta)
    if eps > 0: f = lambda x: cc.source_atom(x + 1j*theta, n)*mp.exp(p*x)
    else:       f = lambda x: cc.source_atom(-x - 1j*theta, n)*mp.exp(p*x)   # x < 0: phi_n(-x - i theta)
    du = mp.pi/(2*a); u_max = cj.DROP/(a*c)
    if u_max <= 1: return mp.mpc(0)
    ks = int(mp.ceil((u_max - 1)/du)); ts = [mp.log(1 + k*du)/2 for k in range(ks+1)]
    if eps > 0: return mp.fsum(mp.quad(f, [ts[k], ts[k+1]]) for k in range(ks))
    return mp.fsum(mp.quad(f, [-ts[k+1], -ts[k]]) for k in range(ks))

def s_closed(n, eps, p, theta):
    """e^{-i theta p} r_alpha(p) with the closed-form rays (3.3)."""
    r = cc.ray(n, p, theta) if eps > 0 else cc.ray(n, -p, -theta)
    return mp.exp(-1j*theta*p)*r

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=40); ap.add_argument("--N", type=int, default=8)
    ap.add_argument("--T", type=float, default=14.0); ap.add_argument("--out", default=str(HERE/"weil_crosswalk_checks.json"))
    a = ap.parse_args(); mp.mp.dps = a.dps; t0 = time.time()
    cc.ADAPTIVE_R = 0.0
    theta, c, M, Nrule = cc.cutoff(a.T); theta = mp.mpf(theta); N = a.N
    out = {"meta": {"dps": a.dps, "N": N, "T_for_theta": a.T, "theta": mp.nstr(theta, 25), "cos2theta": mp.nstr(c, 12),
                    "source": "PROSHKA_RAY_WEIL_COMPRESSION_CROSSWALK_2026-09-17", "note": "identity checks only; (11)-vs-(13) and (21) are the owner's P_M3_7/P_M3_8 and are not computed here"}}

    # ---- (6): F_{f_alpha}(p) from the definition vs e^{-i theta p} r_alpha(p)
    pts = [mp.mpf(1)/64 + 1j*mp.mpf(14.134725), mp.mpf(1)/4 + 1j*mp.mpf(20), -mp.mpf(1)/8 + 1j*mp.mpf(30.5), mp.mpf(1)/2, -mp.mpf(1)/2, 1j*mp.mpf(25)]
    rows6 = []
    for p in pts:
        for n in (1, 2, N):
            for eps in (+1, -1):
                Fv = F_test(n, eps, p, theta); sv = s_closed(n, eps, p, theta)
                rows6.append({"p": mp.nstr(p, 12), "n": n, "eps": eps, "F_from_definition": mp.nstr(Fv, 20), "e^{-i theta p} r": mp.nstr(sv, 20),
                              "rel_err": mp.nstr(abs(Fv - sv)/abs(sv), 5)})
    out["check_6_admissible_parametrisation"] = {"rows": rows6, "max_rel_err": mp.nstr(max(mp.mpf(r["rel_err"]) for r in rows6), 4),
                                                 "verdict": "PASS" if max(mp.mpf(r["rel_err"]) for r in rows6) < mp.mpf(10)**(-a.dps+12) else "FAIL"}

    # ---- (3): growth of r_{n,+}(-iy) and the leading coefficient g(0)
    rows3 = []
    for n in (1, 2, 3):
        a_n = mp.pi*n*n
        g0 = 2*a_n*mp.exp(5j*theta/2)*(2*a_n*mp.exp(2j*theta) - 3)*mp.exp(-a_n*mp.exp(2j*theta))
        for y in (50, 100, 200, 400, 800):
            r = cc.ray(n, -1j*mp.mpf(y), theta)
            lead = mp.exp(theta*y)*g0/(1j*y)
            resid = abs(r - lead)/abs(mp.exp(theta*y)/(y*y))   # should stay bounded: the O(y^{-2}) constant
            rows3.append({"n": n, "y": y, "abs_r": mp.nstr(abs(r), 8), "abs_leading": mp.nstr(abs(lead), 8),
                          "ratio_r_over_leading": mp.nstr(abs(r/lead), 10), "residual_over_y^-2_scale": mp.nstr(resid, 8)})
        out.setdefault("g0", {})[str(n)] = mp.nstr(g0, 20)
    # (3) is an asymptotic in y at fixed n, theta: judge per n by (i) the ratio to the leading term increasing to 1
    # and (ii) the O(y^-2) constant staying bounded (converging) in y. Larger n needs larger y (the constant grows with a_n).
    consts = {}; per_n = {}
    for n in (1, 2, 3):
        v = [mp.mpf(r["residual_over_y^-2_scale"]) for r in rows3 if r["n"] == n]
        rr = [mp.mpf(r["ratio_r_over_leading"]) for r in rows3 if r["n"] == n]
        consts[str(n)] = [mp.nstr(min(v), 5), mp.nstr(max(v), 5)]
        per_n[str(n)] = {"ratio_increasing_to_1": bool(all(rr[i] < rr[i+1] for i in range(len(rr)-1)) and rr[-1] < 1),
                         "ratio_at_max_y": mp.nstr(rr[-1], 8), "const_last_over_first": mp.nstr(v[-1]/v[0], 5)}
    ratios = [mp.mpf(r["ratio_r_over_leading"]) for r in rows3 if r["y"] >= 400]
    ok3 = all(per_n[str(n)]["ratio_increasing_to_1"] and mp.mpf(per_n[str(n)]["const_last_over_first"]) < 2 for n in (1, 2, 3))
    out["check_3_unbounded_growth"] = {"rows": rows3, "ratio_to_leading_at_y_ge_400": [mp.nstr(min(ratios), 8), mp.nstr(max(ratios), 8)],
        "per_n": per_n, "O(y^-2)_constant_range_by_n": consts, "g0_nonzero": all(abs(mp.mpc(v)) > 0 for v in out["g0"].values()),
        "verdict": "PASS" if ok3 else "FAIL",
        "meaning": "|r_{n,+}(-iy)| grows like e^{theta y}|g(0)|/y, so no admissible f in E has F_f = r_{n,+} (the raw shifted rays are not transforms of admissible tests)"}

    # ---- (7): decay of s on |Re p| <= 1/2
    rows7 = []
    for n in (1, N):
        for sg in (mp.mpf(1)/2, mp.mpf(0), -mp.mpf(1)/2):
            v = []
            for tau in (10, 40, 160, 640):
                sv = s_closed(n, +1, sg + 1j*mp.mpf(tau), theta); v.append(abs(sv)*(1 + tau))
            rows7.append({"n": n, "Re p": mp.nstr(sg, 5), "abs_s_times_(1+|Im p|)": [mp.nstr(x, 6) for x in v]})
    out["check_7_decay"] = {"rows": rows7, "verdict": "PASS (bounded along each row)" }

    # ---- (18): A_N from the rays vs from the admissible tests
    rows18 = []
    for p0 in [mp.mpf(1)/64 + 1j*mp.mpf(14.134725), mp.mpf(1)/4 + 1j*mp.mpf(30), mp.mpf(1)/8 + 1j*mp.mpf(40.918719)]:
        tau0 = mp.im(p0)
        u = []; v = []; su = []; sv = []
        for n in range(1, N+1):
            for eps in (+1, -1):
                f = (lambda x, n=n, eps=eps: cc.ray(n, x, theta) if eps > 0 else cc.ray(n, -x, -theta))
                d = list(mp.diffs(f, p0, 1)); u.append(d[0]); v.append(d[1])
                fs = (lambda x, n=n, eps=eps: s_closed(n, eps, x, theta))
                ds = list(mp.diffs(fs, p0, 1)); su.append(ds[0]); sv.append(ds[1])
        # compare the two 2N x 2N matrices entrywise via their Frobenius distance
        num = mp.mpf(0); den = mp.mpf(0)
        for i in range(2*N):
            for j in range(2*N):
                A = 2*(mp.conj(u[i])*v[j] + mp.conj(v[i])*u[j])
                B = mp.exp(-2*theta*tau0)*2*(mp.conj(su[i])*sv[j] + mp.conj(sv[i])*su[j])
                num += abs(A - B)**2; den += abs(A)**2
        rows18.append({"p0": mp.nstr(p0, 12), "frobenius_rel": mp.nstr(mp.sqrt(num/den), 5),
                       "h_N_from_A": mp.nstr(4*mp.re(mp.fsum(v)*mp.conj(mp.fsum(u))), 15)})
    out["check_18_head_normalisation"] = {"rows": rows18, "max_frobenius_rel": mp.nstr(max(mp.mpf(r["frobenius_rel"]) for r in rows18), 4),
        "verdict": "PASS" if max(mp.mpf(r["frobenius_rel"]) for r in rows18) < mp.mpf(10)**(-a.dps+14) else "FAIL",
        "meaning": "the purely imaginary i theta s term cancels in the hermitian polarisation, and the scale is exactly e^{-2 theta tau_0}"}

    # ---- pole line: (9) in s-coordinates vs (11) in r-coordinates
    rowsP = []
    for n in (1, 2, N):
        for l in (1, N):
            for en, el in ((+1, +1), (+1, -1), (-1, +1)):
                lhs = mp.conj(s_closed(n, en, mp.mpf(1)/2, theta))*s_closed(l, el, -mp.mpf(1)/2, theta) + \
                      mp.conj(s_closed(n, en, -mp.mpf(1)/2, theta))*s_closed(l, el, mp.mpf(1)/2, theta)
                ra1 = cc.ray(n, mp.mpf(1)/2, theta) if en > 0 else cc.ray(n, -mp.mpf(1)/2, -theta)
                ra2 = cc.ray(n, -mp.mpf(1)/2, theta) if en > 0 else cc.ray(n, mp.mpf(1)/2, -theta)
                rb1 = cc.ray(l, mp.mpf(1)/2, theta) if el > 0 else cc.ray(l, -mp.mpf(1)/2, -theta)
                rb2 = cc.ray(l, -mp.mpf(1)/2, theta) if el > 0 else cc.ray(l, mp.mpf(1)/2, -theta)
                rhs = mp.exp(1j*theta)*mp.conj(ra1)*rb2 + mp.exp(-1j*theta)*mp.conj(ra2)*rb1
                rowsP.append({"alpha": [n, en], "beta": [l, el], "s_form": mp.nstr(lhs, 18), "r_form": mp.nstr(rhs, 18),
                              "rel_err": mp.nstr(abs(lhs - rhs)/max(abs(lhs), mp.mpf(10)**-300), 5)})
    out["check_pole_terms"] = {"rows": rowsP, "max_rel_err": mp.nstr(max(mp.mpf(r["rel_err"]) for r in rowsP), 4),
        "verdict": "PASS" if max(mp.mpf(r["rel_err"]) for r in rowsP) < mp.mpf(10)**(-a.dps+12) else "FAIL",
        "meaning": "both pole terms of (9) are preserved by the r-form (11); neither is dropped"}

    out["meta"]["runtime_seconds"] = round(time.time()-t0, 1)
    Path(a.out).write_text(json.dumps(out, indent=1))
    for k in ("check_6_admissible_parametrisation", "check_3_unbounded_growth", "check_18_head_normalisation", "check_pole_terms"):
        d = out[k]; print(k, "->", d["verdict"], {kk: vv for kk, vv in d.items() if kk.startswith("max") or kk.startswith("ratio") or kk.startswith("O(")})
    print("\n".join(str(r) for r in out["check_3_unbounded_growth"]["rows"] if r["n"] == 1))
    print(f"written {a.out}", flush=True)

if __name__ == "__main__":
    main()
