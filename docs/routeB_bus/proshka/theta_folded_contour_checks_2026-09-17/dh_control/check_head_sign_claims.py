"""Independent verification of the exact algebraic claims of PROSHKA_HEAD_SIGN_STRUCTURAL_ADJUDICATION_2026-09-17
(INDEPENDENT_ANALYTIC_REVIEW: PENDING in that document). PASS/FAIL checks, no prediction registered.

(1)  A_N = 2(conj(u) v^T + conj(v) u^T),  h_N = e* A_N e
(4)  det A_{i,j} = -4 |u_i v_j - u_j v_i|^2
(5)  |l_{m,+} - l_{N,+}| >= 55/(1792 a_m) with m = floor(3N/4), a_m = pi m^2, both cutoff rules
(6)  I_a != 0 and |d_p I_a / I_a - i theta - 1/(2z)| <= (35/36)(|p|+1)/a^2 for a >= 5(|p|+1), z = a e^{2 i theta}
(8)-(9) witness x with sum x_j = 1, sum l_j x_j = -1 gives x* G_N x = -4 exactly
(10) rank A_N = 2 and lambda_pm = 2 Re s +- 2 sqrt(U^2 W^2 - (Im s)^2), s = u* v
(17) det Gtilde_N = |J+J'|^2 - |J-J'|^2 - E_N = h_N - E_N
control: u = (1,1), v = (1,2) gives A = [[4,6],[6,8]], det A = -4 < 0 while e* A e = 24 > 0

  python check_head_sign_claims.py --dps 40
"""
from __future__ import annotations
import argparse, json, sys, time
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import check_contour as cc

def rays_and_derivs(p, theta, N):
    u = []; v = []
    for n in range(1, N+1):
        for sg in (+1, -1):
            f = (lambda x, n=n, sg=sg: cc.ray(n, sg*x, sg*theta))
            d = list(mp.diffs(f, p, 1)); u.append(d[0]); v.append(d[1])
    return u, v

def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--dps", type=int, default=40)
    ap.add_argument("--out", default=str(HERE/"head_sign_claims_check.json"))
    a = ap.parse_args(); mp.mp.dps = a.dps; t0 = time.time()
    out = {"meta": {"dps": a.dps, "source": "PROSHKA_HEAD_SIGN_STRUCTURAL_ADJUDICATION_2026-09-17",
                    "note": "PASS/FAIL algebraic checks of the document's exact claims; no prediction registered"}}

    # ---- control example of section 4
    u0 = [mp.mpc(1), mp.mpc(1)]; v0 = [mp.mpc(1), mp.mpc(2)]
    A0 = [[2*(mp.conj(u0[i])*v0[j] + mp.conj(v0[i])*u0[j]) for j in range(2)] for i in range(2)]
    det0 = A0[0][0]*A0[1][1] - A0[0][1]*A0[1][0]
    he = mp.fsum(A0[i][j] for i in range(2) for j in range(2))
    out["control_section_4"] = {"A": [[mp.nstr(x, 6) for x in r] for r in A0], "det": mp.nstr(det0, 6),
                                "e*Ae": mp.nstr(he, 6), "expected": "A = [[4,6],[6,8]], det = -4, e*Ae = 24",
                                "verdict": "PASS" if abs(det0 + 4) < 1e-30 and abs(he - 24) < 1e-30 else "FAIL"}

    pts = []
    for rule, adaptive in (("diagnostic", None), ("adaptive_6.3_r=0", 0.0)):
        for T, sig in ((14.0, mp.mpf(1)/64), (14.0, mp.mpf(1)/4), (30.0, mp.mpf(1)/8), (60.0, mp.mpf(1)/64), (5.0, mp.mpf(1)/2)):
            cc.ADAPTIVE_R = adaptive
            theta, c, M, N = cc.cutoff(T); theta = mp.mpf(theta)
            p = sig + 1j*mp.mpf(T)
            u, v = rays_and_derivs(p, theta, N)
            idx_pos = {n: 2*(n-1) for n in range(1, N+1)}     # (n, +) sits at 2(n-1)
            m = max(1, (3*N)//4)
            i, j = idx_pos[m], idx_pos[N]
            # (4) two-ray determinant in the free-weight coordinates
            Aij = [[2*(mp.conj(u[k])*v[l] + mp.conj(v[k])*u[l]) for l in (i, j)] for k in (i, j)]
            det_A = Aij[0][0]*Aij[1][1] - Aij[0][1]*Aij[1][0]
            wron = u[i]*v[j] - u[j]*v[i]
            # (5) log-derivative separation
            li, lj = v[i]/u[i], v[j]/u[j]
            am = mp.pi*m*m
            sep, bound5 = abs(li - lj), mp.mpf(55)/(1792*am)
            # (6) uniform log-derivative estimate, applied to a = a_m
            z = am*mp.exp(2j*theta)
            err6 = abs(li - 1j*theta - 1/(2*z)); bound6 = mp.mpf(35)/36*(abs(p) + 1)/am**2
            applicable6 = bool(am >= 5*(abs(p) + 1))
            # (8)-(9) explicit witness
            delta = li - lj
            x = {i: (-1 - lj)/delta, j: (1 + li)/delta}
            sum_x = x[i] + x[j]; sum_lx = li*x[i] + lj*x[j]
            G2 = [[2*(lb + mp.conj(la)) for lb in (li, lj)] for la in (li, lj)]
            xv = [x[i], x[j]]
            form = mp.fsum(mp.conj(xv[k])*G2[k][l]*xv[l] for k in range(2) for l in range(2))
            # (10) rank-2 spectrum
            s = mp.fsum(mp.conj(u[k])*v[k] for k in range(len(u)))
            U = mp.sqrt(mp.fsum(abs(x_)**2 for x_ in u)); Wn = mp.sqrt(mp.fsum(abs(x_)**2 for x_ in v))
            root = mp.sqrt(U**2*Wn**2 - mp.im(s)**2)
            lp, lm = 2*(mp.re(s) + root), 2*(mp.re(s) - root)
            # (17) determinant of the 2x2 reduction equals h_N - E_N
            J = mp.fsum(u); D = mp.fsum(v); h = 4*mp.re(D*mp.conj(J))
            E = sig*cc.e_N_of(T, theta, c, M)
            det_G = abs(J + D)**2 - abs(J - D)**2 - E
            pts.append({"rule": rule, "T": T, "sigma": mp.nstr(sig, 6), "M": M, "N": N, "m": m,
                "check_4_det_A_vs_wronskian": {"det_A": mp.nstr(det_A, 12), "-4|W|^2": mp.nstr(-4*abs(wron)**2, 12),
                    "rel": mp.nstr(abs(det_A + 4*abs(wron)**2)/max(abs(det_A), mp.mpf(10)**-300), 4)},
                "check_5_separation": {"|l_m - l_N|": mp.nstr(sep, 10), "bound 55/(1792 a_m)": mp.nstr(bound5, 10),
                    "ratio": mp.nstr(sep/bound5, 8), "holds": bool(sep >= bound5)},
                "check_6_logderiv": {"applicable a_m >= 5(|p|+1)": applicable6, "a_m": mp.nstr(am, 8),
                    "error": mp.nstr(err6, 10), "bound (35/36)(|p|+1)/a_m^2": mp.nstr(bound6, 10),
                    "holds": bool(err6 <= bound6) if applicable6 else None},
                "check_9_witness": {"sum_x": mp.nstr(sum_x, 10), "sum_l_x": mp.nstr(sum_lx, 10),
                    "x*G x": mp.nstr(mp.re(form), 12), "expected": -4,
                    "holds": bool(abs(mp.re(form) + 4) < mp.mpf(10)**(-a.dps+12))},
                "check_10_spectrum": {"lambda_plus": mp.nstr(lp, 10), "lambda_minus": mp.nstr(lm, 10),
                    "lambda_minus_negative": bool(lm < 0), "lambda_plus_positive": bool(lp > 0)},
                "check_17_det_equals_h_minus_E": {"det_Gtilde": mp.nstr(det_G, 15), "h_N - E_N": mp.nstr(h - E, 15),
                    "rel": mp.nstr(abs(det_G - (h - E))/max(abs(h - E), mp.mpf(10)**-300), 4)},
                "h_N": mp.nstr(h, 12), "E_N": mp.nstr(E, 12)})
    out["points"] = pts
    agg = {}
    agg["check_4"] = "PASS" if all(mp.mpf(q["check_4_det_A_vs_wronskian"]["rel"]) < mp.mpf(10)**(-a.dps+12) for q in pts) else "FAIL"
    agg["check_5"] = "PASS" if all(q["check_5_separation"]["holds"] for q in pts) else "FAIL"
    six = [q for q in pts if q["check_6_logderiv"]["applicable a_m >= 5(|p|+1)"]]
    agg["check_6"] = ("PASS" if all(q["check_6_logderiv"]["holds"] for q in six) else "FAIL") + f" ({len(six)}/{len(pts)} points satisfy the hypothesis)"
    agg["check_9"] = "PASS" if all(q["check_9_witness"]["holds"] for q in pts) else "FAIL"
    agg["check_10"] = "PASS" if all(q["check_10_spectrum"]["lambda_minus_negative"] and q["check_10_spectrum"]["lambda_plus_positive"] for q in pts) else "FAIL"
    agg["check_17"] = "PASS" if all(mp.mpf(q["check_17_det_equals_h_minus_E"]["rel"]) < mp.mpf(10)**(-a.dps+14) for q in pts) else "FAIL"
    agg["control_section_4"] = out["control_section_4"]["verdict"]
    agg["min_separation_ratio_over_bound"] = mp.nstr(min(mp.mpf(q["check_5_separation"]["ratio"]) for q in pts), 6)
    out["verdicts"] = agg
    out["meta"]["runtime_seconds"] = round(time.time()-t0, 1)
    Path(a.out).write_text(json.dumps(out, indent=1))
    print(json.dumps(agg, indent=1))
    for q in pts:
        print(f"{q['rule']:18s} T={q['T']:<5} sigma={q['sigma']:<8} N={q['N']:<3} m={q['m']:<3} "
              f"sep/bound={q['check_5_separation']['ratio']:<12} witness={q['check_9_witness']['x*G x']:<10} "
              f"det17_rel={q['check_17_det_equals_h_minus_E']['rel']}")
    print(f"written {a.out}", flush=True)

if __name__ == "__main__":
    main()
