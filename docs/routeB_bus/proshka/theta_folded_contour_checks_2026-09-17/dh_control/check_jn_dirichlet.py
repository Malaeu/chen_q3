"""Two checks on PROSHKA_JN_ZERO_FREE_STRIP_ATTEMPT_2026-09-17 (identity (9), zeros of d_N vs J_N).

(a) identity (9):  J_N(p;theta) = B(p) d_N(s) + E_N(p;theta),  s = p + 1/2,
      d_N(s) = sum_{n<=N} n^{-s},  B(p) = s(s-1)/2 pi^{-s/2} Gamma(s/2),
      E_N = int_0^inf g_N(t) e^{-pt} dt - int_{-inf}^0 g_N(t) e^{pt} dt - V_N,
      V_N = int_0^{i theta} (g_N(z) - g_N(-z)) e^{pz} dz = i int_0^theta (g_N(iu) - g_N(-iu)) e^{ipu} du,
      g_N = sum_{n<=N} phi_n,  phi_n(z) = (4 a_n^2 e^{9z/2} - 6 a_n e^{5z/2}) e^{-a_n e^{2z}},  a_n = pi n^2.
    LHS = check_contour.head (closed-form rays (3.3)); LHS is also recomputed by direct quadrature of (1).
    RHS: all integrals by mpmath quad at dps 50; target 30 agreeing digits at 20 random strip points
    (T uniform in [1,40], tau uniform in [T-1,T+1], sigma = Re p uniform in (0, 3/2]; N = M_0(T)-1, theta = theta_T, rule (2)).

(b) zeros in windows s in [1/2,2] x [T0-1,T0+1], T0 in {14,20,30,40}, N = M_0(T0)-1, theta0 = theta(T0):
      d_N(s): winding number on the s-rectangle boundary, zeros localized by quadtree subdivision + findroot;
      J_N(p;theta0), p = s - 1/2: winding on the symmetric p-rectangle [-3/2,3/2] x [T0-1,T0+1] (total count),
      on-line zeros of the real function J_N(i tau) by sign changes (refined by bisection), off-line = total - on-line;
      cross-check: winding on [0.01, 3/2] x [T0-1,T0+1] directly.

  python check_jn_dirichlet.py --dps 50 --seed 20260918 --workers 6 --out jn_dirichlet.json
"""
from __future__ import annotations
import argparse, json, os, random, sys, time
from multiprocessing import Pool
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import check_contour as cc

T0S = [14.0, 20.0, 30.0, 40.0]
EPS = 0.01

def frozen(T0):
    cc.ADAPTIVE_R = 0.0
    theta0, c0, M0, N0 = cc.cutoff(T0)
    return mp.mpf(theta0), c0, M0, N0

def g_N(z, N):
    return mp.fsum(cc.source_atom(z, n) for n in range(1, N+1))

def d_N(s, N):
    return mp.fsum(mp.power(n, -s) for n in range(1, N+1))

def B_of(p):
    s = p + mp.mpf(1)/2
    return s*(s-1)/2*mp.power(mp.pi, -s/2)*mp.gamma(s/2)

DROP = 250   # a piece whose atom magnitude bound is below e^{-DROP} (times a polynomial factor) is skipped

def ray_direct(n, p, theta, direct_n_max):
    """I_n(p,theta) = int_0^inf phi_n(t+i theta) e^{p(t+i theta)} dt by quadrature (definition (1)).
    The integrand oscillates with phase a e^{2t} sin(2 theta); pieces of phase <= pi/2 in u = e^{2t}, cut where
    a e^{2t} cos(2 theta) > DROP (magnitude e^{-DROP})."""
    a = mp.pi*n*n; c = mp.cos(2*theta)
    f = lambda t: cc.source_atom(t + 1j*theta, n)*mp.exp(p*(t + 1j*theta))
    du = mp.pi/(2*a); u_max = DROP/(a*c)
    if u_max <= 1: return mp.mpc(0)
    ks = int(mp.ceil((u_max - 1)/du))
    ts = [mp.log(1 + k*du)/2 for k in range(ks+1)]
    return mp.fsum(mp.quad(f, [ts[k], ts[k+1]]) for k in range(ks))

def V_atom(n, p, theta):
    """i int_0^theta (phi_n(iu) - phi_n(-iu)) e^{ipu} du; phase a sin(2u) (derivative <= 2a), pieces of length pi/(4a),
    skipped where a cos(2u) > DROP on the whole piece (cos decreasing on [0, theta], theta < pi/4)."""
    a = mp.pi*n*n
    f = lambda u: (cc.source_atom(1j*u, n) - cc.source_atom(-1j*u, n))*mp.exp(1j*p*u)
    du = mp.pi/(4*a); ks = max(4, int(mp.ceil(theta/du))); h = theta/ks
    tot = mp.mpc(0)
    for k in range(ks):
        u1 = (k+1)*h
        if a*mp.cos(2*u1) > DROP: continue
        tot += mp.quad(f, [k*h, u1])
    return 1j*tot

def identity_point(task):
    mp.mp.dps = task["dps"]
    T = task["T"]; theta, c, M, N = frozen(T)
    p = mp.mpf(task["sigma"]) + 1j*mp.mpf(task["tau"]); t0 = time.time()
    lhs = cc.head(p, theta, N)
    # closed-form rays (3.3) vs direct quadrature of (1), atoms n <= 2 only (the large-n integrands oscillate ~a e^{2t} times)
    ray_cmp = []
    for n in (1, 2):
        for sg in (+1, -1):
            cf = cc.ray(n, sg*p, sg*theta); dq = ray_direct(n, sg*p, sg*theta, 2)
            ray_cmp.append({"n": n, "sign": sg, "rel_err": mp.nstr(abs(cf-dq)/abs(cf), 5)})
    s = p + mp.mpf(1)/2
    main = B_of(p)*d_N(s, N)
    # real-axis integrals by quadrature on finite pieces: on [0, inf) the atom is e^{-a e^{2t}} (cut where a e^{2t} > DROP,
    # an infinite upper limit makes mpmath evaluate exp of numbers with astronomically large exponents), on (-inf, 0] the
    # integrand is O(e^{(5/2+sigma)t}) (cut at t = -60: below e^{-150}). Cross-check: closed forms via incomplete gamma,
    # int_0^inf = a^{p/2-1/4}[2 Gamma(9/4-p/2, a) - 3 Gamma(5/4-p/2, a)], int_{-inf}^0 = a^{-p/2-1/4}[2 gamma(9/4+p/2, a) - 3 gamma(5/4+p/2, a)].
    def Ipos_atom(n):
        a = mp.pi*n*n; tmax = mp.log(DROP/a)/2
        if tmax <= 0: return mp.mpc(0)
        pts = [x for x in [0, 0.1, 0.25, 0.5, 1, 1.5, 2, 3] if x < tmax] + [tmax]
        return mp.quad(lambda t: cc.source_atom(t, n)*mp.exp(-p*t), pts)
    def Ineg_atom(n):
        return mp.quad(lambda t: cc.source_atom(t, n)*mp.exp(p*t), [-60, -30, -15, -8, -4, -2, -1, -0.5, -0.25, 0])
    Ipos = mp.fsum(Ipos_atom(n) for n in range(1, N+1))
    Ineg = mp.fsum(Ineg_atom(n) for n in range(1, N+1))
    Ipos_cf = mp.fsum(a**(p/2-mp.mpf(1)/4)*(2*mp.gammainc(mp.mpf(9)/4-p/2, a, mp.inf) - 3*mp.gammainc(mp.mpf(5)/4-p/2, a, mp.inf))
                      for a in (mp.pi*n*n for n in range(1, N+1)))
    Ineg_cf = mp.fsum(a**(-p/2-mp.mpf(1)/4)*(2*mp.gammainc(mp.mpf(9)/4+p/2, 0, a) - 3*mp.gammainc(mp.mpf(5)/4+p/2, 0, a))
                      for a in (mp.pi*n*n for n in range(1, N+1)))
    V = mp.fsum(V_atom(n, p, theta) for n in range(1, N+1))
    E = Ipos - Ineg - V
    rhs = main + E
    rel = abs(lhs - rhs)/abs(lhs)
    digits = float(-mp.log10(rel)) if rel > 0 else float(task["dps"])
    return {"T": T, "sigma": task["sigma"], "tau": task["tau"], "N": N, "theta": mp.nstr(theta, 20),
            "J_N_closed_form": mp.nstr(lhs, 35), "rhs_BdN_plus_EN": mp.nstr(rhs, 35),
            "B_dN": mp.nstr(main, 35), "E_N": mp.nstr(E, 35), "I_pos": mp.nstr(Ipos, 20), "I_neg": mp.nstr(Ineg, 20), "V_N": mp.nstr(V, 20),
            "I_pos_quad_vs_gamma_rel": mp.nstr(abs(Ipos-Ipos_cf)/abs(Ipos_cf), 5), "I_neg_quad_vs_gamma_rel": mp.nstr(abs(Ineg-Ineg_cf)/abs(Ineg_cf), 5),
            "abs_E_over_abs_J": mp.nstr(abs(E)/abs(lhs), 8), "abs_BdN_over_abs_J": mp.nstr(abs(main)/abs(lhs), 8),
            "rel_err_identity": mp.nstr(rel, 6), "digits_agree": round(digits, 1), "pass_30_digits": bool(digits >= 30),
            "ray_closed_form_vs_direct_n_le_2": ray_cmp, "runtime_seconds": round(time.time()-t0, 1)}

def winding_rect(f, rect, h_horiz=0.01, h_vert=0.02):
    """Winding number of f around the rectangle [x_lo,x_hi] x [y_lo,y_hi] (counter-clockwise), phase unwrapping with
    step control (every phase step < pi/2, else halve). Returns (w, max_step, n_eval)."""
    x_lo, x_hi, y_lo, y_hi = rect
    def side(g, a, b, h0):
        n = max(2, int(abs(b-a)/h0)); hs = (b-a)/n
        xs = [a + k*hs for k in range(n+1)]; vals = [g(x) for x in xs]
        i = 0; ms = 0
        while i < len(vals)-1:
            d = mp.arg(vals[i+1]/vals[i])
            if abs(d) > mp.pi/2 and abs(xs[i+1]-xs[i]) > 1e-7:
                xm = (xs[i]+xs[i+1])/2; xs.insert(i+1, xm); vals.insert(i+1, g(xm)); continue
            ms = max(ms, abs(d)); i += 1
        return vals, ms
    total = mp.mpf(0); maxstep = 0; nev = 0
    for g, a, b, h0 in [(lambda x: f(x, y_lo), x_lo, x_hi, h_horiz), (lambda y: f(x_hi, y), y_lo, y_hi, h_vert),
                        (lambda x: f(x, y_hi), x_hi, x_lo, h_horiz), (lambda y: f(x_lo, y), y_hi, y_lo, h_vert)]:
        vals, ms = side(g, a, b, h0); nev += len(vals); maxstep = max(maxstep, ms)
        total += mp.fsum(mp.arg(vals[i+1]/vals[i]) for i in range(len(vals)-1))
    return total/(2*mp.pi), maxstep, nev

def localize(f, rect, count, min_size=0.02, depth=0):
    """Quadtree: split until each box holds <= 1 zero and is small, then findroot from the centre."""
    x_lo, x_hi, y_lo, y_hi = rect
    if count == 0: return []
    if (x_hi - x_lo) <= min_size and (y_hi - y_lo) <= min_size or depth > 12:
        z0 = mp.mpc((x_lo+x_hi)/2, (y_lo+y_hi)/2)
        try:
            z = mp.findroot(lambda w: f(mp.re(w), mp.im(w)), z0, solver="muller", tol=mp.mpf(10)**(-mp.mp.dps+8), maxsteps=60)
            return [{"zero": mp.nstr(z, 25), "re": float(mp.re(z)), "im": float(mp.im(z)), "abs_f": mp.nstr(abs(f(mp.re(z), mp.im(z))), 5), "box_count": count}]
        except Exception as e:
            return [{"zero": None, "box": rect, "box_count": count, "error": repr(e)[:80]}]
    xm = (x_lo+x_hi)/2; ym = (y_lo+y_hi)/2
    out = []
    for sub in [(x_lo, xm, y_lo, ym), (xm, x_hi, y_lo, ym), (x_lo, xm, ym, y_hi), (xm, x_hi, ym, y_hi)]:
        w, ms, _ = winding_rect(f, sub, h_horiz=min(0.01, (sub[1]-sub[0])/10), h_vert=min(0.02, (sub[3]-sub[2])/10))
        k = int(mp.nint(w))
        if abs(w - k) > 1e-6:  # boundary hits a zero: nudge the box
            out.append({"zero": None, "box": sub, "winding_raw": mp.nstr(w, 8), "error": "non-integer winding (zero near sub-box boundary)"}); continue
        out.extend(localize(f, sub, k, min_size, depth+1))
    return out

def zeros_dN(task):
    mp.mp.dps = task["dps"]; T0 = task["T0"]; theta0, c0, M0, N0 = frozen(T0); t0 = time.time()
    rect = [0.5, 2.0, T0-1, T0+1]
    f = lambda x, y: d_N(mp.mpc(x, y), N0)
    w, ms, nev = winding_rect(f, rect)
    k = int(mp.nint(w))
    zs = localize(f, rect, k) if k > 0 else []
    found = [z for z in zs if z.get("zero")]
    return {"function": "d_N", "T0": T0, "N": N0, "rect_s": rect, "winding_raw": mp.nstr(w, 10), "zeros_in_window": k,
            "integer_residual": mp.nstr(abs(w-k), 4), "max_phase_step": mp.nstr(ms, 5), "evaluations": nev,
            "zeros": zs, "n_localized": len(found), "n_re_gt_half": sum(1 for z in found if z["re"] > 0.5),
            "n_re_gt_one": sum(1 for z in found if z["re"] > 1.0), "runtime_seconds": round(time.time()-t0, 1)}

def zeros_JN(task):
    mp.mp.dps = task["dps"]; T0 = task["T0"]; theta0, c0, M0, N0 = frozen(T0); t0 = time.time()
    f = lambda x, y: cc.head(mp.mpc(x, y), theta0, N0)
    rect_full = [-1.5, 1.5, T0-1, T0+1]; rect_right = [EPS, 1.5, T0-1, T0+1]
    w_full, ms_full, nev_full = winding_rect(f, rect_full)
    w_right, ms_right, nev_right = winding_rect(f, rect_right)
    # on-line zeros: J_N(i tau) is real (3.6)/(4); sign changes on tau in [T0-1, T0+1]
    taus = [T0 - 1 + k*0.005 for k in range(401)]
    vals = [f(0, t) for t in taus]
    max_im = max(abs(mp.im(v)) for v in vals); max_re = max(abs(mp.re(v)) for v in vals)
    online = []
    for i in range(400):
        a, b = mp.re(vals[i]), mp.re(vals[i+1])
        if a == 0 or a*b < 0:
            lo, hi = taus[i], taus[i+1]; fa = a
            for _ in range(80):
                m = (lo+hi)/2; fm = mp.re(f(0, m))
                if fa*fm <= 0: hi = m
                else: lo = m; fa = fm
            online.append(mp.nstr((lo+hi)/2, 20))
    k_full = int(mp.nint(w_full)); k_right = int(mp.nint(w_right))
    off = k_full - len(online)
    res = {"function": "J_N", "T0": T0, "N": N0, "theta0": mp.nstr(theta0, 20), "rect_p_full": rect_full, "rect_p_right": rect_right,
           "winding_full_raw": mp.nstr(w_full, 10), "zeros_full": k_full, "residual_full": mp.nstr(abs(w_full-k_full), 4), "max_step_full": mp.nstr(ms_full, 5),
           "winding_right_raw": mp.nstr(w_right, 10), "zeros_right_of_eps": k_right, "residual_right": mp.nstr(abs(w_right-k_right), 4), "max_step_right": mp.nstr(ms_right, 5),
           "online_zeros_tau": online, "n_online": len(online), "max_abs_im_on_axis": mp.nstr(max_im, 4), "max_abs_re_on_axis": mp.nstr(max_re, 4),
           "off_line_zeros": off, "evaluations": nev_full + nev_right + 401, "runtime_seconds": round(time.time()-t0, 1)}
    if k_right > 0: res["localized_right"] = localize(f, rect_right, k_right)
    return res

def shadow(task):
    """A''' (b): the zero of d_N nearest (in Im) to a zeta-zero height gamma, in the box s in [0.01, 2] x [gamma-1, gamma+1];
    offsets delta_re = Re s - 1/2, delta_im = Im s - gamma. All zeros in the box are listed (winding + quadtree + findroot)."""
    mp.mp.dps = task["dps"]; gamma = mp.mpf(task["gamma"]); N = task["N"]; t0 = time.time()
    rect = [0.01, 2.0, float(gamma) - 1, float(gamma) + 1]
    f = lambda x, y: d_N(mp.mpc(x, y), N)
    w, ms, nev = winding_rect(f, rect); k = int(mp.nint(w))
    zs = localize(f, rect, k) if k > 0 else []
    found = [z for z in zs if z.get("zero")]
    res = {"gamma": task["gamma"], "N": N, "N_rule": task["N_rule"], "rect_s": rect, "zeros_in_box": k, "integer_residual": mp.nstr(abs(w-k), 4),
           "max_phase_step": mp.nstr(ms, 5), "zeros": zs, "n_localized": len(found), "runtime_seconds": round(time.time()-t0, 1)}
    if found:
        near = min(found, key=lambda z: abs(z["im"] - float(gamma)))
        z = mp.mpc(near["zero"]); dre = mp.re(z) - mp.mpf(1)/2; dim = mp.im(z) - gamma
        # exact zeta zero rho near 1/2 + i gamma (refined), and the first-principles shadow (P_M3_2):
        # delta_th = N^{1-rho} / ((rho-1) zeta'(rho))
        rho = mp.findroot(mp.zeta, mp.mpc(0.5, gamma)); zp = mp.zeta(rho, derivative=1)
        dth = mp.power(N, 1 - rho)/((rho - 1)*zp)
        delta = z - rho
        # P_M3_6: two-term Euler-Maclaurin numerator over the directly computed d_N'(rho)
        dNp = -mp.fsum(mp.log(n)*mp.power(n, -rho) for n in range(1, N+1))
        num2 = mp.power(N, 1 - rho)/(rho - 1) - mp.power(N, -rho)/2
        dpred = num2/dNp
        dN_rho = d_N(rho, N)
        res.update({"dN_prime_at_rho": mp.nstr(dNp, 15), "dN_at_rho": mp.nstr(dN_rho, 15), "em2_numerator_minus_dN": mp.nstr(-num2, 15),
                    "rel_err_em2_vs_dN_at_rho": mp.nstr(abs(dN_rho + num2)/abs(dN_rho), 6),
                    "delta_pred_em2": mp.nstr(dpred, 20), "rel_dev_pred_vs_obs": mp.nstr(abs(dpred - delta)/abs(delta), 6),
                    "delta_newton": mp.nstr(-dN_rho/dNp, 20), "rel_dev_newton_vs_obs": mp.nstr(abs(-dN_rho/dNp - delta)/abs(delta), 6)})
        res.update({"nearest_zero": near["zero"], "rho_refined": mp.nstr(rho, 25), "delta": mp.nstr(delta, 20), "delta_re": mp.nstr(mp.re(delta), 12), "delta_im": mp.nstr(mp.im(delta), 12),
                    "delta_abs": mp.nstr(abs(delta), 12), "delta_arg": mp.nstr(mp.arg(delta), 12), "delta_abs_over_sqrtN": mp.nstr(abs(delta)/mp.sqrt(N), 12),
                    "delta_re_times_N": mp.nstr(mp.re(delta)*N, 10), "nearest_re_gt_half": bool(mp.re(z) > 0.5),
                    "delta_th": mp.nstr(dth, 20), "delta_th_abs": mp.nstr(abs(dth), 12), "delta_th_arg": mp.nstr(mp.arg(dth), 12),
                    "abs_ratio_measured_over_th": mp.nstr(abs(delta)/abs(dth), 8), "arg_diff_measured_minus_th": mp.nstr(mp.arg(delta/dth), 8),
                    "zeta_prime_at_rho": mp.nstr(zp, 15)})
    return res

def en_main_term(a):
    """P_M3_5: E_N of identity (9) against the Euler-Maclaurin main term B(p) N^{1/2-p}/(p-1/2) (one term) and with the
    next term -B(p) N^{-1/2-p}/2 (two terms), on the identity points of jn_dirichlet.json."""
    mp.mp.dps = 40
    d = json.load(open(a.source)); rows = []
    for r in d["identity_points"]:
        p = mp.mpf(r["sigma"]) + 1j*mp.mpf(r["tau"]); N = r["N"]; E = mp.mpc(r["E_N"]); J = mp.mpc(r["J_N_closed_form"])
        B = B_of(p); s = p + mp.mpf(1)/2
        m1 = B*mp.power(N, mp.mpf(1)/2 - p)/(p - mp.mpf(1)/2)
        m2 = m1 - B*mp.power(N, -s)/2
        rows.append({"T": r["T"], "sigma": r["sigma"], "tau": r["tau"], "N": N, "qualifies_N_ge_tau_over_pi": bool(N >= float(r["tau"])/mp.pi),
                     "E_N": r["E_N"][:40], "main_term_1": mp.nstr(m1, 20), "rel_dev_1term": mp.nstr(abs(E - m1)/abs(E), 6), "rel_dev_2terms": mp.nstr(abs(E - m2)/abs(E), 6),
                     "abs_E_over_abs_J": r["abs_E_over_abs_J"], "pass_1term_0.2": bool(abs(E - m1)/abs(E) < mp.mpf("0.2")), "pass_2terms_0.2": bool(abs(E - m2)/abs(E) < mp.mpf("0.2"))})
    q = [x for x in rows if x["qualifies_N_ge_tau_over_pi"]]
    out = {"meta": {"source": a.source, "criterion": "|E_N - B(p) N^{1/2-p}/(p-1/2)| / |E_N| < 0.2 at points with N >= tau/pi", "n_points": len(rows), "n_qualifying": len(q),
                    "n_pass_1term": sum(1 for x in q if x["pass_1term_0.2"]), "n_pass_2terms": sum(1 for x in q if x["pass_2terms_0.2"]),
                    "max_rel_dev_1term": mp.nstr(max(mp.mpf(x["rel_dev_1term"]) for x in q), 5), "max_rel_dev_2terms": mp.nstr(max(mp.mpf(x["rel_dev_2terms"]) for x in q), 5)}, "points": rows}
    Path(a.out).write_text(json.dumps(out, indent=1))
    for x in rows: print(f"T={x['T']:<8} sigma={x['sigma']:<7} N={x['N']:<3} rel_dev 1 term={x['rel_dev_1term']:<10} 2 terms={x['rel_dev_2terms']}")
    print(out["meta"]); print(f"written {a.out}", flush=True)

def run_shadows(a):
    zs = cc.zeta_zero_heights(60.0)
    cc.ADAPTIVE_R = 0.0
    tasks = []
    for g in zs:
        _, _, M, N = cc.cutoff(float(g)); tasks.append(("shadow", {"gamma": round(float(g), 9), "N": N, "N_rule": "N(T)=M_0(gamma)-1", "dps": a.wind_dps}))
    g40 = [g for g in zs if abs(g - 40.918719) < 1e-3][0]
    Ns = [int(x) for x in a.shadow_N.split(",")]
    for N in Ns:
        tasks.append(("shadow", {"gamma": round(float(g40), 9), "N": N, "N_rule": "fixed height, N given", "dps": a.wind_dps}))
    if a.shadows_extra_only: tasks = [t for t in tasks if t[1]["N_rule"] == "fixed height, N given"]
    total = len(tasks); t0 = time.time(); res = []; fails = []
    print(f"shadows: {total} boxes ({len(zs)} zero heights at N(T) + 6 values of N at gamma={g40:.6f}), workers {a.workers}", flush=True)
    with Pool(a.workers) as pool:
        for i, (fn, r, err) in enumerate(pool.imap_unordered(_worker, tasks, chunksize=1), 1):
            if err: fails.append({"task": r, "error": err}); label = f"FAIL {err[:60]}"
            else: res.append(r); label = f"gamma={r['gamma']} N={r['N']} zeros={r['zeros_in_box']} delta_re={r.get('delta_re','-')[:9]} delta_im={r.get('delta_im','-')[:9]} dre*N={r.get('delta_re_times_N','-')[:7]}"
            el = time.time()-t0; eta = el/i*(total-i)
            print(f"[{i}/{total}] {i*100//total}% | ETA {int(eta//60)}m{int(eta%60):02d}s | {label}", flush=True)
    res.sort(key=lambda r: (r["N_rule"], float(r["gamma"]), r["N"]))
    out = {"meta": {"dps": a.wind_dps, "box": "[0.01, 2] x [gamma-1, gamma+1]", "zero_heights": [round(float(g), 9) for g in zs], "fixed_height": round(float(g40), 9),
                    "fixed_N_values": Ns, "runtime_seconds": round(time.time()-t0, 1), "n_failures": len(fails)}, "shadows": res, "failures": fails}
    Path(a.out).write_text(json.dumps(out, indent=1))
    for r in res: print(f"{r['N_rule']:22s} gamma={r['gamma']:<12} N={r['N']:<3} zeros={r['zeros_in_box']} delta_re={r.get('delta_re')} delta_im={r.get('delta_im')} dre*N={r.get('delta_re_times_N')}")
    print(f"written {a.out}", flush=True)

def _worker(args):
    fn, task = args
    try: return fn, globals()[fn](task), None
    except Exception as e: return fn, task, repr(e)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=50); ap.add_argument("--wind-dps", type=int, default=30)
    ap.add_argument("--seed", type=int, default=20260918); ap.add_argument("--workers", type=int, default=max(1, os.cpu_count()//2))
    ap.add_argument("--n-points", type=int, default=20); ap.add_argument("--out", default=str(HERE/"jn_dirichlet.json"))
    ap.add_argument("--shadows", action="store_true"); ap.add_argument("--shadow-N", default="10,15,20,30,40,60"); ap.add_argument("--shadows-extra-only", action="store_true")
    ap.add_argument("--en-main-term", action="store_true"); ap.add_argument("--source", default=str(HERE/"jn_dirichlet.json"))
    a = ap.parse_args()
    if a.shadows: return run_shadows(a)
    if a.en_main_term: return en_main_term(a)
    rng = random.Random(a.seed)
    pts = []
    for _ in range(a.n_points):
        T = round(rng.uniform(1.0, 40.0), 4); tau = round(rng.uniform(T-1, T+1), 4); sigma = round(rng.uniform(1e-3, 1.5), 4)
        pts.append({"T": T, "tau": tau, "sigma": sigma, "dps": a.dps})
    tasks = [("identity_point", t) for t in pts]
    for T0 in T0S:
        tasks.append(("zeros_dN", {"T0": T0, "dps": a.wind_dps})); tasks.append(("zeros_JN", {"T0": T0, "dps": a.wind_dps}))
    total = len(tasks); t0 = time.time(); ident = []; zd = []; zj = []; fails = []
    print(f"jn_dirichlet: {total} tasks ({a.n_points} identity points, {2*len(T0S)} zero windows), workers {a.workers}, seed {a.seed}", flush=True)
    with Pool(a.workers) as pool:
        for i, (fn, r, err) in enumerate(pool.imap_unordered(_worker, tasks, chunksize=1), 1):
            if err: fails.append({"fn": fn, "task": r, "error": err}); label = f"FAIL {fn} {err[:60]}"
            elif fn == "identity_point": ident.append(r); label = f"identity T={r['T']} sigma={r['sigma']} digits={r["digits_agree"]} E/J={r["abs_E_over_abs_J"]}"
            elif fn == "zeros_dN": zd.append(r); label = f"d_N T0={r['T0']} N={r['N']} zeros={r['zeros_in_window']} re>1/2={r['n_re_gt_half']} re>1={r['n_re_gt_one']} maxstep={r['max_phase_step']}"
            else: zj.append(r); label = f"J_N T0={r['T0']} N={r['N']} full={r['zeros_full']} online={r['n_online']} off={r['off_line_zeros']} right={r['zeros_right_of_eps']}"
            el = time.time()-t0; eta = el/i*(total-i)
            print(f"[{i}/{total}] {i*100//total}% | ETA {int(eta//60)}m{int(eta%60):02d}s | {label}", flush=True)
    ident.sort(key=lambda r: r["T"]); zd.sort(key=lambda r: r["T0"]); zj.sort(key=lambda r: r["T0"])
    out = {"meta": {"dps_identity": a.dps, "dps_winding": a.wind_dps, "seed": a.seed, "n_identity_points": len(ident),
                    "identity_all_pass_30_digits": all(r["pass_30_digits"] for r in ident), "min_digits_agree": min((r["digits_agree"] for r in ident), default=None),
                    "cutoff_rule": "N = M_0(T)-1 with (6.3) r=0, theta = pi/4 - 1/(T+1)", "windows_s": "[1/2,2] x [T0-1,T0+1]",
                    "runtime_seconds": round(time.time()-t0, 1), "n_failures": len(fails)},
           "identity_points": ident, "zeros_dN": zd, "zeros_JN": zj, "failures": fails}
    Path(a.out).write_text(json.dumps(out, indent=1))
    for r in ident: print(f"T={r['T']} sigma={r['sigma']} tau={r['tau']} N={r['N']} digits={r['digits_agree']} |E|/|J|={r['abs_E_over_abs_J']}")
    for r in zd: print(f"d_N T0={r['T0']} zeros={r['zeros_in_window']} re>1/2={r['n_re_gt_half']} re>1={r['n_re_gt_one']} zeros={[z.get('zero') for z in r['zeros']]}")
    for r in zj: print(f"J_N T0={r['T0']} full={r['zeros_full']} online={r['n_online']} off={r['off_line_zeros']} right_of_eps={r['zeros_right_of_eps']}")
    print(f"written {a.out}", flush=True)

if __name__ == "__main__":
    main()
