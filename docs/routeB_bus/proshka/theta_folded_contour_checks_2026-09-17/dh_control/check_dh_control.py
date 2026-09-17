"""DH control + G_N spectrum for the folded-contour discriminator (MAC, 2026-09-17).

Diagnostics and finite-point certificates only. Nothing here is a statement about
SUPPORT, V or RH. Shared machinery is imported from ../check_contour.py (not copied).

Part A  G_N spectrum on the zeta grid: h_N = 1^T G_N 1 with
        G_N[j,k] = 2 Re( s_j' conj(s_k) + s_k' conj(s_j) ),  s_n = I_n(p,th) + I_n(-p,-th)  (N x N real symmetric)
Part B  Davenport-Heilbronn control: chi mod 5 with chi(2)=i, kappa=(sqrt(10-2sqrt5)-2)/(sqrt5-1),
        a_n = Re chi(n) + kappa Im chi(n) -> (1, kappa, -kappa, -1, 0) periodic,
        Lambda_DH(s) = (5/pi)^{(s+1)/2} Gamma((s+1)/2) f_DH(s) = Lambda_DH(1-s), F_DH(p) = Lambda_DH(1/2+p),
        theta atom phi_n(z) = 2 n a_n e^{3z/2} exp(-A_n e^{2z}), A_n = pi n^2/5,
        ray (3.3)^DH: I_n(p,th) = n a_n A_n^{-p/2-3/4} Gamma(p/2+3/4, A_n e^{2 i th}),
        budgets: pair of rays <= 2n e^{-th T} e^{-beta_n}(1/beta_n + 1/beta_n^2), beta_n = pi c n^2/5;
        B_DH = (4/(bM))(1+1/(2bM)) e^{-bM^2}, b = pi c/5, bM^2 >= 1; D_DH = sum_n 2n e^{-beta_n}(1/beta_n+1/beta_n^2);
        E_N^DH = 16 sigma D_DH B_DH e^{-2 th T}.

Modes:
  --selftest            derivation gate (closed form vs direct integral vs Hurwitz reference; envelope check)
  --reference           s0 by findroot, on-line zeros near T0, first-order window delta -> dh_control_reference.json
  --spectrum-zeta       Part A on the zeta grid (mpmath dps 50), diagnostic + adaptive cutoff -> gn_spectrum_zeta.json
  --spectrum-arb        rigorous sign of lambda_min at 20 points (Rayleigh quotient in arb) -> gn_spectrum_zeta_arb.json
  --dh-grid             Part B rigorous arb grid (control strip + zeta-like strip) -> dh_control_grid_arb.json
  --spectrum-dh         Part A for DH on the control strip (mpmath dps 50) -> gn_spectrum_dh.json
"""
from __future__ import annotations
import argparse, json, os, sys, time
from fractions import Fraction
from multiprocessing import Pool
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import check_contour as cc                      # shared: ray, head, cutoff, reference_xi, _nstr, _arb_setup, _ray_integrals_arb

# ----------------------------------------------------------------------------------
# DH arithmetic (mpmath)
# ----------------------------------------------------------------------------------

def kappa_mp():
    return (mp.sqrt(10 - 2*mp.sqrt(5)) - 2)/(mp.sqrt(5) - 1)

CHI = {1: 1, 2: 1j, 3: -1j, 4: -1, 0: 0}

def a_dh(n, kappa):
    x = CHI[n % 5]
    return mp.re(x) + kappa*mp.im(x)

def A_n(n):
    return mp.pi*n*n/5

def ray_dh(n, p, theta, kappa):
    """(3.3)^DH: I_n(p,theta) = n a_n A^{-p/2-3/4} Gamma(p/2+3/4, A e^{2 i theta})."""
    an = a_dh(n, kappa)
    if an == 0:
        return mp.mpc(0)
    A = A_n(n); z = A*mp.exp(2j*theta); b = p/2 + mp.mpf(3)/4
    return n*an*A**(-p/2 - mp.mpf(3)/4)*mp.gammainc(b, z, mp.inf)

def head_dh(p, theta, N, kappa):
    return mp.fsum(ray_dh(n, p, theta, kappa) + ray_dh(n, -p, -theta, kappa) for n in range(1, N+1))

def ray_dh_direct(n, p, theta, kappa, L=6):
    """Direct integral of the atom along the rotated ray (derivation check only)."""
    an = a_dh(n, kappa); A = A_n(n)
    f = lambda t: 2*n*an*mp.exp(mp.mpf(3)*(t+1j*theta)/2)*mp.exp(-A*mp.exp(2*(t+1j*theta)))*mp.exp(p*(t+1j*theta))
    return mp.quad(f, [0, 1, 3, L])

def L_chi(s, kappa=None, conj=False):
    """L(s,chi) = 5^{-s} sum_{a=1}^{4} chi(a) zeta(s, a/5) (Hurwitz)."""
    tot = mp.mpc(0)
    for a in range(1, 5):
        x = CHI[a]
        if conj: x = mp.conj(x)
        tot += x*mp.zeta(s, mp.mpf(a)/5)
    return mp.power(5, -s)*tot

def f_dh(s, kappa):
    return (1 - 1j*kappa)/2*L_chi(s) + (1 + 1j*kappa)/2*L_chi(s, conj=True)

def Lambda_dh(s, kappa):
    return mp.power(mp.mpf(5)/mp.pi, (s+1)/2)*mp.gamma((s+1)/2)*f_dh(s, kappa)

def F_dh(p, kappa):
    return Lambda_dh(mp.mpf(1)/2 + p, kappa)

def budgets_dh(theta, c, M, sigma, T):
    b = mp.pi*c/5
    B = (4/(b*M))*(1 + 1/(2*b*M))*mp.exp(-b*M*M)
    # D_DH: finite sum up to K with bK^2 >= 1, plus the same tail bound from K
    K = max(2, int(mp.ceil(mp.sqrt(1/b))))
    D = mp.fsum(2*n*mp.exp(-b*n*n)*(1/(b*n*n) + 1/(b*n*n)**2) for n in range(1, K)) + (4/(b*K))*(1 + 1/(2*b*K))*mp.exp(-b*K*K)
    E = 16*sigma*D*B*mp.exp(-2*theta*T)
    return B, D, E

# ----------------------------------------------------------------------------------
# selftest: derivation gate
# ----------------------------------------------------------------------------------

def selftest(dps=50):
    mp.mp.dps = dps
    kappa = kappa_mp()
    out = {"dps": dps, "kappa": mp.nstr(kappa, 30)}
    out["a_n_1_to_10"] = [mp.nstr(a_dh(n, kappa), 20) for n in range(1, 11)]
    out["a_n_matches_(1,k,-k,-1,0)"] = all(abs(a_dh(n, kappa) - v) < mp.mpf(10)**(-dps+5) for n, v in zip(range(1, 6), [1, kappa, -kappa, -1, 0]))
    # functional equation and reality on the line
    for p in [mp.mpc(0.25, 20), mp.mpc(0.3085, 85.699), mp.mpc(0.1, 40)]:
        out[f"F(p)-F(-p) at {mp.nstr(p,6)}"] = mp.nstr(abs(F_dh(p, kappa) - F_dh(-p, kappa)), 5)
    out["Im F(iT), T=40"] = mp.nstr(abs(mp.im(F_dh(mp.mpc(0, 40), kappa))), 5)
    # closed form vs direct ray integral (n=1,2 at two points)
    for n in (1, 2):
        for p, th in [(mp.mpc(0.25, 20), mp.pi/4 - mp.mpf(1)/21), (mp.mpc(0.3, 86), mp.pi/4 - mp.mpf(1)/87)]:
            a = ray_dh(n, p, th, kappa); d = ray_dh_direct(n, p, th, kappa)
            out[f"ray closed-vs-direct n={n} p={mp.nstr(p,5)}"] = mp.nstr(abs(a-d)/max(abs(a), mp.mpf(10)**-200), 5)
    # envelope: |H_DH - h_N^DH| vs E_N^DH at test points (adaptive cutoff r=0)
    env = []
    for sigma, T in [(mp.mpf(1)/4, 20), (mp.mpf(1)/4, 40), (mp.mpf(1)/64, 86), (mp.mpf('0.3'), 85.7)]:
        cc.ADAPTIVE_R = 0.0
        theta, c, M, N = cc.cutoff(T)
        p = sigma + 1j*T
        J = list(mp.diffs(lambda x: head_dh(x, theta, N, kappa), p, 1))
        F = list(mp.diffs(lambda x: F_dh(x, kappa), p, 1))
        h = 4*mp.re(J[1]*mp.conj(J[0])); H = 4*mp.re(F[1]*mp.conj(F[0]))
        B, D, E = budgets_dh(theta, c, M, sigma, T)
        env.append({"sigma": mp.nstr(sigma, 6), "T": T, "M": M, "h_N": mp.nstr(h, 20), "H_ref": mp.nstr(H, 20),
                    "abs_diff": mp.nstr(abs(H-h), 5), "E_N_DH": mp.nstr(E, 5), "diff_over_E": mp.nstr(abs(H-h)/E, 5),
                    "scaled_F_error_j0": mp.nstr(mp.exp(theta*T)*abs(F[0]-J[0]), 5), "B_DH": mp.nstr(B, 5), "D_DH": mp.nstr(D, 5),
                    "envelope_holds": bool(abs(H-h) <= E)})
    out["envelope"] = env
    out["envelope_holds_all"] = all(e["envelope_holds"] for e in env)
    return out

# ----------------------------------------------------------------------------------
# reference: s0, on-line zeros near T0, first-order window
# ----------------------------------------------------------------------------------

def reference(dps=40):
    mp.mp.dps = dps
    kappa = kappa_mp()
    s0 = mp.findroot(lambda s: f_dh(s, kappa), mp.mpc('0.808517', '85.699348'))
    out = {"dps": dps, "kappa": mp.nstr(kappa, 30), "s0": mp.nstr(s0, 32), "sigma0": mp.nstr(mp.re(s0) - mp.mpf(1)/2, 30),
           "T0": mp.nstr(mp.im(s0), 30), "abs_f_at_s0": mp.nstr(abs(f_dh(s0, kappa)), 5),
           "mirror_1-conj(s0)": mp.nstr(1 - mp.conj(s0), 32)}
    # on-line zeros of X(T)=Lambda_DH(1/2+iT) near T0: sign changes on [80, 92] step 0.05, refined by findroot
    X = lambda T: mp.re(Lambda_dh(mp.mpf(1)/2 + 1j*T, kappa))
    Ts = [80 + k*mp.mpf('0.05') for k in range(0, 241)]
    vals = [X(T) for T in Ts]
    zeros = []
    for i in range(len(Ts)-1):
        if vals[i]*vals[i+1] < 0:
            zeros.append(mp.findroot(X, (Ts[i], Ts[i+1]), solver='bisect'))
    out["online_zeros_80_92"] = [mp.nstr(z, 15) for z in zeros]
    T0 = mp.im(s0); a = mp.re(s0) - mp.mpf(1)/2
    # first-order window: d/dsigma [H/(4|F|^2)] at sigma=0 = 2(d^2-a^2)/(a^2+d^2)^2 + sum_gamma 1/(T-gamma)^2 (+ far-zero remainder, positive, ignored -> window is an upper bound)
    def slope(T):
        d = T - T0
        return 2*(d*d - a*a)/(a*a + d*d)**2 + mp.fsum(1/(T-g)**2 for g in zeros)
    grid = [T0 + k*mp.mpf('0.001') for k in range(-400, 401)]
    neg = [T for T in grid if slope(T) < 0]
    out["first_order_negative_window"] = {"T_min": mp.nstr(min(neg), 10) if neg else None, "T_max": mp.nstr(max(neg), 10) if neg else None,
                                          "delta_minus": mp.nstr(T0 - min(neg), 6) if neg else None, "delta_plus": mp.nstr(max(neg) - T0, 6) if neg else None,
                                          "note": "near on-line zeros only (80..92); far zeros add a positive remainder, so the true window is not wider"}
    out["slope_at_T0"] = mp.nstr(slope(T0), 8)
    out["nearest_online_zeros_to_T0"] = [mp.nstr(z, 12) for z in sorted(zeros, key=lambda z: abs(z-T0))[:4]]
    return out

# ----------------------------------------------------------------------------------
# Part A: G_N spectrum (mpmath) for zeta and for DH
# ----------------------------------------------------------------------------------

def summands(kind, p, theta, N, kappa=None):
    """s_n and s_n' (derivative in p, theta and N fixed) for n=1..N."""
    s, sp = [], []
    for n in range(1, N+1):
        if kind == "zeta":
            f = lambda x, n=n: cc.ray(n, x, theta) + cc.ray(n, -x, -theta)
        else:
            f = lambda x, n=n: ray_dh(n, x, theta, kappa) + ray_dh(n, -x, -theta, kappa)
        d = list(mp.diffs(f, p, 1))
        s.append(d[0]); sp.append(d[1])
    return s, sp

def gram(s, sp):
    N = len(s)
    G = mp.matrix(N, N)
    for j in range(N):
        for k in range(j, N):
            v = 2*mp.re(sp[j]*mp.conj(s[k]) + sp[k]*mp.conj(s[j]))
            G[j, k] = v; G[k, j] = v
    return G

def spectrum_rank4(s, sp):
    """G = W C W^T, W=[Re u, Im u, Re v, Im v] (u=s, v=s'), C=2*[[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]].
    Nonzero eigenvalues of G = eigenvalues of C (W^T W); eigenvectors x = W y."""
    N = len(s)
    W = mp.matrix(N, 4)
    for i in range(N):
        W[i, 0] = mp.re(s[i]); W[i, 1] = mp.im(s[i]); W[i, 2] = mp.re(sp[i]); W[i, 3] = mp.im(sp[i])
    S = W.T*W
    C = mp.matrix([[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]])*2
    E, Y = mp.eig(C*S)
    lam = [mp.re(E[i]) for i in range(4)]
    imag_leak = max(abs(mp.im(E[i])) for i in range(4))
    vecs = []
    for i in range(4):
        y = [Y[k, i] for k in range(4)]
        x = [mp.re(mp.fsum(W[r, k]*y[k] for k in range(4))) for r in range(N)]
        nrm = mp.sqrt(mp.fsum(v*v for v in x)) or mp.mpf(1)
        vecs.append([v/nrm for v in x])
    return lam, vecs, imag_leak

def spectrum_point(task):
    dps = task["dps"]; mp.mp.dps = dps
    kind = task["kind_fn"]; kappa = kappa_mp() if kind == "dh" else None
    cc.ADAPTIVE_R = task.get("adaptive_r")
    T = mp.mpf(task["T"]); sigma = mp.mpf(Fraction(task["sigma"])) if "/" in task["sigma"] else mp.mpf(task["sigma"])
    theta, c, M, N = cc.cutoff(T)
    p = sigma + 1j*T
    t0 = time.time()
    s, sp = summands(kind, p, theta, N, kappa)
    lam, vecs, leak = spectrum_rank4(s, sp)
    order = sorted(range(4), key=lambda i: lam[i])
    imin, imax = order[0], order[-1]
    vec = vecs[imin]
    top = sorted(range(N), key=lambda i: -abs(vec[i]))[:5]
    h_direct = 4*mp.re(mp.fsum(sp)*mp.conj(mp.fsum(s)))
    # h from the form: 1^T G 1 = sum_i lam_i (1^T x_i)^2 only if x_i orthonormal; use the explicit W-form instead
    ones = [mp.mpf(1)]*N
    Wt = [mp.fsum(mp.re(s[i]) for i in range(N)), mp.fsum(mp.im(s[i]) for i in range(N)), mp.fsum(mp.re(sp[i]) for i in range(N)), mp.fsum(mp.im(sp[i]) for i in range(N))]
    h_form = 2*(2*Wt[0]*Wt[2] + 2*Wt[1]*Wt[3])
    scale = abs(mp.fsum(s))**2
    out = {"sigma": task["sigma"], "T": task["T"], "kind": task["kind"], "gamma": task.get("gamma"), "dps": dps,
           "cutoff_rule": task["cutoff_rule"], "M": M, "N": N, "rank_bound": 4,
           "nonzero_eigenvalues_sorted": [lam[i] for i in order], "lambda_min": lam[imin], "lambda_max": lam[imax],
           "n_negative": sum(1 for x in lam if x < 0), "n_positive": sum(1 for x in lam if x > 0), "n_zero_exact": N - 4,
           "eig_imag_leak": leak,
           "lambda_min_over_absJ2": lam[imin]/scale if scale else None, "lambda_max_over_absJ2": lam[imax]/scale if scale else None,
           "eigvec_min_top5": [{"n": i+1, "component": vec[i]} for i in top],
           "eigvec_min_full": vec if task.get("keep_vec") else None,
           "h_N_from_form": h_form, "h_N_direct": h_direct, "runtime_seconds": time.time()-t0}
    if task.get("full_check"):
        G = gram(s, sp); Ef, _ = mp.eigsy(G); full = sorted(Ef[i] for i in range(N))
        out["full_eigsy_min_max"] = [full[0], full[-1]]
        out["full_eigsy_nonzero_count_rel_1e-30"] = sum(1 for x in full if abs(x) > mp.mpf(10)**-30*abs(full[-1]))
    def ser(k, v):
        if k == "eigvec_min_top5": return [{"n": d["n"], "component": cc._nstr(d["component"], 12)} for d in v]
        if k == "eigvec_min_full": return None if v is None else [cc._nstr(x, 20) for x in v]
        return cc._nstr(v)
    return {k: ser(k, v) for k, v in out.items()}

def build_zeta_grid():
    sigmas = ["1/64", "1/32", "1/16", "1/8", "1/4"]
    pts, _ = cc.build_grid([Fraction(s) for s in sigmas], 14.0, 60.0, 0.25, [-0.05, 0.0, 0.05])
    return pts

def run_spectrum_zeta(args):
    pts = build_zeta_grid()
    tasks = []
    zeros = cc.zeta_zero_heights(60.0)
    keep = set([("1/64", round(z, 6)) for z in zeros] + [("1/4", T) for T in (14.0, 20.0, 30.0, 40.0, 50.0, 60.0, 25.75)])
    for rule, ar in (("diagnostic_sqrt(40/c)", None), ("adaptive_6.3_r=0", 0.0)):
        for i, pt in enumerate(pts):
            tasks.append(dict(pt, dps=args.dps, kind_fn="zeta", cutoff_rule=rule, adaptive_r=ar,
                              full_check=(i < 3), keep_vec=((pt["sigma"], pt["T"]) in keep and rule.startswith("diagnostic"))))
    _run_pool(tasks, spectrum_point, args.workers, args.out, meta={"part": "A", "function": "zeta", "matrix": "G_N[j,k]=2Re(s_j' conj s_k + s_k' conj s_j) on summands s_n; h_N = 1^T G 1", "dps": args.dps})

def build_dh_control_grid(T0):
    sig = ["1/64", "1/32", "1/16", "1/8", "1/4", "0.28", "0.30", "0.3085", "0.32"]
    Ts = [round(80.0 + 0.1*k, 6) for k in range(0, 121)]
    extra = [round(T0 + d, 6) for d in (-0.05, -0.02, -0.01, -0.005, 0.005, 0.01, 0.02, 0.05)]
    pts = [{"sigma": s, "T": T, "kind": "control", "gamma": None} for T in Ts for s in sig] + \
          [{"sigma": s, "T": T, "kind": "T0_neighbourhood", "gamma": T0} for T in extra for s in sig]
    return pts

def build_dh_zetalike_grid():
    return [{"sigma": s, "T": float(T), "kind": "zetalike", "gamma": None} for T in range(14, 61) for s in ("1/64", "1/8", "1/4")]

def run_spectrum_dh(args):
    ref = json.load(open(HERE/"dh_control_reference.json"))
    T0 = float(ref["T0"])
    pts = build_dh_control_grid(T0)
    tasks = [dict(pt, dps=args.dps, kind_fn="dh", cutoff_rule="adaptive_6.3_r=0", adaptive_r=0.0, full_check=(i < 3)) for i, pt in enumerate(pts)]
    _run_pool(tasks, spectrum_point, args.workers, args.out, meta={"part": "A", "function": "DH", "matrix": "same G_N on DH summands", "dps": args.dps, "T0": T0})

# ----------------------------------------------------------------------------------
# Part A rigorous: sign of lambda_min via Rayleigh quotient in arb
# ----------------------------------------------------------------------------------

def _dh_ray_integrals_arb(acb, arb, p, theta, n, kappa_a, L, sign):
    """Orders j=0,1 of one DH ray as balls; sign=-1 is the reflected ray (derivative factor -(t-i th))."""
    ith = acb(0, theta)*sign; pp = p*sign
    A = arb.pi()*n*n/5
    an = {1: arb(1), 2: kappa_a, 3: -kappa_a, 4: arb(-1), 0: arb(0)}[n % 5]
    def mk(j):
        def f(t, analytic):
            z = t + ith
            return ((sign*z)**j) * 2*n*an*(3*z/2).exp()*(-A*(2*z).exp()).exp()*(pp*z).exp()
        return f
    return [acb.integral(mk(j), 0, L) for j in range(2)]

def _dh_tail_arb(arb, theta, T, n, c, L):
    """|int_L^inf| for one ray, j<=2, |Re p|<=1/2: <= e^{-th T} 2n * 1/2 int_U^inf u e^{-beta u} du, beta = A_n c."""
    beta = arb.pi()*n*n/5*c; U = (2*L).exp()
    return (-theta*T).exp()*n*(-beta*U).exp()*(U/beta + 1/beta**2)

def _zeta_ray_integrals_arb(acb, arb, p, theta, a, L, sign):
    return cc._ray_integrals_arb(acb, arb, p, theta, a, L, sign)[:2]

def rayleigh_point(task):
    """Certify sign of x^T G x for the mpmath eigenvector x (Rayleigh quotient upper bound on lambda_min)."""
    dps = task["dps"]; acb, arb = cc._arb_setup(dps)
    kind = task["kind_fn"]; cc.ADAPTIVE_R = task.get("adaptive_r")
    T = arb(task["T"]); t1 = T + 1; theta = arb.pi()/4 - 1/t1; c = (2*theta).cos()
    fr = Fraction(task["sigma"]); sigma = arb(fr.numerator)/fr.denominator
    _, _, M, N = cc.cutoff(float(task["T"]))
    p = acb(sigma, T); L = arb(4); t0 = time.time()
    kappa_a = ((10 - 2*arb(5).sqrt()).sqrt() - 2)/(arb(5).sqrt() - 1)
    s, sp = [], []
    for n in range(1, N+1):
        if kind == "zeta":
            a = arb.pi()*n*n
            r1 = _zeta_ray_integrals_arb(acb, arb, p, theta, a, L, +1); r2 = _zeta_ray_integrals_arb(acb, arb, p, theta, a, L, -1)
            tb = cc._tail_bound_arb(arb, theta, T, sigma, a, c, L).upper()
        else:
            r1 = _dh_ray_integrals_arb(acb, arb, p, theta, n, kappa_a, L, +1); r2 = _dh_ray_integrals_arb(acb, arb, p, theta, n, kappa_a, L, -1)
            tb = _dh_tail_arb(arb, theta, T, n, c, L).upper()
        ball = acb(arb(0, tb), arb(0, tb))
        s.append(r1[0] + r2[0] + ball + ball); sp.append(r1[1] + r2[1] + ball + ball)
    # mpmath eigenvector (float coefficients, exact rationals in arb) for the Rayleigh quotient
    x = [arb(v) for v in task["eigvec"]]
    q = arb(0)
    for j in range(N):
        for k in range(N):
            q = q + x[j]*x[k]*2*(sp[j]*s[k].conjugate() + sp[k]*s[j].conjugate()).real
    xx = sum((v*v for v in x), arb(0))
    def cert(v):
        if v.lower() > 0: return "POSITIVE"
        if v.upper() < 0: return "NEGATIVE"
        return "UNDECIDED"
    hN = 4*(sum(sp, acb(0))*sum(s, acb(0)).conjugate()).real
    return {"sigma": task["sigma"], "T": task["T"], "kind_fn": kind, "M": M, "N": N, "dps": dps,
            "rayleigh_xGx_over_xx": str(q/xx), "sign_certificate_rayleigh": cert(q),
            "meaning": "NEGATIVE certifies lambda_min(G_N) < 0 rigorously (Rayleigh upper bound); POSITIVE/UNDECIDED certify nothing about lambda_min",
            "h_N_arb": str(hN), "sign_certificate_h_N": cert(hN), "runtime_seconds": time.time()-t0}

def run_spectrum_arb(args):
    spec = json.load(open(args.spectrum_json))
    want = [("1/64", z) for z in cc.zeta_zero_heights(60.0)] + [("1/4", T) for T in (14.0, 20.0, 30.0, 40.0, 50.0, 60.0, 25.75)]
    tasks = []
    for sig, T in want:
        cand = [r for r in spec["points"] if r["sigma"] == sig and abs(float(r["T"]) - T) < 1e-6 and r["cutoff_rule"].startswith("diagnostic")]
        if not cand: continue
        r = cand[0]
        vec = [float(x) for x in r["eigvec_min_full"]] if r.get("eigvec_min_full") else None
        if vec is None: continue
        tasks.append({"sigma": sig, "T": float(r["T"]), "dps": args.dps, "kind_fn": "zeta", "adaptive_r": None, "eigvec": vec})
    _run_pool(tasks, rayleigh_point, args.workers, args.out, meta={"part": "A-rigorous", "note": "test vector = mpmath lambda_min eigenvector rounded to double (exact rationals in arb); Rayleigh quotient x^T G x computed in arb; NEGATIVE ball => lambda_min<0 certified at that point", "dps": args.dps})

# ----------------------------------------------------------------------------------
# Part B: DH rigorous grid (arb)
# ----------------------------------------------------------------------------------

def dh_grid_point(task):
    dps = task["dps"]; acb, arb = cc._arb_setup(dps)
    cc.ADAPTIVE_R = 0.0
    T = arb(task["T"]); t1 = T + 1; theta = arb.pi()/4 - 1/t1; c = (2*theta).cos()
    sg = task["sigma"]; sigma = (arb(Fraction(sg).numerator)/Fraction(sg).denominator) if "/" in sg else arb(sg)
    _, _, M, N = cc.cutoff(float(task["T"]))
    p = acb(sigma, T); t0 = time.time()
    kappa_a = ((10 - 2*arb(5).sqrt()).sqrt() - 2)/(arb(5).sqrt() - 1)
    # truncation L: tail of n=1 below 10^-(dps+8) e^{-th T}
    target = arb(10)**(-(dps+8))*(-theta*T).exp(); L = arb(2)
    while _dh_tail_arb(arb, theta, T, 1, c, L).upper() > target.lower():
        L = L + arb(1)/2
        if L > 12: break
    J = [acb(0), acb(0)]
    for n in range(1, N+1):
        if n % 5 == 0: continue
        r1 = _dh_ray_integrals_arb(acb, arb, p, theta, n, kappa_a, L, +1); r2 = _dh_ray_integrals_arb(acb, arb, p, theta, n, kappa_a, L, -1)
        tb = _dh_tail_arb(arb, theta, T, n, c, L).upper(); ball = acb(arb(0, tb), arb(0, tb))
        for j in range(2): J[j] = J[j] + r1[j] + r2[j] + ball + ball
    h = 4*(J[1]*J[0].conjugate()).real
    b = arb.pi()*c/5
    B = (4/(b*M))*(1 + 1/(2*b*M))*(-b*M*M).exp()
    K = max(2, int(mp.ceil(mp.sqrt(1/float(b.mid())))))
    D = sum((2*n*(-b*n*n).exp()*(1/(b*n*n) + 1/(b*n*n)**2) for n in range(1, K)), arb(0)) + (4/(b*K))*(1 + 1/(2*b*K))*(-b*K*K).exp()
    E = 16*sigma*D*B*(-2*theta*T).exp()
    LN = h - E; UN = h + E
    def cert(v):
        if v.lower() > 0: return "POSITIVE"
        if v.upper() < 0: return "NEGATIVE"
        return "UNDECIDED"
    # reference H_DH via mpmath (Hurwitz zeta), diagnostic only; compared against the rigorous E lower edge
    mp.mp.dps = dps; kappa = kappa_mp(); pm = mp.mpf(Fraction(sg)) if "/" in sg else mp.mpf(sg); pm = pm + 1j*mp.mpf(task["T"])
    Fm = list(mp.diffs(lambda x: F_dh(x, kappa), pm, 1)); Hm = 4*mp.re(Fm[1]*mp.conj(Fm[0]))
    H = arb(mp.nstr(Hm, dps))
    dHh = abs(H - h)
    return {"sigma": sg, "T": task["T"], "kind": task["kind"], "gamma": task.get("gamma"), "dps": dps, "M": M, "N": N, "L_truncation": str(L),
            "J0": str(J[0]), "J1": str(J[1]), "h_N_DH": str(h), "h_N_mid": str(h.mid()), "h_N_rad": str(h.rad()),
            "B_DH": str(B), "D_DH": str(D), "E_N_DH": str(E), "L_N": str(LN), "U_N": str(UN),
            "sign_certificate_h_N": cert(h), "sign_certificate_L_N": cert(LN), "sign_certificate_U_N": cert(UN),
            "H_DH_reference_mpmath": mp.nstr(Hm, 32), "abs_H_minus_h": str(dHh), "abs_H_minus_h_over_E": str(dHh/E),
            "envelope_holds_diagnostic": bool(dHh.upper() < E.lower()), "sign_H_reference_float": int(mp.sign(Hm)),
            "runtime_seconds": time.time()-t0, "certificate_scope": "finite point only; DH control, no statement about zeta"}

def run_dh_grid(args):
    ref = json.load(open(HERE/"dh_control_reference.json")); T0 = float(ref["T0"])
    pts = build_dh_control_grid(T0) + build_dh_zetalike_grid()
    tasks = [dict(pt, dps=args.dps) for pt in pts]
    _run_pool(tasks, dh_grid_point, args.workers, args.out, meta={"part": "B", "function": "DH", "cutoff": "adaptive (6.3) r=0", "dps": args.dps, "T0": T0,
              "budget": "E_N^DH = 16 sigma D_DH B_DH e^{-2 theta T}, B_DH=(4/(bM))(1+1/(2bM))e^{-bM^2}, b=pi c/5"})

# ----------------------------------------------------------------------------------
# pool driver
# ----------------------------------------------------------------------------------

def _worker(args):
    fn_name, task = args
    fn = globals()[fn_name]
    try:
        return fn(task), None
    except Exception as e:
        return task, repr(e)

def _run_pool(tasks, fn, workers, out, meta):
    total = len(tasks); res = {"points": [], "failures": [], "meta": dict(meta)}; t0 = time.time(); done = 0
    print(f"{fn.__name__}: {total} tasks, workers {workers}", flush=True)
    with Pool(workers) as pool:
        for r, err in pool.imap_unordered(_worker, [(fn.__name__, t) for t in tasks], chunksize=1):
            done += 1
            if err: res["failures"].append({"task": {k: v for k, v in r.items() if k != "eigvec"}, "error": err}); label = f"FAIL {err[:70]}"
            else:
                res["points"].append(r)
                keyz = [k for k in ("lambda_min", "sign_certificate_U_N", "sign_certificate_rayleigh", "h_N_DH") if k in r]
                label = f"sigma={r.get('sigma')} T={r.get('T')} " + " ".join(f"{k}={str(r[k])[:14]}" for k in keyz)
            el = time.time()-t0; eta = el/done*(total-done)
            print(f"[{done}/{total}] {done*100//total}% | ETA {int(eta//60)}m{int(eta%60):02d}s | {label}", flush=True)
            if done % 25 == 0: Path(out).write_text(json.dumps(res, indent=1))
    res["points"].sort(key=lambda r: (str(r.get("cutoff_rule", "")), float(r["T"]), str(r["sigma"])))
    res["meta"].update({"n_points": len(res["points"]), "n_failures": len(res["failures"]), "runtime_seconds": time.time()-t0})
    Path(out).write_text(json.dumps(res, indent=1)); print(f"written {out} in {time.time()-t0:.0f}s", flush=True)

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true"); ap.add_argument("--reference", action="store_true")
    ap.add_argument("--spectrum-zeta", action="store_true"); ap.add_argument("--spectrum-arb", action="store_true")
    ap.add_argument("--dh-grid", action="store_true"); ap.add_argument("--spectrum-dh", action="store_true")
    ap.add_argument("--dps", type=int, default=50); ap.add_argument("--workers", type=int, default=max(1, os.cpu_count()//2))
    ap.add_argument("--out", default=None); ap.add_argument("--spectrum-json", default=str(HERE/"gn_spectrum_zeta.json"))
    a = ap.parse_args()
    if a.selftest:
        r = selftest(a.dps); Path(a.out or HERE/"dh_selftest.json").write_text(json.dumps(r, indent=1)); print(json.dumps(r, indent=1))
    elif a.reference:
        r = reference(a.dps); Path(a.out or HERE/"dh_control_reference.json").write_text(json.dumps(r, indent=1)); print(json.dumps(r, indent=1))
    elif a.spectrum_zeta: a.out = a.out or str(HERE/"gn_spectrum_zeta.json"); run_spectrum_zeta(a)
    elif a.spectrum_arb: a.out = a.out or str(HERE/"gn_spectrum_zeta_arb.json"); run_spectrum_arb(a)
    elif a.dh_grid: a.out = a.out or str(HERE/"dh_control_grid_arb.json"); run_dh_grid(a)
    elif a.spectrum_dh: a.out = a.out or str(HERE/"gn_spectrum_dh.json"); run_spectrum_dh(a)
    else: ap.print_help()
