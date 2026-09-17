"""Diagnostic checks only: mpmath is not interval arithmetic or a sign proof.

Extended 2026-09-17 (Mac channel): grid mode over sigma x T incl. zeta-zero heights,
two diagnostic mpmath passes (dps 50 / 80) and a rigorous python-flint/arb pass
(every value a ball; a sign counts only if the whole ball lies on one side of zero).

Formulas: (3.2)-(3.4) head h_N, (5.2) error E_N = sigma*e_N, e_N as in the round-8
audit (1.1); theta(T)=pi/4-1/(T+1), c=cos(2 theta), M=ceil(sqrt(40/c)), N=M-1 as in the
registered diagnostic cutoff. Sigma->0 slope: 4*L1[j](T), L1 = j'^2 - j j'' with j(T)=J_N(iT).

Usage (legacy, unchanged):
    python check_contour.py --T 40 --dps 80
Grid, diagnostic (mpmath):
    python check_contour.py --grid --dps 50 --workers 8 --out grid_dps50.json
Grid, rigorous (arb):
    python check_contour.py --grid --arb --dps 60 --workers 4 --out grid_arb_dps60.json
Compare two diagnostic passes:
    python check_contour.py --compare grid_dps50.json grid_dps80.json --out grid_compare.json
"""
from __future__ import annotations
import argparse, json, os, sys, time
from fractions import Fraction
from multiprocessing import Pool
from pathlib import Path
import mpmath as mp

# ----------------------------------------------------------------------------------
# legacy single-point diagnostic (unchanged)
# ----------------------------------------------------------------------------------

def source_atom(z: mp.mpc, n: int) -> mp.mpc:
    a = mp.pi*n*n
    return (4*a*a*mp.exp(mp.mpf(9)*z/2)-6*a*mp.exp(mp.mpf(5)*z/2))*mp.exp(-a*mp.exp(2*z))

def ray(n: int, p: mp.mpc, theta: mp.mpf) -> mp.mpc:
    a = mp.pi*n*n
    z = a*mp.exp(2j*theta)
    b = p/2 + mp.mpf(5)/4
    # Exact recurrence, with the principal logarithm in |arg z|<pi/2.
    return a**(-p/2-mp.mpf(1)/4)*((p-mp.mpf(1)/2)*mp.gammainc(b,z,mp.inf)+2*mp.exp(b*mp.log(z)-z))

def head(p: mp.mpc, theta: mp.mpf, N: int) -> mp.mpc:
    return mp.fsum(ray(n,p,theta)+ray(n,-p,-theta) for n in range(1,N+1))

def reference_xi(p: mp.mpc) -> mp.mpc:
    s = mp.mpf(1)/2+p
    return s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)/2

def check(T: int, dps: int) -> dict:
    mp.mp.dps=dps
    theta=mp.pi/4-1/mp.mpf(T+1)
    c=mp.cos(2*theta)
    M=int(mp.ceil(mp.sqrt(40/c)))
    N=M-1
    p=mp.mpf(1)/4+1j*T
    fac=mp.exp(theta*T)
    approx=[mp.diff(lambda x:head(x,theta,N),p,j) for j in range(3)]
    refs=[mp.diff(reference_xi,p,j) for j in range(3)]
    beta=mp.pi*c*M*M
    B=448*M**3/c*mp.exp(-beta)
    D=4/c**4
    err=16*mp.re(p)*D*B/mp.exp(2*theta*T)
    Hn=4*mp.re(approx[1]*mp.conj(approx[0]))
    H=4*mp.re(refs[1]*mp.conj(refs[0]))
    symmetry=head(-mp.conj(p),theta,N)-mp.conj(approx[0])
    values={"T":T,"dps":dps,"N":N,"M":M,"theta":theta,"c":c,"beta":beta,
     "scaled_error_F_derivatives":[fac*abs(approx[j]-refs[j]) for j in range(3)],
     "scaled_B":B,"scaled_D":D,"Hn":Hn,"H_reference":H,
     "H_error_bound":err,"observed_H_error":abs(H-Hn),
     "scaled_Hn_over_sigma":Hn*fac**2/mp.re(p),
     "scaled_remainder_over_sigma":16*D*B,
     "reflection_error":abs(symmetry),
     "derivative_errors_fit_envelope_diagnostic":all(fac*abs(approx[j]-refs[j])<=B for j in range(3)),
     "H_error_fits_envelope_diagnostic":abs(H-Hn)<=err,
     "claimed_sign_certificate":False}
    def serial(x):
        if isinstance(x,(bool,str,int)):return x
        if isinstance(x,list):return [serial(y) for y in x]
        return mp.nstr(x,32)
    return {k:serial(v) for k,v in values.items()}

# ----------------------------------------------------------------------------------
# grid definition
# ----------------------------------------------------------------------------------

ZETA_ZEROS_LE_60 = None  # filled lazily via mp.zetazero

def zeta_zero_heights(Tmax: float) -> list:
    """Imaginary parts of the first zeta zeros with gamma <= Tmax (mpmath, 30 digits)."""
    global ZETA_ZEROS_LE_60
    if ZETA_ZEROS_LE_60 is None:
        old = mp.mp.dps; mp.mp.dps = 30
        zs=[]; k=1
        while True:
            g = mp.zetazero(k).imag
            if g > Tmax: break
            zs.append(float(mp.nstr(g, 20))); k+=1
        mp.mp.dps = old
        ZETA_ZEROS_LE_60 = zs
    return [z for z in ZETA_ZEROS_LE_60 if z <= Tmax]

def build_grid(sigmas, Tmin, Tmax, Tstep, zero_offsets):
    Ts = []
    k = 0
    while True:
        T = Tmin + k*Tstep
        if T > Tmax + 1e-12: break
        Ts.append(("grid", round(T, 6), None)); k += 1
    for g in zeta_zero_heights(Tmax):
        for off in zero_offsets:
            T = g + off
            if Tmin <= T <= Tmax:
                Ts.append(("zero", round(T, 6), g))
    points = []
    for kind, T, g in Ts:
        for s in sigmas:
            points.append({"sigma": str(s), "T": T, "kind": kind, "gamma": g})
    # sigma->0 slope once per T
    slopes = [{"T": T, "kind": kind, "gamma": g} for kind, T, g in Ts]
    return points, slopes

def cutoff(T):
    theta = mp.pi/4 - 1/mp.mpf(T+1)
    c = mp.cos(2*theta)
    M = int(mp.ceil(mp.sqrt(40/c)))
    return theta, c, M, M-1

def e_N_of(T, theta, c, M):
    # round-8 audit (1.1): e_N = 28672 c^-5 M^3 exp(-pi c M^2 - 2 theta T); E_N = sigma e_N
    return 28672*c**-5*M**3*mp.exp(-mp.pi*c*M*M - 2*theta*T)

def _nstr(x, d=32):
    if isinstance(x, (bool, str, int)) or x is None: return x
    if isinstance(x, float): return repr(x)
    if isinstance(x, list): return [_nstr(y, d) for y in x]
    return mp.nstr(x, d)

# ----------------------------------------------------------------------------------
# diagnostic grid point (mpmath)
# ----------------------------------------------------------------------------------

def grid_point_mp(task):
    dps = task["dps"]; mp.mp.dps = dps
    T = mp.mpf(task["T"]); sigma = mp.mpf(Fraction(task["sigma"]))
    theta, c, M, N = cutoff(T)
    p = sigma + 1j*T
    t0 = time.time()
    J = list(mp.diffs(lambda x: head(x, theta, N), p, 2))       # J, J', J''
    h = 4*mp.re(J[1]*mp.conj(J[0]))
    eN = e_N_of(T, theta, c, M)
    E = sigma*eN
    F = list(mp.diffs(reference_xi, p, 1))                      # diagnostic reference F, F'
    H = 4*mp.re(F[1]*mp.conj(F[0]))
    B = 448*M**3/c*mp.exp(-mp.pi*c*M*M)
    fac = mp.exp(theta*T)
    out = {"sigma": task["sigma"], "T": task["T"], "kind": task["kind"], "gamma": task["gamma"],
           "dps": dps, "theta": theta, "c": c, "M": M, "N": N,
           "J0": J[0], "J1": J[1], "J2": J[2],
           "h_N": h, "e_N": eN, "E_N": E, "L_N": h-E, "U_N": h+E,
           "ratio_hN_over_EN": h/E if E != 0 else None,
           "H_reference": H, "observed_H_error": abs(H-h), "H_error_bound_5.2": E,
           "scaled_F_error_j0": fac*abs(F[0]-J[0]), "scaled_B_bound": B,
           "sign_hN": int(mp.sign(h)), "LN_positive_float": bool(h-E > 0),
           "runtime_seconds": time.time()-t0, "claimed_sign_certificate": False}
    return {k: _nstr(v) for k, v in out.items()}

def slope_point_mp(task):
    """sigma->0 slope at p=iT: h_N ~ 4 L1 sigma, L1=j'^2-jj'' with j(T)=J_N(iT) real."""
    dps = task["dps"]; mp.mp.dps = dps
    T = mp.mpf(task["T"])
    theta, c, M, N = cutoff(T)
    p = mp.mpc(0, T)
    t0 = time.time()
    J = list(mp.diffs(lambda x: head(x, theta, N), p, 2))
    j0 = mp.re(J[0]); jp = mp.re(1j*J[1]); jpp = mp.re(-J[2])      # d/dT j(T) = i J'(iT), d2 = -J''
    imag_leak = max(abs(mp.im(J[0])), abs(mp.im(1j*J[1])), abs(mp.im(-J[2])))
    L1 = jp*jp - j0*jpp
    eN = e_N_of(T, theta, c, M)
    out = {"T": task["T"], "kind": task["kind"], "gamma": task["gamma"], "dps": dps, "M": M, "N": N,
           "j": j0, "j_prime": jp, "j_double_prime": jpp, "imag_leak_symmetry_3.6": imag_leak,
           "L1": L1, "e_N": eN, "four_L1_over_eN": 4*L1/eN, "sign_L1": int(mp.sign(L1)),
           "runtime_seconds": time.time()-t0, "claimed_sign_certificate": False}
    return {k: _nstr(v) for k, v in out.items()}

# ----------------------------------------------------------------------------------
# rigorous grid point (python-flint / arb)
# ----------------------------------------------------------------------------------

def _arb_setup(dps):
    from flint import acb, arb, ctx
    ctx.dps = dps
    return acb, arb

def _ray_integrals_arb(acb, arb, p, theta, a, L, sign):
    """J-contribution of one ray for orders j=0,1,2 as rigorous balls on [0,L].
    sign=+1: I_n(p,theta): integrand (t+i th)^j phi(t+i th) e^{p(t+i th)}
    sign=-1: I_n(-p,-theta): integrand (-(t-i th))^j phi(t-i th) e^{-p(t-i th)}  (d/dp brings -(t-i th))."""
    ith = acb(0, theta)*sign
    pp = p*sign
    def mk(j):
        def f(t, analytic):
            z = t + ith
            phi = (4*a*a*(9*z/2).exp() - 6*a*(5*z/2).exp()) * (-a*(2*z).exp()).exp()
            return ((sign*z)**j) * phi * (pp*z).exp()
        return f
    return [acb.integral(mk(j), 0, L) for j in range(3)]

def _tail_bound_arb(arb, theta, T, sigma, a, c, L):
    """Rigorous bound of |int_L^inf integrand| for j<=2 (both rays):
    integrand <= e^{-theta T} e^{(j+sigma)t}(4a^2 e^{9t/2}+6a e^{5t/2}) e^{-beta e^{2t}}, beta=a c,
    u=e^{2t}: <= e^{-theta T}(2a^2+3a) int_U^inf u^3 e^{-beta u} du (exponent <= 2.5 <= 3 for u>=1)."""
    beta = a*c; U = (2*L).exp()
    I3 = (-beta*U).exp()*(U**3/beta + 3*U**2/beta**2 + 6*U/beta**3 + 6/beta**4)
    return (-theta*T).exp()*(2*a*a + 3*a)*I3

def grid_point_arb(task):
    dps = task["dps"]
    acb, arb = _arb_setup(dps)
    T = arb(task["T"]); fr = Fraction(task["sigma"]); sigma = arb(fr.numerator)/fr.denominator
    t1 = T + 1
    theta = arb.pi()/4 - 1/t1
    c = (2*theta).cos()
    M = int(mp.ceil(mp.sqrt(40/float(c.mid()))))          # same integer cutoff rule as the mpmath pass
    N = M - 1
    p = acb(sigma, T)
    t0 = time.time()
    # choose L so that the (n=1) tail bound is below 10^-(dps+8) * e^{-theta T}
    target = arb(10)**(-(dps+8)) * (-theta*T).exp()
    L = arb(2)
    while _tail_bound_arb(arb, theta, T, sigma, arb.pi(), c, L).upper() > target.lower():
        L = L + arb(1)/2
        if L > 12: break
    J = [acb(0), acb(0), acb(0)]
    for n in range(1, N+1):
        a = arb.pi()*n*n
        tb = _tail_bound_arb(arb, theta, T, sigma, a, c, L).upper()
        ball = acb(arb(0, tb), arb(0, tb))
        r1 = _ray_integrals_arb(acb, arb, p, theta, a, L, +1)
        r2 = _ray_integrals_arb(acb, arb, p, theta, a, L, -1)
        for j in range(3):
            J[j] = J[j] + r1[j] + r2[j] + ball + ball
    h = 4*(J[1]*J[0].conjugate()).real
    eN = 28672*c**-5*arb(M)**3*(-arb.pi()*c*M*M - 2*theta*T).exp()
    E = sigma*eN
    LN = h - E; UN = h + E
    def cert(x):
        if x.lower() > 0: return "POSITIVE"
        if x.upper() < 0: return "NEGATIVE"
        return "UNDECIDED"
    # rigorous reference F(p)=xi(1/2+p) via acb zeta/gamma; check (4.2) |F-J_N| <= B e^{-theta T}
    s = acb(arb(1)/2, 0) + p
    F0 = s*(s-1)*(arb.pi()**(-s/2))*(s/2).gamma()*s.zeta()/2
    B = 448*arb(M)**3/c*(-arb.pi()*c*M*M).exp()
    bound42 = B*(-theta*T).exp()
    diff0 = abs(F0 - J[0])
    out = {"sigma": task["sigma"], "T": task["T"], "kind": task["kind"], "gamma": task["gamma"], "dps": dps,
           "M": M, "N": N, "L_truncation": str(L), "theta": str(theta), "c": str(c),
           "J0": str(J[0]), "J1": str(J[1]), "J2": str(J[2]),
           "h_N": str(h), "h_N_mid": str(h.mid()), "h_N_rad": str(h.rad()),
           "e_N": str(eN), "E_N": str(E), "L_N": str(LN), "U_N": str(UN),
           "ratio_hN_over_EN": str(h/E),
           "sign_certificate_h_N": cert(h), "sign_certificate_L_N": cert(LN), "sign_certificate_U_N": cert(UN),
           "F_reference_arb": str(F0), "abs_F_minus_J0": str(diff0), "bound_4.2": str(bound42),
           "bound_4.2_holds_rigorously": bool(diff0.upper() < bound42.lower()),
           "runtime_seconds": time.time()-t0,
           "certificate_scope": "finite point only; no continuum claim"}
    return out

def slope_point_arb(task):
    dps = task["dps"]
    acb, arb = _arb_setup(dps)
    T = arb(task["T"]); t1 = T + 1
    theta = arb.pi()/4 - 1/t1
    c = (2*theta).cos()
    M = int(mp.ceil(mp.sqrt(40/float(c.mid())))); N = M - 1
    p = acb(0, T)
    t0 = time.time()
    target = arb(10)**(-(dps+8)) * (-theta*T).exp()
    L = arb(2)
    while _tail_bound_arb(arb, theta, T, arb(0), arb.pi(), c, L).upper() > target.lower():
        L = L + arb(1)/2
        if L > 12: break
    J = [acb(0), acb(0), acb(0)]
    for n in range(1, N+1):
        a = arb.pi()*n*n
        tb = _tail_bound_arb(arb, theta, T, arb(0), a, c, L).upper()
        ball = acb(arb(0, tb), arb(0, tb))
        r1 = _ray_integrals_arb(acb, arb, p, theta, a, L, +1)
        r2 = _ray_integrals_arb(acb, arb, p, theta, a, L, -1)
        for j in range(3):
            J[j] = J[j] + r1[j] + r2[j] + ball + ball
    jp_c = acb(0, 1)*J[1]; jpp_c = -J[2]
    L1c = jp_c*jp_c - J[0]*jpp_c
    L1 = L1c.real
    imag_leak = max(abs(J[0].imag).upper(), abs(jp_c.imag).upper(), abs(jpp_c.imag).upper(), abs(L1c.imag).upper())
    eN = 28672*c**-5*arb(M)**3*(-arb.pi()*c*M*M - 2*theta*T).exp()
    margin = 4*L1 - eN
    def cert(x):
        if x.lower() > 0: return "POSITIVE"
        if x.upper() < 0: return "NEGATIVE"
        return "UNDECIDED"
    return {"T": task["T"], "kind": task["kind"], "gamma": task["gamma"], "dps": dps, "M": M, "N": N,
            "j": str(J[0].real), "j_prime": str(jp_c.real), "j_double_prime": str(jpp_c.real),
            "imag_leak_symmetry_3.6": str(imag_leak), "L1": str(L1), "e_N": str(eN),
            "four_L1_over_eN": str(4*L1/eN), "sign_certificate_L1": cert(L1),
            "sign_certificate_4L1_minus_eN": cert(margin),
            "runtime_seconds": time.time()-t0, "certificate_scope": "finite point only; no continuum claim"}

# ----------------------------------------------------------------------------------
# drivers
# ----------------------------------------------------------------------------------

def _worker(args):
    kind, task = args
    fn = {"point_mp": grid_point_mp, "slope_mp": slope_point_mp,
          "point_arb": grid_point_arb, "slope_arb": slope_point_arb}[kind]
    try:
        return kind, fn(task), None
    except Exception as e:      # keep the grid going, record the failure
        return kind, task, repr(e)

def run_grid(args):
    sigmas = [Fraction(s) for s in args.sigmas.split(",")]
    offsets = [float(x) for x in args.zero_offsets.split(",")]
    points, slopes = build_grid(sigmas, args.Tmin, args.Tmax, args.Tstep, offsets)
    mode = "arb" if args.arb else "mp"
    tasks = [(f"point_{mode}", dict(pt, dps=args.dps)) for pt in points] + \
            [(f"slope_{mode}", dict(sl, dps=args.dps)) for sl in slopes]
    total = len(tasks)
    print(f"grid: {len(points)} points ({len(sigmas)} sigmas x {len(slopes)} T incl. {sum(1 for s in slopes if s['kind']=='zero')} zero-height T) "
          f"+ {len(slopes)} sigma->0 slopes = {total} tasks | mode={mode} dps={args.dps} workers={args.workers}", flush=True)
    results = {"points": [], "slopes": [], "failures": []}
    t0 = time.time(); done = 0
    with Pool(args.workers) as pool:
        for kind, res, err in pool.imap_unordered(_worker, tasks, chunksize=1):
            done += 1
            if err:
                results["failures"].append({"task": res, "error": err})
                label = f"FAIL {err[:60]}"
            else:
                (results["points"] if kind.startswith("point") else results["slopes"]).append(res)
                if kind.startswith("point"):
                    label = f"sigma={res['sigma']} T={res['T']} h/E={res['ratio_hN_over_EN'][:12]}" + \
                            (f" cert={res['sign_certificate_L_N']}" if mode == "arb" else "")
                else:
                    label = f"slope T={res['T']} 4L1/eN={res['four_L1_over_eN'][:12]}" + \
                            (f" cert={res['sign_certificate_4L1_minus_eN']}" if mode == "arb" else "")
            el = time.time()-t0; eta = el/done*(total-done)
            print(f"[{done}/{total}] {done*100//total}% | ETA {int(eta//60)}m{int(eta%60):02d}s | {label}", flush=True)
            if done % 25 == 0:
                Path(args.out).write_text(json.dumps(results, indent=1))
    results["points"].sort(key=lambda r: (float(r["T"]), float(Fraction(r["sigma"]))))
    results["slopes"].sort(key=lambda r: float(r["T"]))
    results["meta"] = {"mode": mode, "dps": args.dps, "sigmas": [str(s) for s in sigmas],
                       "Tmin": args.Tmin, "Tmax": args.Tmax, "Tstep": args.Tstep, "zero_offsets": offsets,
                       "cutoff_rule": "theta=pi/4-1/(T+1); c=cos 2theta; M=ceil(sqrt(40/c)); N=M-1",
                       "error_rule": "E_N = sigma*e_N, e_N = 28672 c^-5 M^3 exp(-pi c M^2 - 2 theta T)",
                       "runtime_seconds": time.time()-t0, "n_points": len(results["points"]),
                       "n_slopes": len(results["slopes"]), "n_failures": len(results["failures"]),
                       "claimed_sign_certificate": (mode == "arb"),
                       "certificate_scope": "finite grid points only; the continuum is not certified"}
    if mode == "arb":
        pts = results["points"]; sl = results["slopes"]
        results["meta"]["summary"] = {
            "L_N_positive_certified": sum(1 for r in pts if r["sign_certificate_L_N"] == "POSITIVE"),
            "L_N_negative_certified": sum(1 for r in pts if r["sign_certificate_L_N"] == "NEGATIVE"),
            "L_N_undecided": sum(1 for r in pts if r["sign_certificate_L_N"] == "UNDECIDED"),
            "bound_4.2_holds_all": all(r["bound_4.2_holds_rigorously"] for r in pts),
            "slope_4L1_minus_eN_positive": sum(1 for r in sl if r["sign_certificate_4L1_minus_eN"] == "POSITIVE"),
            "slope_4L1_minus_eN_negative": sum(1 for r in sl if r["sign_certificate_4L1_minus_eN"] == "NEGATIVE"),
            "slope_undecided": sum(1 for r in sl if r["sign_certificate_4L1_minus_eN"] == "UNDECIDED")}
    else:
        pts = results["points"]; sl = results["slopes"]
        ratios = [mp.mpf(r["ratio_hN_over_EN"]) for r in pts]
        results["meta"]["summary"] = {
            "min_ratio_hN_over_EN": mp.nstr(min(ratios), 12), "max_ratio_hN_over_EN": mp.nstr(max(ratios), 12),
            "points_with_hN_negative": sum(1 for r in pts if r["sign_hN"] < 0),
            "points_with_LN_negative_float": sum(1 for r in pts if not r["LN_positive_float"]),
            "min_four_L1_over_eN": mp.nstr(min(mp.mpf(r["four_L1_over_eN"]) for r in sl), 12),
            "slopes_with_L1_negative": sum(1 for r in sl if r["sign_L1"] < 0),
            "max_observed_H_error_over_bound": mp.nstr(max(mp.mpf(r["observed_H_error"])/mp.mpf(r["H_error_bound_5.2"]) for r in pts), 12)}
    Path(args.out).write_text(json.dumps(results, indent=1))
    print("summary:", json.dumps(results["meta"]["summary"], indent=1), flush=True)
    print(f"written {args.out} in {time.time()-t0:.0f}s", flush=True)

def run_compare(args):
    A = json.loads(Path(args.compare[0]).read_text()); Bj = json.loads(Path(args.compare[1]).read_text())
    mp.mp.dps = 40
    key = lambda r: (r["sigma"], float(r["T"]))
    bm = {key(r): r for r in Bj["points"]}
    rows = []; worst = mp.mpf(0); sign_mismatch = 0
    for r in A["points"]:
        s = bm.get(key(r))
        if not s: continue
        ha, hb = mp.mpf(r["h_N"]), mp.mpf(s["h_N"])
        rel = abs(ha-hb)/max(abs(hb), mp.mpf("1e-300"))
        worst = max(worst, rel)
        if r["sign_hN"] != s["sign_hN"]: sign_mismatch += 1
        rows.append({"sigma": r["sigma"], "T": r["T"], "rel_diff_hN": mp.nstr(rel, 6),
                     "sign_agree": r["sign_hN"] == s["sign_hN"]})
    sm = {float(r["T"]): r for r in Bj["slopes"]}; worst_s = mp.mpf(0); sign_mismatch_s = 0
    for r in A["slopes"]:
        s = sm.get(float(r["T"]))
        if not s: continue
        la, lb = mp.mpf(r["L1"]), mp.mpf(s["L1"])
        worst_s = max(worst_s, abs(la-lb)/max(abs(lb), mp.mpf("1e-300")))
        if r["sign_L1"] != s["sign_L1"]: sign_mismatch_s += 1
    out = {"files": args.compare, "dps": [A["meta"]["dps"], Bj["meta"]["dps"]],
           "n_common_points": len(rows), "max_rel_diff_hN": mp.nstr(worst, 6), "sign_mismatches_hN": sign_mismatch,
           "max_rel_diff_L1": mp.nstr(worst_s, 6), "sign_mismatches_L1": sign_mismatch_s,
           "clean": sign_mismatch == 0 and sign_mismatch_s == 0 and worst < mp.mpf("1e-20") and worst_s < mp.mpf("1e-20"),
           "rows": rows}
    Path(args.out).write_text(json.dumps(out, indent=1))
    print(json.dumps({k: v for k, v in out.items() if k != "rows"}, indent=1))

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--T',type=int)
    ap.add_argument('--dps',type=int,default=50)
    ap.add_argument('--grid',action='store_true')
    ap.add_argument('--arb',action='store_true',help='rigorous python-flint/arb pass')
    ap.add_argument('--sigmas',default='1/64,1/32,1/16,1/8,1/4')
    ap.add_argument('--Tmin',type=float,default=14.0)
    ap.add_argument('--Tmax',type=float,default=60.0)
    ap.add_argument('--Tstep',type=float,default=0.25)
    ap.add_argument('--zero-offsets',dest='zero_offsets',default='-0.05,0,0.05')
    ap.add_argument('--workers',type=int,default=max(1, os.cpu_count()//2))
    ap.add_argument('--out',default=None)
    ap.add_argument('--compare',nargs=2)
    args=ap.parse_args()
    if args.compare:
        args.out = args.out or 'grid_compare.json'; run_compare(args); sys.exit(0)
    if args.grid:
        args.out = args.out or (Path(__file__).parent/f"grid_{'arb' if args.arb else 'mp'}_dps{args.dps}.json")
        run_grid(args); sys.exit(0)
    if args.T is None:
        ap.error('--T required in legacy mode (or use --grid)')
    start=time.time()
    ans=check(args.T,args.dps)
    ans['runtime_seconds']=time.time()-start
    out=Path(__file__).parent/f'check_T{args.T}_dps{args.dps}.json'
    out.write_text(json.dumps(ans,indent=2))
    print(json.dumps(ans,indent=2))
