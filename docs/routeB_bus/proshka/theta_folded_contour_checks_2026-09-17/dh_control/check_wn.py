"""W_N^theta of PROSHKA_RAY_WEIL_COMPRESSION_CROSSWALK_2026-09-17, both sides, and the per-side hygiene checks.

Admissible tests (5):  f_{n,+}^theta(x) = 1_{x>0} phi_n(x + i theta),  f_{n,-}^theta(x) = 1_{x<0} phi_n(-x - i theta)
(6)   s_alpha(p) = e^{-i theta p} r_alpha(p)          [verified to 3.5e-39 in weil_crosswalk_checks.json]

PRIME SIDE (11):
  (W_N)_ab = (1/2pi) int Omega(tau) H_ab(tau) dtau
             - (1/pi) sum_{m>=2} Lambda(m)/sqrt(m) int cos(tau log m) H_ab(tau) dtau
             + e^{i theta} conj(r_a(1/2)) r_b(-1/2) + e^{-i theta} conj(r_a(-1/2)) r_b(1/2)
  H_ab(tau) = conj(s_a(i tau)) s_b(i tau),   Omega(tau) = Re psi(1/4 + i tau/2) - log pi
  Order of operations is mandatory: the tau-integral first for each m, then the convergent sum over m.

ZERO SIDE (13):
  (W_N)_ab = sum_{lambda in Z_c} m_lambda conj(s_a(j lambda)) s_b(lambda),  j lambda = -conj(lambda)
  Zeros of the FULL xi, in centred coordinates lambda = rho - 1/2; on-line lambda = i gamma gives j lambda = lambda,
  so the term is conj(s_a(i gamma)) s_b(i gamma), summed over gamma > 0 and gamma < 0 (the zeros come in pairs +-gamma).

Modes:
  --hygiene   per-side numerical hygiene only: convergence of the zero sum in the height cutoff, of the prime sum
              in m, and stability of the tau-integral under different quadrature splits; hermiticity of each side.
              This produces NO cross-side comparison and NO defect.
  --compare   (11) vs (13) and/or the defect (21) ||W - A||_F^2. GUARDED: refuses to run unless --i-have-registered
              is passed, because these are the owner's P_M3_7 / P_M3_8 and the numbers must not exist before the
              statements are registered.

  python check_wn.py --hygiene --N 4 --dps 30
"""
from __future__ import annotations
import argparse, json, sys, time
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent)); sys.path.insert(0, str(HERE))
import check_contour as cc

ZEROS_FILE = Path.home()/"Documents/Papers/Riehmann/zeta_zeros_100k.txt"

def s_of(n, eps, p, theta):
    r = cc.ray(n, p, theta) if eps > 0 else cc.ray(n, -p, -theta)
    return mp.exp(-1j*theta*p)*r

def index(N):
    return [(n, eps) for n in range(1, N+1) for eps in (+1, -1)]

def Omega(tau):
    return mp.re(mp.digamma(mp.mpf(1)/4 + 1j*tau/2)) - mp.log(mp.pi)

def H_entry(a, b, tau, theta):
    return mp.conj(s_of(a[0], a[1], 1j*tau, theta))*s_of(b[0], b[1], 1j*tau, theta)

# ---------------------------------------------------------------- zero side (13)
def load_zeros(limit=None):
    """Imaginary parts gamma > 0 of the zeta zeros, ascending, from the local Odlyzko table."""
    out = []
    with open(ZEROS_FILE) as f:
        for line in f:
            line = line.strip()
            if not line: continue
            try: g = mp.mpf(line.split()[-1])
            except Exception: continue
            out.append(g)
            if limit and len(out) >= limit: break
    return out

def W_zero_side(N, theta, gammas):
    """Partial sum of (13) over the given gammas (each contributes gamma and -gamma, both on-line, multiplicity 1)."""
    idx = index(N); d = len(idx)
    W = [[mp.mpc(0) for _ in range(d)] for _ in range(d)]
    for g in gammas:
        for sgn in (+1, -1):
            tau = sgn*g
            sv = [s_of(n, eps, 1j*tau, theta) for (n, eps) in idx]
            for i in range(d):
                ci = mp.conj(sv[i])
                for j in range(d): W[i][j] += ci*sv[j]
    return W

# ---------------------------------------------------------------- prime side (11)
def tau_integral(a, b, theta, weight, T_cut, splits):
    f = lambda t: weight(t)*H_entry(a, b, t, theta)
    return mp.quad(f, splits)

# ---------------------------------------------------------------- prime side via the correlation form (9)/(10)
# C_ab(t) = int_{eps x > 0, eta (x-t) > 0} conj(phi_n(eps x + i eps theta)) phi_l(eta (x-t) + i eta theta) dx
# G = C(0);  D_ab = int_0^inf A_0(t) [2G - C(t) - C(-t)] dt,  A_0(t) = e^{-t/2}/(1 - e^{-2t});  c_A = gamma_E + log(8 pi) + pi/2
# (9)  W_ab = D_ab - c_A G_ab - sum_m Lambda(m)/sqrt(m) [C_ab(log m) + C_ab(-log m)] + conj(b_+,a) b_-,b + conj(b_-,a) b_+,b
# Parseval: (1/pi) int H_ab(tau) cos(tau t) dtau = C_ab(t) + C_ab(-t)   <- cross-check of the two forms
CUT = 250.0   # |phi_n(z)| is below e^{-CUT} once a_n e^{2 Re z} > CUT

def C_corr(a, b, t, theta):
    (n, eps), (l, eta) = a, b
    t = mp.mpf(t)
    lo_a, hi_a = (mp.mpf(0), mp.inf) if eps > 0 else (-mp.inf, mp.mpf(0))
    lo_b, hi_b = (t, mp.inf) if eta > 0 else (-mp.inf, t)
    lo = max(lo_a, lo_b); hi = min(hi_a, hi_b)
    if lo >= hi: return mp.mpc(0)
    # the integrand decays doubly exponentially where either argument is large positive; cut there
    an, al = mp.pi*n*n, mp.pi*l*l
    if hi == mp.inf: hi = max(lo, (t if eta > 0 else mp.mpf(0))) + mp.log(CUT/min(an, al))/2 + 2
    if lo == -mp.inf: lo = min(hi, (t if eta < 0 else mp.mpf(0))) - (mp.log(CUT/min(an, al))/2 + 2)
    if lo >= hi: return mp.mpc(0)
    f = lambda x: mp.conj(cc.source_atom(eps*x + 1j*eps*theta, n))*cc.source_atom(eta*(x - t) + 1j*eta*theta, l)
    k = 12; pts = [lo + (hi - lo)*i/k for i in range(k+1)]
    return mp.quad(f, pts)

def A0(t): return mp.exp(-t/2)/(1 - mp.exp(-2*t))

def D_energy(a, b, theta, G, Tmax=40.0):
    """int_0^inf A_0(t)[2G - C(t) - C(-t)] dt; the bracket is O(t) at 0 against A_0 ~ 1/(2t), integrable."""
    f = lambda t: A0(t)*(2*G - C_corr(a, b, t, theta) - C_corr(a, b, -t, theta))
    pts = [mp.mpf(0), mp.mpf("0.01"), mp.mpf("0.1"), mp.mpf(1), mp.mpf(4), mp.mpf(12), mp.mpf(Tmax)]
    return mp.quad(f, pts)

def _entry_hybrid(task):
    """One entry of (11)/(9) in the hybrid form: main term by the Omega tau-integral (no cancellation there, the
    weight is smooth and positive-ish), arithmetic sum by the correlations C(+-log m) (no cancellation, doubly
    exponential decay in log m), pole terms exact. The two forms of the arithmetic term agree by Parseval
    (checked to 1e-5..1e-8), so the hybrid is the cheap route, not a different object."""
    mp.mp.dps = task["dps"]; cc.ADAPTIVE_R = 0.0
    theta = mp.mpf(task["theta"]); a = tuple(task["a"]); b = tuple(task["b"]); T_cut = task["T_cut"]
    splits = [-T_cut + 2*T_cut*k/task["n_split"] for k in range(task["n_split"]+1)]
    main = tau_integral(a, b, theta, Omega, T_cut, splits)/(2*mp.pi)
    pole = pole_entry(a, b, theta)
    terms = {}
    for m, L in sorted(von_mangoldt_support(task["m_max"]).items()):
        lm = mp.log(m)
        terms[m] = L/mp.sqrt(m)*(C_corr(a, b, lm, theta) + C_corr(a, b, -lm, theta))
    return {"a": list(a), "b": list(b), "main": mp.nstr(main, 25), "pole": mp.nstr(pole, 25),
            "terms": {str(m): mp.nstr(v, 25) for m, v in terms.items()}}

def W_prime_hybrid(N, theta, m_cuts, T_cut, n_split, dps, workers, progress=True, want_components=False):
    idx = index(N); d = len(idx); m_cuts = sorted(m_cuts)
    tasks = [{"a": list(a), "b": list(b), "theta": mp.nstr(theta, dps+5), "T_cut": T_cut, "n_split": n_split,
              "dps": dps, "m_max": m_cuts[-1]} for a in idx for b in idx]
    res = {}; t0 = time.time(); total = len(tasks)
    from multiprocessing import Pool
    with Pool(workers) as pool:
        for i, r in enumerate(pool.imap_unordered(_entry_hybrid, tasks, chunksize=1), 1):
            res[(tuple(r["a"]), tuple(r["b"]))] = r
            if progress:
                el = time.time()-t0; eta_ = el/i*(total-i)
                print(f"[{i}/{total}] {i*100//total}% | ETA {int(eta_//60)}m{int(eta_%60):02d}s | entry {tuple(r['a'])}x{tuple(r['b'])}", flush=True)
    Ws = {m: [[mp.mpc(0) for _ in range(d)] for _ in range(d)] for m in m_cuts}
    decay = {}
    for i, a in enumerate(idx):
        for j, b in enumerate(idx):
            r = res[(a, b)]; base = mp.mpc(r["main"]) + mp.mpc(r["pole"]); run = mp.mpc(0)
            ms = sorted(int(k) for k in r["terms"])
            for cut in m_cuts:
                run = mp.fsum(mp.mpc(r["terms"][str(m)]) for m in ms if m <= cut)
                Ws[cut][i][j] = base - run
            if (a, b) == (idx[0], idx[1]):
                decay = {str(m): mp.nstr(abs(mp.mpc(r["terms"][str(m)])), 5) for m in ms}
    if not want_components: return Ws, decay
    comps = {k: [[mp.mpc(0) for _ in range(d)] for _ in range(d)] for k in ("main", "arith", "pole")}
    for i, a in enumerate(idx):
        for j, b in enumerate(idx):
            r = res[(a, b)]
            comps["main"][i][j] = mp.mpc(r["main"]); comps["pole"][i][j] = mp.mpc(r["pole"])
            comps["arith"][i][j] = mp.fsum(mp.mpc(v) for v in r["terms"].values())
    return Ws, decay, comps

def quad_form(M, v):
    d = len(M)
    return mp.fsum(mp.conj(v[i])*M[i][j]*v[j] for i in range(d) for j in range(d))

def W_prime_side_corr(N, theta, m_cuts, progress=True):
    """(9) with the correlation integrals; returns {m_cut: matrix}. No oscillatory tau-integration."""
    idx = index(N); d = len(idx); m_cuts = sorted(m_cuts)
    c_A = mp.euler + mp.log(8*mp.pi) + mp.pi/2
    lam = von_mangoldt_support(m_cuts[-1])
    Ws = {m: [[mp.mpc(0) for _ in range(d)] for _ in range(d)] for m in m_cuts}
    t0 = time.time(); done = 0; total = d*d
    for i, a in enumerate(idx):
        for j, b in enumerate(idx):
            G = C_corr(a, b, 0, theta); D = D_energy(a, b, theta, G); pole = pole_entry(a, b, theta)
            base = D - c_A*G + pole
            run = mp.mpc(0); it = iter(m_cuts); cut = next(it)
            for m in sorted(lam):
                while cut is not None and m > cut:
                    Ws[cut][i][j] = base - run
                    cut = next(it, None)
                if cut is None: break
                lm = mp.log(m)
                run += lam[m]/mp.sqrt(m)*(C_corr(a, b, lm, theta) + C_corr(a, b, -lm, theta))
            while cut is not None:
                Ws[cut][i][j] = base - run; cut = next(it, None)
            done += 1
            if progress:
                el = time.time()-t0; eta_ = el/done*(total-done)
                print(f"[{done}/{total}] {done*100//total}% | ETA {int(eta_//60)}m{int(eta_%60):02d}s | corr entry {a}x{b}", flush=True)
    return Ws

def von_mangoldt_support(m_max):
    """{m: Lambda(m)} for 2 <= m <= m_max (prime powers only)."""
    lam = {}
    for m in range(2, m_max+1):
        mm = m; p = 2; v = mp.mpf(0)
        while p*p <= mm:
            if mm % p == 0:
                while mm % p == 0: mm //= p
                if mm == 1: v = mp.log(p)
                break
            p += 1
        else:
            if mm == m: v = mp.log(m)
        if v: lam[m] = v
    return lam

def pole_entry(a, b, theta):
    ra1 = cc.ray(a[0], mp.mpf(1)/2, theta) if a[1] > 0 else cc.ray(a[0], -mp.mpf(1)/2, -theta)
    ra2 = cc.ray(a[0], -mp.mpf(1)/2, theta) if a[1] > 0 else cc.ray(a[0], mp.mpf(1)/2, -theta)
    rb1 = cc.ray(b[0], mp.mpf(1)/2, theta) if b[1] > 0 else cc.ray(b[0], -mp.mpf(1)/2, -theta)
    rb2 = cc.ray(b[0], -mp.mpf(1)/2, theta) if b[1] > 0 else cc.ray(b[0], mp.mpf(1)/2, -theta)
    return mp.exp(1j*theta)*mp.conj(ra1)*rb2 + mp.exp(-1j*theta)*mp.conj(ra2)*rb1

def W_prime_side(N, theta, m_cuts, T_cut, n_split=8, progress=True):
    """(11) evaluated once per entry; returns {m_cut: matrix} using cumulative sums over the m-integrals, so the
    m-convergence table costs one pass, not one pass per cut. The tau-integral for a given m is done before the
    sum over m, as (11) requires."""
    idx = index(N); d = len(idx); m_cuts = sorted(m_cuts)
    splits = [-T_cut + 2*T_cut*k/n_split for k in range(n_split+1)]
    lam = von_mangoldt_support(m_cuts[-1])
    Ws = {m: [[mp.mpc(0) for _ in range(d)] for _ in range(d)] for m in m_cuts}
    t0 = time.time(); done = 0; total = d*d
    for i, a in enumerate(idx):
        for j, b in enumerate(idx):
            main = tau_integral(a, b, theta, Omega, T_cut, splits)/(2*mp.pi)
            pole = pole_entry(a, b, theta)
            run = mp.mpf(0); cut_it = iter(m_cuts); cut = next(cut_it)
            for m in sorted(lam):
                while m > cut:
                    Ws[cut][i][j] = main - run/mp.pi + pole
                    try: cut = next(cut_it)
                    except StopIteration: cut = None; break
                if cut is None: break
                run += lam[m]/mp.sqrt(m)*tau_integral(a, b, theta, lambda t, m=m: mp.cos(t*mp.log(m)), T_cut, splits)
            while cut is not None:
                Ws[cut][i][j] = main - run/mp.pi + pole
                try: cut = next(cut_it)
                except StopIteration: cut = None
            done += 1
            if progress:
                el = time.time()-t0; eta = el/done*(total-done)
                print(f"[{done}/{total}] {done*100//total}% | ETA {int(eta//60)}m{int(eta%60):02d}s | entry {a}x{b}", flush=True)
    return Ws

def herm_defect(W):
    d = len(W); num = mp.mpf(0); den = mp.mpf(0)
    for i in range(d):
        for j in range(d):
            num += abs(W[i][j] - mp.conj(W[j][i]))**2; den += abs(W[i][j])**2
    return mp.sqrt(num/max(den, mp.mpf(10)**-300))

def frob(W):
    return mp.sqrt(mp.fsum(abs(W[i][j])**2 for i in range(len(W)) for j in range(len(W))))

def diff_frob(A, B):
    return mp.sqrt(mp.fsum(abs(A[i][j] - B[i][j])**2 for i in range(len(A)) for j in range(len(A))))

# ---------------------------------------------------------------- hygiene
def hygiene(a):
    mp.mp.dps = a.dps; cc.ADAPTIVE_R = 0.0
    theta, c, M, _ = cc.cutoff(a.T); theta = mp.mpf(theta); N = a.N
    out = {"meta": {"dps": a.dps, "N": N, "theta": mp.nstr(theta, 20), "T_for_theta": a.T,
                    "note": "per-side hygiene only; no cross-side comparison and no defect (21) — those are the owner's P_M3_7 / P_M3_8"}}
    t0 = time.time()
    # zero side: convergence in the height cutoff
    gam = load_zeros(a.zeros)
    out["meta"]["zeros_file"] = str(ZEROS_FILE); out["meta"]["zeros_loaded"] = len(gam); out["meta"]["gamma_max"] = mp.nstr(gam[-1], 12)
    rows = []; prev = None
    for k in (10, 50, 200, 1000, len(gam)):
        if k > len(gam): continue
        W = W_zero_side(N, theta, gam[:k])
        f = frob(W); step = mp.nstr(diff_frob(W, prev)/f, 5) if prev else None
        rows.append({"zeros_used": k, "gamma_cut": mp.nstr(gam[k-1], 10), "frobenius": mp.nstr(f, 12), "rel_change_vs_previous": step,
                     "hermiticity_defect": mp.nstr(herm_defect(W), 4)})
        prev = W
    out["zero_side_convergence"] = {"rows": rows, "tail_law_expected": "|s|^2 ~ 1/gamma^2 with N(T) ~ T log T/2pi, so the tail beyond Y falls like log(Y)/Y",
                                    "last_rel_change": rows[-1]["rel_change_vs_previous"]}
    # prime side: convergence in m (one pass, cumulative) and stability of the tau-integral
    cuts = sorted({2, 8, 32, a.m_max})
    Ws = W_prime_side(N, theta, cuts, a.T_cut, a.n_split)
    rows2 = []; prev = None
    for m_max in cuts:
        W = Ws[m_max]; f = frob(W); step = mp.nstr(diff_frob(W, prev)/f, 5) if prev else None
        rows2.append({"m_max": m_max, "frobenius": mp.nstr(f, 12), "rel_change_vs_previous": step, "hermiticity_defect": mp.nstr(herm_defect(W), 4)})
        prev = W
    out["prime_side_convergence"] = {"rows": rows2, "T_cut": a.T_cut, "n_split": a.n_split,
                                     "n_prime_powers": len(von_mangoldt_support(cuts[-1]))}
    rows3 = []
    for T_cut in (a.T_cut/2, a.T_cut, 2*a.T_cut):
        W = W_prime_side(N, theta, [8], T_cut, a.n_split, progress=False)[8]
        rows3.append({"T_cut": T_cut, "frobenius": mp.nstr(frob(W), 12)})
    out["prime_side_tau_cut_stability"] = {"rows": rows3, "m_max_used": 8,
        "tail_estimate": "|H| (1+|tau|)^2 is bounded (checked: ~760-820 at tau = 200, 800 for the (1,+)x(1,-) entry), so the tail beyond T_cut falls like 1/T_cut"}
    out["meta"]["runtime_seconds"] = round(time.time()-t0, 1)
    Path(a.out).write_text(json.dumps(out, indent=1))
    print(json.dumps(out["zero_side_convergence"], indent=1)); print(json.dumps(out["prime_side_convergence"], indent=1))
    print(json.dumps(out["prime_side_tau_cut_stability"], indent=1)); print(f"written {a.out}", flush=True)

def eig_hermitian_full(W):
    """Eigenvalues and eigenvectors of the hermitian part; returns (ascending eigenvalues, matching column list)."""
    d = len(W)
    A = mp.matrix(d, d)
    for i in range(d):
        for j in range(d): A[i, j] = (W[i][j] + mp.conj(W[j][i]))/2
    E, V = mp.eighe(A)
    order = sorted(range(d), key=lambda k: mp.re(E[k]))
    return [mp.re(E[k]) for k in order], [[V[i, k] for i in range(d)] for k in order]

def mode_profile(vec, idx):
    """Weight of each ray n in an eigenvector: |v_{n,+}|^2 + |v_{n,-}|^2, normalised to sum 1."""
    w = {}
    for c, (n, eps) in zip(vec, idx): w[n] = w.get(n, mp.mpf(0)) + abs(c)**2
    tot = mp.fsum(w.values())
    return {str(n): mp.nstr(w[n]/tot, 6) for n in sorted(w)}

def eig_hermitian(W):
    """Eigenvalues of the hermitian part, ascending (mpmath eigsy on the 2d x 2d real embedding is avoided:
    use mp.eighe on the complex hermitian matrix)."""
    d = len(W)
    A = mp.matrix(d, d)
    for i in range(d):
        for j in range(d): A[i, j] = (W[i][j] + mp.conj(W[j][i]))/2
    E, _ = mp.eighe(A)
    return sorted([mp.re(E[i]) for i in range(d)])

def A_head(N, theta, p0):
    """HEAD (1.2): A_N = 2(conj(u) v^T + conj(v) u^T), u = r(p0), v = r'(p0), in the same ray index order as index(N)."""
    idx = index(N); u = []; v = []
    for (n, eps) in idx:
        f = (lambda x, n=n, eps=eps: cc.ray(n, x, theta) if eps > 0 else cc.ray(n, -x, -theta))
        dd = list(mp.diffs(f, p0, 1)); u.append(dd[0]); v.append(dd[1])
    d = len(idx)
    return [[2*(mp.conj(u[i])*v[j] + mp.conj(v[i])*u[j]) for j in range(d)] for i in range(d)]

def compare(a):
    mp.mp.dps = a.dps; cc.ADAPTIVE_R = 0.0
    theta, c, M, _ = cc.cutoff(a.T); theta = mp.mpf(theta); N = a.N
    out = {"meta": {"dps": a.dps, "N": N, "theta": mp.nstr(theta, 20), "T_for_theta": a.T, "m_max": a.m_max,
                    "T_cut": a.T_cut, "n_split": a.n_split, "zero_counts": [100, 200, a.zeros],
                    "prime_side_form": "hybrid: Omega tau-integral for the main term, correlations C(+-log m) for the arithmetic sum (the two forms of the arithmetic term agree by Parseval to 1e-5..1e-8)",
                    "registered": ["P_M3_7a", "P_M3_7b", "P_M3_8"], "leak": "AMEND_LEAK_1"}}
    t0 = time.time()
    cuts = sorted({8, 32, a.m_max})
    Ws, decay, comps = W_prime_hybrid(N, theta, cuts, a.T_cut, a.n_split, a.dps, a.workers, want_components=True)
    Wp = Ws[a.m_max]
    out["prime_side"] = {"frobenius": mp.nstr(frob(Wp), 12), "hermiticity_defect": mp.nstr(herm_defect(Wp), 4),
                         "m_convergence": [{"m_max": m, "frobenius": mp.nstr(frob(Ws[m]), 12),
                                            "rel_change": mp.nstr(diff_frob(Ws[m], Ws[cuts[k-1]])/frob(Ws[m]), 5) if k else None}
                                           for k, m in enumerate(cuts)],
                         "term_magnitude_by_m_sample_entry": decay}
    gam = load_zeros(a.zeros)
    rows = []
    counts = [k for k in (100, 200, 400, 800, a.zeros) if k <= a.zeros]
    out["meta"]["zero_counts"] = counts
    out["meta"]["truncation_matching"] = ("the prime side integrates tau over [-T_cut, T_cut]; the zero side over gamma <= gamma_cut. "
        "A comparison is only meaningful when T_cut >> gamma_cut, otherwise the zero side carries spectrum the prime side has cut away. "
        f"Here T_cut = {a.T_cut}, gamma_cut at the largest zero count = {mp.nstr(gam[counts[-1]-1], 8)}.")
    for k in counts:
        Wz = W_zero_side(N, theta, gam[:k])
        D = [[Wp[i][j] - Wz[i][j] for j in range(len(Wz))] for i in range(len(Wz))]
        ev, vecs = eig_hermitian_full(D)
        idx = index(N)
        rows.append({"zeros": k, "gamma_cut": mp.nstr(gam[k-1], 10), "frob_W_zeros": mp.nstr(frob(Wz), 12),
                     "frob_difference": mp.nstr(frob(D), 12), "lambda_min": mp.nstr(ev[0], 8), "lambda_max": mp.nstr(ev[-1], 8),
                     "eigenvalues": [mp.nstr(x, 8) for x in ev],
                     "min_mode_ray_profile": mode_profile(vecs[0], idx),
                     "min_mode_vector": [mp.nstr(c, 8) for c in vecs[0]],
                     "max_mode_ray_profile": mode_profile(vecs[-1], idx)})
    # localise the negative mode: value of the quadratic form of each part of (11) and of the zero side on it
    Wz_last = W_zero_side(N, theta, gam[:counts[-1]])
    Dlast = [[Wp[i][j] - Wz_last[i][j] for j in range(len(Wz_last))] for i in range(len(Wz_last))]
    ev_l, vec_l = eig_hermitian_full(Dlast); v = vec_l[0]
    out["negative_mode_decomposition"] = {
        "zeros_used": counts[-1], "lambda_min": mp.nstr(ev_l[0], 10),
        "ray_profile": mode_profile(v, index(N)),
        "v*_main_v": mp.nstr(mp.re(quad_form(comps["main"], v)), 12),
        "v*_arith_v": mp.nstr(mp.re(quad_form(comps["arith"], v)), 12),
        "v*_pole_v": mp.nstr(mp.re(quad_form(comps["pole"], v)), 12),
        "v*_W_primes_v": mp.nstr(mp.re(quad_form(Wp, v)), 12),
        "v*_W_zeros_v": mp.nstr(mp.re(quad_form(Wz_last, v)), 12),
        "check_sum_equals_lambda_min": mp.nstr(mp.re(quad_form(Wp, v) - quad_form(Wz_last, v)), 12),
        "note": "W_primes = main - arith + pole; W_zeros is a sum of PSD blocks so v* W_zeros v >= 0 always. Whichever part makes v* W_primes v fall below v* W_zeros v is the suspect."}
    out["difference"] = {"rows": rows, "valid_rows": [r["zeros"] for r in rows if mp.mpf(r["gamma_cut"]) < a.T_cut/3],
                         "note": "a row is a valid test only while gamma_cut is well inside the prime-side tau cutoff"}
    r100 = [r for r in rows if r["zeros"] == 100][0]; r200 = [r for r in rows if r["zeros"] == 200][0]
    ratio = mp.mpf(r100["frob_difference"])/mp.mpf(r200["frob_difference"])
    ratios = [{"from": rows[i]["zeros"], "to": rows[i+1]["zeros"], "ratio": mp.nstr(mp.mpf(rows[i]["frob_difference"])/mp.mpf(rows[i+1]["frob_difference"]), 6),
               "both_valid": bool(mp.mpf(rows[i+1]["gamma_cut"]) < a.T_cut/3)} for i in range(len(rows)-1)]
    out["P_M3_7b"] = {"frob_ratio_100_over_200": mp.nstr(ratio, 6), "in_1.8_2.2": bool(mp.mpf("1.8") <= ratio <= mp.mpf("2.2")),
                      "all_consecutive_ratios": ratios,
                      "m_tail_argument": "terms of the arithmetic sum decay doubly exponentially in log m (see term_magnitude_by_m_sample_entry): the m_max 1e4 -> 1e6 part is judged by the measured decay, not by summing 78498 prime powers"}
    last = rows[-1]
    out["P_M3_7a"] = {"lambda_min_at_max_zeros": last["lambda_min"], "frob_difference": last["frob_difference"],
                      "prime_side_error_bar": mp.nstr(mp.mpf(out["prime_side"]["m_convergence"][-1]["rel_change"] or 0)*frob(Wp), 5),
                      "verdict_note": "PSD iff lambda_min >= -(prime-side error bar)"}
    # P_M3_8: rank and defect against A_N(1/4 + 14i)
    evW = eig_hermitian(Wp); nrm = frob(Wp)
    thr = [mp.mpf(10)**-k for k in (6, 8, 10)]
    p0 = mp.mpf(1)/4 + 1j*mp.mpf(14)
    A = A_head(N, theta, p0)
    out["P_M3_8"] = {"eigenvalues_W": [mp.nstr(x, 8) for x in evW],
                     "rank_above_rel_threshold": {str(t): sum(1 for x in evW if abs(x) > t*abs(evW[-1])) for t in thr},
                     "n_negative": sum(1 for x in evW if x < 0), "n_positive": sum(1 for x in evW if x > 0),
                     "defect_frob": mp.nstr(diff_frob(Wp, A), 12), "frob_W": mp.nstr(nrm, 12), "frob_A": mp.nstr(frob(A), 12),
                     "defect_over_frob_W": mp.nstr(diff_frob(Wp, A)/nrm, 6), "p0": "1/4 + 14i",
                     "n_negative_is_NOT_A_TEST": "every zero used is on the line, so the truncated zero side is PSD by construction"}
    out["meta"]["runtime_seconds"] = round(time.time()-t0, 1)
    Path(a.out).write_text(json.dumps(out, indent=1))
    print(json.dumps({k: v for k, v in out.items() if k != "meta"}, indent=1)[:4000])
    print(f"written {a.out}", flush=True)

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--hygiene", action="store_true"); ap.add_argument("--compare", action="store_true")
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--i-have-registered", action="store_true", help="required for --compare: P_M3_7 / P_M3_8 statements are registered in registration_v3.json")
    ap.add_argument("--N", type=int, default=4); ap.add_argument("--dps", type=int, default=30); ap.add_argument("--T", type=float, default=14.0)
    ap.add_argument("--zeros", type=int, default=2000); ap.add_argument("--m-max", type=int, default=64)
    ap.add_argument("--T-cut", type=float, default=200.0); ap.add_argument("--n-split", type=int, default=8)
    ap.add_argument("--out", default=str(HERE/"wn_hygiene.json"))
    a = ap.parse_args()
    if a.compare and not a.i_have_registered:
        raise SystemExit("refused: (11)-vs-(13) and the defect (21) are the owner's P_M3_7 / P_M3_8; register the statements first, then pass --i-have-registered")
    if a.hygiene: hygiene(a)
    elif a.compare: compare(a)
    else: ap.print_help()
