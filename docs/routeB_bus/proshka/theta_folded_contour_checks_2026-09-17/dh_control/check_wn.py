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

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--hygiene", action="store_true"); ap.add_argument("--compare", action="store_true")
    ap.add_argument("--i-have-registered", action="store_true", help="required for --compare: P_M3_7 / P_M3_8 statements are registered in registration_v3.json")
    ap.add_argument("--N", type=int, default=4); ap.add_argument("--dps", type=int, default=30); ap.add_argument("--T", type=float, default=14.0)
    ap.add_argument("--zeros", type=int, default=2000); ap.add_argument("--m-max", type=int, default=64)
    ap.add_argument("--T-cut", type=float, default=200.0); ap.add_argument("--n-split", type=int, default=8)
    ap.add_argument("--out", default=str(HERE/"wn_hygiene.json"))
    a = ap.parse_args()
    if a.compare and not a.i_have_registered:
        raise SystemExit("refused: (11)-vs-(13) and the defect (21) are the owner's P_M3_7 / P_M3_8; register the statements first, then pass --i-have-registered")
    if a.hygiene: hygiene(a)
    else: ap.print_help()
