"""kernel_laguerre.py — spectral factorization of the folded Laguerre kernel K_N.

Run: MAC_SPECTRAL_FACTOR_LAGUERRE_KERNEL_2026-09-18 (Steps A..E).

Folded source (theta = 0, on the axis; Proshka folded doc sect. 1):
    phi_n(t)   = (4 a_n^2 e^{9t/2} - 6 a_n e^{5t/2}) e^{-a_n e^{2t}},   a_n = pi n^2
    Phi_N^fold(t) = sum_{n<=N} phi_n(|t|)                 (even, real, > 0)
    j_N(tau)   = J_N(i tau) = int_R Phi_N^fold(t) e^{i tau t} dt        (real, even)

Laguerre form on the axis:
    L1[j_N](tau) = j_N'(tau)^2 - j_N(tau) j_N''(tau)
Kernel (task eq. (1)):
    K_N(v)     = int_R Phi_N^fold((v+w)/2) Phi_N^fold((v-w)/2) w^2 dw    (>= 0, even)
    Khat_N(tau) = int_R e^{i tau v} K_N(v) dv

Exact identity (derived and verified numerically; the task's "2 L1" carries a
factor-2 slip — the honest factor is 4, sign unaffected):
    Khat_N(tau) = 4 * L1[j_N](tau)

Gasper source (Step A): Phi^G(t)=e^{-a cosh t}, a=2 pi,  j^G(tau)=2 K_{i tau}(a).
Gasper 0801.2996 (2.6)+(2.8) gives, at y=0 (derived in-line):
    L1[K_{i tau}](tau) = int_0^1  [ln(1/t) / (t(1-t))]  [K_{i tau}(a/sqrt t)]^2 dt
i.e. the Laguerre form is a POSITIVE INTEGRAL OF SQUARES (not a single square).
Hence Khat^G(tau) = 16 int_0^1 w(t) [K_{i tau}(a/sqrt t)]^2 dt,  w(t)=ln(1/t)/(t(1-t)).

Numerical policy: mpmath dps 30, FINITE integration ranges (no infinite limits —
the 2026-09-17 mp.quad incident).  Source is super-gaussian; integrate over a tight
window so adaptive quadrature does not miss the peak.  K_N is computed by the stable
positive double integral (1); the equivalent convolution form 4[(t^2 phi)*phi -
(t phi)*(t phi)] suffers catastrophic cancellation for |v|>0 (used only as v=0 check).

No interval arithmetic, no sign certificate, no xi-zero input anywhere in A..E.
"""
from __future__ import annotations
import argparse, json, os, sys, time
from fractions import Fraction
from multiprocessing import Pool
from pathlib import Path

import mpmath as mp
import numpy as np

HERE = Path(__file__).resolve().parent
DPS = 30
mp.mp.dps = DPS

T_CUT = mp.mpf(2)          # Phi_fold(|t|) ~ e^{-a_n e^{2|t|}}, < 1e-60 for |t| > 1.6
T_CUT_G = mp.mpf(4)        # Gasper source e^{-a cosh t} ~ e^{-pi e^{|t|}}, < 1e-60 for |t| > 3.6
SUPPORT = mp.mpf(2) * T_CUT  # K_N(v) supported on |v| <= SUPPORT


# ------------------------------------------------------------------------------
# folded source and its Fourier transform
# ------------------------------------------------------------------------------
def a_n(n):
    return mp.pi * n * n


def phi_n(t, n):
    a = a_n(n)
    return (4 * a * a * mp.exp(mp.mpf(9) * t / 2) - 6 * a * mp.exp(mp.mpf(5) * t / 2)) \
        * mp.exp(-a * mp.exp(2 * t))


def Phi_fold(t, N):
    at = abs(t)
    return mp.fsum(phi_n(at, n) for n in range(1, N + 1))


def _j(tau, N):
    f = lambda t: Phi_fold(t, N) * mp.cos(tau * t)
    return 2 * mp.quad(f, [0, T_CUT])


def _jp(tau, N):
    f = lambda t: -Phi_fold(t, N) * t * mp.sin(tau * t)
    return 2 * mp.quad(f, [0, T_CUT])


def _jpp(tau, N):
    f = lambda t: -Phi_fold(t, N) * t * t * mp.cos(tau * t)
    return 2 * mp.quad(f, [0, T_CUT])


def j_N(tau, N):
    return _j(tau, N)


def j_N_prime(tau, N):
    return _jp(tau, N)


def j_N_dprime(tau, N):
    return _jpp(tau, N)


def L1(tau, N):
    j0, j1, j2 = _j(tau, N), _jp(tau, N), _jpp(tau, N)
    return j1 * j1 - j0 * j2


def Khat_N(tau, N):
    return 4 * L1(tau, N)


# ------------------------------------------------------------------------------
# closed form of j_N via upper incomplete gamma (fast, exact, gamma-class structure)
# ------------------------------------------------------------------------------
def J_n_closed(tau, n):
    """One-sided FT of phi_n: int_0^inf phi_n(t) e^{i tau t} dt
    = a_n^{-1/4 - i tau/2} [2 Gamma(9/4 + i tau/2, a_n) - 3 Gamma(5/4 + i tau/2, a_n)]."""
    an = a_n(n)
    t = mp.mpf(tau) / 2
    base = mp.power(an, mp.mpc('-0.25', 0) - mp.mpc(0, t))
    G94 = mp.gammainc(mp.mpc('2.25', 0) + mp.mpc(0, t), a=an, b=mp.inf, regularized=False)
    G54 = mp.gammainc(mp.mpc('1.25', 0) + mp.mpc(0, t), a=an, b=mp.inf, regularized=False)
    return base * (2 * G94 - 3 * G54)


def j_N_closed(tau, N):
    return 2 * mp.re(mp.fsum(J_n_closed(tau, n) for n in range(1, N + 1)))


def L1_closed(tau, N):
    j0 = j_N_closed(tau, N)
    j1 = mp.diff(lambda x: j_N_closed(x, N), tau, n=1)
    j2 = mp.diff(lambda x: j_N_closed(x, N), tau, n=2)
    return j1 * j1 - j0 * j2


def Khat_N_closed(tau, N):
    return 4 * L1_closed(tau, N)


def _L1_full(tau, N):
    j0, j1, j2 = _j(tau, N), _jp(tau, N), _jpp(tau, N)
    return j0, j1, j2, j1 * j1 - j0 * j2


# ------------------------------------------------------------------------------
# kernel K_N by task eq. (1)  (stable, positive integrand)  and by convolution
# ------------------------------------------------------------------------------
def K_N_double(v, N):
    v = abs(v)
    L = SUPPORT
    if v >= L:
        return mp.mpf(0)
    wlo = v - L
    whi = L - v
    f = lambda w: Phi_fold((v + w) / 2, N) * Phi_fold((v - w) / 2, N) * w * w
    return mp.quad(f, [wlo, whi])


def _conv_tt(v, N):
    f = lambda t: t * t * Phi_fold(t, N) * Phi_fold(v - t, N)
    return mp.quad(f, [-T_CUT, T_CUT])


def _conv_t(v, N):
    f = lambda t: t * Phi_fold(t, N) * (v - t) * Phi_fold(v - t, N)
    return mp.quad(f, [-T_CUT, T_CUT])


def K_N_conv(v, N):
    return 4 * (_conv_tt(v, N) - _conv_t(v, N))


# ------------------------------------------------------------------------------
# band-limited (normalized) kernel and the transform-side H  [verdict (3.1)-(3.3)]
# ------------------------------------------------------------------------------
def Ksigma_N_double(v, N, sigma):
    """K_σ,N(v) = int (w sinh(σw)/σ) Phi((v+w)/2) Phi((v-w)/2) dw.
    Verdict (3.1).  Weight w sinh(σw)/σ -> w^2 as σ->0, so K_σ,N -> K_N."""
    v = abs(v)
    L = SUPPORT
    if v >= L:
        return mp.mpf(0)
    wlo = v - L
    whi = L - v
    s = mp.mpf(sigma)
    f = lambda w: (w * mp.sinh(s * w) / s) * Phi_fold((v + w) / 2, N) * Phi_fold((v - w) / 2, N)
    return mp.quad(f, [wlo, whi])


def F_fold(p, N):
    """F_N^fold(p) = int_R Phi_N^fold(t) e^{p t} dt = 2 int_0^inf Phi cosh(p t) dt."""
    s = mp.re(p)
    tau = mp.im(p)
    fr = lambda t: Phi_fold(t, N) * mp.cosh(s * t) * mp.cos(tau * t)
    fi = lambda t: Phi_fold(t, N) * mp.sinh(s * t) * mp.sin(tau * t)
    return 2 * (mp.quad(fr, [0, T_CUT]) + mp.mpc(0, 1) * mp.quad(fi, [0, T_CUT]))


def F_fold_prime(p, N):
    """F_N^fold'(p) = int_R t Phi_N^fold(t) e^{p t} dt = 2 int_0^inf t Phi sinh(p t) dt."""
    s = mp.re(p)
    tau = mp.im(p)
    fr = lambda t: t * Phi_fold(t, N) * mp.sinh(s * t) * mp.cos(tau * t)
    fi = lambda t: t * Phi_fold(t, N) * mp.cosh(s * t) * mp.sin(tau * t)
    return 2 * (mp.quad(fr, [0, T_CUT]) + mp.mpc(0, 1) * mp.quad(fi, [0, T_CUT]))


def H_fold(sigma, tau, N):
    """H_N(sigma+i tau) = 4 Re(F'(p) conj(F(p)))."""
    p = mp.mpc(sigma, tau)
    F = F_fold(p, N)
    Fp = F_fold_prime(p, N)
    return 4 * mp.re(Fp * mp.conj(F))


# ------------------------------------------------------------------------------
# Gasper source (Step A)
# ------------------------------------------------------------------------------
A_GASPER = mp.mpf(2) * mp.pi


def Phi_G(t):
    return mp.exp(-A_GASPER * mp.cosh(t))


def _jG(tau):
    f = lambda t: Phi_G(t) * mp.cos(tau * t)
    return 2 * mp.quad(f, [0, T_CUT_G])


def _jGp(tau):
    f = lambda t: -Phi_G(t) * t * mp.sin(tau * t)
    return 2 * mp.quad(f, [0, T_CUT_G])


def _jGpp(tau):
    f = lambda t: -Phi_G(t) * t * t * mp.cos(tau * t)
    return 2 * mp.quad(f, [0, T_CUT_G])


def j_G(tau):
    return _jG(tau)


def j_G_prime(tau):
    return _jGp(tau)


def j_G_dprime(tau):
    return _jGpp(tau)


def L1_G(tau):
    j0, j1, j2 = _jG(tau), _jGp(tau), _jGpp(tau)
    return j1 * j1 - j0 * j2


def j_G_besselk(tau):
    return 2 * mp.besselk(mp.mpc(0, tau), A_GASPER).real


def K_besselk_i(tau, arg):
    """K_{i tau}(arg), real for real tau, arg > 0."""
    return mp.besselk(mp.mpc(0, tau), arg).real


def gasper_weight(t):
    """w(t) = ln(1/t) / (t(1-t))  — coefficient from Gasper (2.6)+(2.8) at y=0."""
    return mp.log(1 / t) / (t * (1 - t))


def gasper_rhs(tau, a):
    """16 int_0^1 w(t) [K_{i tau}(a/sqrt t)]^2 dt  (should equal 4 L1_G(tau))."""
    # integrand has endpoint singularities (t=0 log, t=1 pole); split and use mp.quad
    f = lambda t: gasper_weight(t) * K_besselk_i(tau, a / mp.sqrt(t)) ** 2
    return 16 * mp.quad(f, [mp.mpf(0), mp.mpf(1)])


# ------------------------------------------------------------------------------
# cepstrum outer factor (numpy float64; Hilbert via FFT)
# ------------------------------------------------------------------------------
def outer_factor(tau_grid, Kfun, n_tau):
    """Outer (minimum-phase) factor ghat of a nonnegative even K on [0, tau_max].

    ghat = exp(0.5*(log K + i H[log K])).  Even-extends K to [-tau_max, tau_max].
    Returns (tau, K_sampled, ghat_complex).  |ghat|^2 == K by construction.
    """
    tau = np.linspace(0.0, tau_grid, n_tau)
    Kvals = np.array([float(Kfun(t)) for t in tau])
    Kvals = np.maximum(Kvals, 1e-300)
    N = 2 * (n_tau - 1)
    full = np.concatenate([Kvals, Kvals[-2:0:-1]])   # even extension, length N
    logK = np.log(full)
    F = np.fft.rfft(logK)
    kk = np.arange(len(F))
    H = -1j * np.sign(kk) * F
    H[0] = 0.0
    hilb = np.fft.irfft(H, n=N)
    ghat_full = np.exp(0.5 * (logK + 1j * hilb))
    ghat = ghat_full[:n_tau]
    return tau, Kvals, ghat


# ------------------------------------------------------------------------------
# gamma-class basis (Step D)
# ------------------------------------------------------------------------------
def gamma_psi(alpha, beta, tau):
    """Fourier transform of x^alpha e^{-beta x} on x in (0,inf), coordinate x=e^{2t}:
    psi_hat(alpha,beta)(tau) = (1/2) beta^{-(alpha + i tau/2)} Gamma(alpha + i tau/2)."""
    s = mp.mpc(alpha, mp.mpf(tau) / 2)
    return mp.mpf('0.5') * mp.power(beta, -s) * mp.gamma(s)


def gamma_basis_candidates(N):
    """(alpha, beta) candidate set: alpha in {5/4,9/4,13/4,17/4};
    beta in {a_n, 2 a_n, a_n+a_m : n,m <= N}."""
    alphas = [mp.mpf('1.25'), mp.mpf('2.25'), mp.mpf('3.25'), mp.mpf('4.25')]
    betas = set()
    for n in range(1, N + 1):
        betas.add(a_n(n))
        betas.add(2 * a_n(n))
        for m in range(1, N + 1):
            betas.add(a_n(n) + a_n(m))
    return [(a, b) for a in alphas for b in sorted(betas)]


def _nstr(x, d=30):
    if isinstance(x, (bool, str, int, type(None))):
        return x
    if isinstance(x, float):
        return repr(x)
    if isinstance(x, list):
        return [_nstr(y, d) for y in x]
    if isinstance(x, complex):
        return [repr(x.real), repr(x.imag)]
    return mp.nstr(x, d)


# ------------------------------------------------------------------------------
# Step A: Gasper regression
# ------------------------------------------------------------------------------
def stepA(tau_max=100.0, step=0.25, out=None):
    out = out or HERE / "gasper_regression.json"
    taus = np.arange(0.0, tau_max + 1e-12, step)
    rows = []
    worst_abs = mp.mpf(0)
    rel_at_tau0 = None
    min_khat = mp.mpf(1)
    t0 = time.time()
    for i, tau in enumerate(taus):
        tt = mp.mpf(float(tau))
        khat = 4 * L1_G(tt)               # primary: pipeline value
        gasper = gasper_rhs(tt, A_GASPER)        # Gasper identity RHS
        abs_dev = abs(khat - gasper)
        worst_abs = max(worst_abs, abs_dev)
        if rel_at_tau0 is None and tau < 1e-9:
            rel_at_tau0 = float(abs_dev / abs(gasper))
        min_khat = min(min_khat, khat)
        rows.append({
            "tau": float(tau), "khat_G": float(khat),
            "gasper_rhs": float(gasper),
            "abs_dev_from_gasper": float(abs_dev),
            "khat_nonnegative": bool(khat >= -mp.mpf('1e-25')),
        })
        if (i + 1) % 40 == 0:
            print(f"[A {i+1}/{len(taus)}] {int((i+1)/len(taus)*100)}% tau={tau:6.1f} "
                  f"khat={mp.nstr(khat,8)} absdev={mp.nstr(abs_dev,3)}", flush=True)
    result = {
        "source": "Phi^G(t)=exp(-2 pi cosh t); j^G=2 K_{i tau}(2pi)",
        "tau_max": tau_max, "step": step, "dps": DPS,
        "khat_G_min": float(min_khat),
        "khat_G_nonnegative_all": bool(min_khat >= -mp.mpf('1e-25')),
        # identity check vs the Gasper integral (16 int w [K]^2 dt): ABSOLUTE metric,
        # because both sides decay ~ e^{-pi tau} and relative error is meaningless at high tau
        "max_abs_dev_from_gasper_integral": float(worst_abs),
        "rel_dev_from_gasper_at_tau0": rel_at_tau0,
        "gasper_identity_holds": bool(worst_abs < mp.mpf('1e-10')),
        "n_points": len(rows),
        "runtime_seconds": time.time() - t0,
        "rows": rows,
    }
    Path(out).write_text(json.dumps(result, indent=1))
    print("Step A summary:", json.dumps({k: v for k, v in result.items() if k != "rows"}, indent=1))
    return result


def L1_besselk(tau):
    """L1[K_{i tau}(a)] = (d/dtau K)^2 - K (d2/dtau2 K), via besselk numerical derivatives."""
    a = A_GASPER
    K = lambda t: K_besselk_i(t, a)
    Kp = mp.diff(K, mp.mpf(tau), 1)
    Kpp = mp.diff(K, mp.mpf(tau), 2)
    return Kp * Kp - K(mp.mpf(tau)) * Kpp


# ------------------------------------------------------------------------------
# Step B: K_N and Khat_N grids
# ------------------------------------------------------------------------------
def _worker_L1(args):
    tau, N = args
    try:
        j0, j1, j2, L = _L1_full(mp.mpf(tau), N)
        return tau, N, float(j0), float(j1), float(j2), float(L), float(4 * L), None
    except Exception as e:
        return tau, N, None, None, None, None, None, repr(e)


def _worker_K(args):
    v, N = args
    try:
        return v, N, float(K_N_double(mp.mpf(v), N)), None
    except Exception as e:
        return v, N, None, repr(e)


def _worker_Ksigma(args):
    v, N, sigma = args
    try:
        return v, N, sigma, float(Ksigma_N_double(mp.mpf(v), N, mp.mpf(sigma))), None
    except Exception as e:
        return v, N, sigma, None, repr(e)


def _worker_H(args):
    sigma, tau, N = args
    try:
        return sigma, tau, N, float(H_fold(mp.mpf(sigma), mp.mpf(tau), N) / mp.mpf(sigma)), None
    except Exception as e:
        return sigma, tau, N, None, repr(e)


def stepB(workers=None, out=None):
    workers = workers or max(1, os.cpu_count() - 2)
    out = out or HERE
    for N in (1, 2, 3):
        # Khat on tau in [0, 80] step 0.05  (Khat = 4 L1)
        taus = [round(0.05 * k, 6) for k in range(int(80 / 0.05) + 1)]
        tasks = [(t, N) for t in taus]
        print(f"stepB N={N}: Khat on {len(taus)} tau points, workers={workers}", flush=True)
        rows = {}
        t0 = time.time()
        with Pool(workers) as pool:
            for tau, n, j0, j1, j2, L, khat, err in pool.imap_unordered(_worker_L1, tasks, chunksize=8):
                if err:
                    print(f"  FAIL tau={tau}: {err}", flush=True)
                    continue
                rows[tau] = {"tau": tau, "j": j0, "j_prime": j1, "j_dprime": j2,
                             "L1": L, "khat": khat}
        khats = sorted(rows.items())
        # sign-change location
        flips = []
        prev = None
        for tau, r in khats:
            s = 1 if r["khat"] >= 0 else -1
            if prev is not None and s != prev:
                flips.append(tau)
            prev = s
        meta = {"N": N, "tau_range": [0.0, 80.0], "step": 0.05, "dps": DPS,
                "first_sign_flips_tau": flips,
                "khat_min": min(r["khat"] for _, r in khats),
                "khat_max": max(r["khat"] for _, r in khats),
                "runtime_seconds": time.time() - t0}
        Path(out / f"khat_N_{N}.json").write_text(
            json.dumps({"meta": meta, "points": [r for _, r in khats]}, indent=1))
        print(f"  N={N} Khat done: flips at {flips}, min={meta['khat_min']:.3e} "
              f"max={meta['khat_max']:.3e} ({time.time()-t0:.0f}s)", flush=True)

        # K_N on v in [-40, 40] step 0.01 (only |v|<=SUPPORT nonzero)
        vs = [round(0.01 * k, 6) for k in range(int(40 / 0.01) + 1)]  # 0..40
        tasks = [(v, N) for v in vs]
        print(f"stepB N={N}: K_N on {len(vs)} v points", flush=True)
        rows = {}
        t0 = time.time()
        with Pool(workers) as pool:
            for v, n, kv, err in pool.imap_unordered(_worker_K, tasks, chunksize=16):
                if err:
                    print(f"  FAIL v={v}: {err}", flush=True)
                    continue
                rows[v] = kv
        # build full [-40,40] grid (K_N even)
        grid = []
        for k in range(int(40 / 0.01) + 1):
            v = round(0.01 * k, 6)
            grid.append({"v": -v, "K": rows.get(v, 0.0)})
        for k in range(1, int(40 / 0.01) + 1):
            v = round(0.01 * k, 6)
            grid.append({"v": v, "K": rows.get(v, 0.0)})
        meta = {"N": N, "v_range": [-40.0, 40.0], "step": 0.01, "dps": DPS,
                "K_v0": rows.get(0.0), "K_nonnegative": all(x >= 0 for x in rows.values()),
                "runtime_seconds": time.time() - t0}
        Path(out / f"K_N_{N}.json").write_text(json.dumps({"meta": meta, "grid": grid}, indent=1))
        print(f"  N={N} K_N done: K(0)={rows.get(0.0):.6e} ({time.time()-t0:.0f}s)", flush=True)


# ------------------------------------------------------------------------------
# Step B (band version): normalized strip kernel K_σ,N and the strip identity
# ------------------------------------------------------------------------------
SIGMAS = [mp.mpf('0.015625'), mp.mpf('0.125')]  # 1/64, 1/8


def _sigma_tag(sigma):
    return {mp.mpf('0.015625'): "1over64", mp.mpf('0.125'): "1over8"}.get(sigma, "x")


def stepB_band(workers=None, out=None):
    workers = workers or max(1, os.cpu_count() - 2)
    out = out or HERE
    band = {}
    for N in (1, 2, 3):
        for sigma in SIGMAS:
            tag = _sigma_tag(sigma)
            vs = [round(0.01 * k, 6) for k in range(int(40 / 0.01) + 1)]
            tasks = [(v, N, float(sigma)) for v in vs]
            print(f"stepB_band N={N} sigma={tag}: K_σ,N on {len(vs)} v points", flush=True)
            rows = {}
            t0 = time.time()
            with Pool(workers) as pool:
                for v, n, sg, kv, err in pool.imap_unordered(_worker_Ksigma, tasks, chunksize=16):
                    if err:
                        print(f"  FAIL v={v}: {err}", flush=True)
                        continue
                    rows[v] = kv
            grid = []
            for k in range(int(40 / 0.01) + 1):
                v = round(0.01 * k, 6)
                grid.append({"v": -v, "K": rows.get(v, 0.0)})
            for k in range(1, int(40 / 0.01) + 1):
                v = round(0.01 * k, 6)
                grid.append({"v": v, "K": rows.get(v, 0.0)})
            meta = {"N": N, "sigma": float(sigma), "sigma_frac": tag,
                    "v_range": [-40.0, 40.0], "step": 0.01, "dps": DPS,
                    "K_v0": rows.get(0.0), "K_nonnegative": all(x >= 0 for x in rows.values()),
                    "runtime_seconds": time.time() - t0}
            Path(out / f"Ksigma_N_{N}_sigma_{tag}.json").write_text(
                json.dumps({"meta": meta, "grid": grid}, indent=1))
            band[(N, tag)] = {"rows": rows, "meta": meta}
            print(f"  Kσ,N(0)={rows.get(0.0):.6e} ({time.time()-t0:.0f}s)", flush=True)

    # strip identity regression: H(σ+iτ)/σ = 2∫_0^SUPPORT Kσ,N(v) cos(τv) dv
    # on τ in [0,80] step 0.25; transform side via H_fold.
    reg = []
    for N in (1, 2, 3):
        for sigma in SIGMAS:
            tag = _sigma_tag(sigma)
            taus = [round(0.25 * k, 6) for k in range(int(80 / 0.25) + 1)]
            tasks = [(float(sigma), t, N) for t in taus]
            print(f"stepB_band N={N} sigma={tag}: H/σ on {len(taus)} tau points", flush=True)
            rows = {}
            t0 = time.time()
            with Pool(workers) as pool:
                for sg, t, n, hv, err in pool.imap_unordered(_worker_H, tasks, chunksize=8):
                    if err:
                        print(f"  FAIL tau={t}: {err}", flush=True)
                        continue
                    rows[t] = hv
            # finer v-grid for the strip-identity regression (step 0.002 over [0,4]):
            # the saved 0.01 grid does not resolve cos(tau v) at tau up to 80.
            vf = np.arange(0.0, 4.0 + 1e-9, 0.002)
            vf_tasks = [(round(0.002 * k, 7), N, float(sigma)) for k in range(int(4 / 0.002) + 1)]
            Kf = {}
            with Pool(workers) as pool:
                for v, n, sg, kv, err in pool.imap_unordered(_worker_Ksigma, vf_tasks, chunksize=32):
                    if err:
                        continue
                    Kf[v] = kv
            Kf_arr = np.array([Kf.get(round(0.002 * k, 7), 0.0) for k in range(int(4 / 0.002) + 1)])
            worst = 0.0
            worst_abs = 0.0
            for t in taus:
                lhs = rows[t]
                rhs = float(np.trapezoid(2 * Kf_arr * np.cos(t * vf), vf))
                absdev = abs(lhs - rhs)
                worst_abs = max(worst_abs, absdev)
                if abs(lhs) > 1e-6:  # relative error only where the signal is significant
                    worst = max(worst, absdev / abs(lhs))
            reg.append({"N": N, "sigma": tag, "sigma_val": float(sigma),
                        "worst_rel_strip_identity_where_significant": worst,
                        "max_abs_dev_strip_identity": worst_abs,
                        "strip_identity_holds_1e-10": bool(worst_abs < 1e-10),
                        "runtime_seconds": time.time() - t0})
            print(f"  strip identity: max abs dev = {worst_abs:.3e}, "
                  f"worst rel (|H/σ|>1e-6) = {worst:.3e} ({time.time()-t0:.0f}s)", flush=True)
    # σ→0 regression: K_σ,N → K_N and H/σ → 4 L1 (khat from stepB)
    s0 = mp.mpf('0.015625')
    for N in (1, 2, 3):
        ks = Ksigma_N_double(0, N, s0)
        kn = K_N_double(0, N)
        htau0 = H_fold(s0, mp.mpf(0), N) / s0
        L10 = L1(0, N)
        reg.append({"N": N, "regression": "sigma0_limit",
                    "K_sigma_v0": float(ks), "K_N_v0": float(kn),
                    "rel_K": float(abs(ks - kn) / kn),
                    "H_over_sigma_tau0": float(htau0), "4L1_tau0": float(4 * L10),
                    "rel_H": float(abs(htau0 - 4 * L10) / abs(4 * L10))})
        print(f"  sigma0: N={N} rel_K={float(abs(ks-kn)/kn):.2e} rel_H={float(abs(htau0-4*L10)/abs(4*L10)):.2e}", flush=True)
    result = {"strip_identity_regressions": reg,
              "sigma_fractions": [{"frac": "1/64", "val": 0.015625}, {"frac": "1/8", "val": 0.125}]}
    Path(out / "band_regression.json").write_text(json.dumps(result, indent=1))
    print("band_regression.json written")
    return result


def stepC(out=None):
    """Canonical outer (minimum-phase) factor ghat_N on the positivity range."""
    out = out or HERE
    cuts = {1: 19.0, 2: 43.0, 3: 60.0}
    summary = {}
    for N in (1, 2, 3):
        tcut = cuts[N]
        tau, Kvals, ghat = outer_factor(tcut, lambda t: float(Khat_N_closed(mp.mpf(t), N)), 1024)
        recon = np.abs(ghat) ** 2
        maxdev = float(np.max(np.abs(recon - Kvals)))
        summary[N] = {
            "N": N, "tau_cut": tcut, "n_tau": len(tau),
            "max_abs_dev_outer_reconstruction": maxdev,
            "outer_factor_holds": bool(maxdev < 1e-10),
            "tau": [float(t) for t in tau],
            "Khat": [float(k) for k in Kvals],
            "ghat_re": [float(g.real) for g in ghat],
            "ghat_im": [float(g.imag) for g in ghat],
        }
        Path(out / f"outer_factor_N_{N}.json").write_text(json.dumps(summary[N], indent=1))
        print(f"stepC N={N}: tau_cut={tcut}, |ghat|^2-Khat maxdev={maxdev:.3e}", flush=True)
    return summary


def _omp(B, target, max_terms):
    """Greedy orthogonal matching pursuit: select <= max_terms columns of B to fit target."""
    n_basis = B.shape[0]
    residual = target.copy()
    sel = []
    coefs = np.array([])
    for _ in range(max_terms):
        corr = B @ residual
        masked = corr.copy()
        for i in sel:
            masked[i] = 0.0
        best = int(np.argmax(np.abs(masked)))
        sel.append(best)
        A = B[sel].T
        c, *_ = np.linalg.lstsq(A, target, rcond=None)
        coefs = c
        residual = target - A @ c
    return sel, coefs, residual


def stepD(out=None, max_terms=20, tol=1e-10):
    """Fit Khat_N on the positivity range into the gamma class (real basis Re[psi(alpha,beta)])."""
    out = out or HERE
    cuts = {1: 19.0, 2: 43.0, 3: 60.0}
    summary = {}
    for N in (1, 2, 3):
        tcut = cuts[N]
        tau = np.linspace(0.0, tcut, 1024)
        target = np.array([float(Khat_N_closed(mp.mpf(t), N)) for t in tau])
        norm = float(np.linalg.norm(target))
        cands = gamma_basis_candidates(N)
        B = np.array([[float(mp.re(gamma_psi(a, b, mp.mpf(t)))) for t in tau] for (a, b) in cands])
        sel, coefs, residual = _omp(B, target, max_terms)
        rel_res = float(np.linalg.norm(residual) / norm)
        Afull = B.T
        cfull, *_ = np.linalg.lstsq(Afull, target, rcond=None)
        rel_res_full = float(np.linalg.norm(target - Afull @ cfull) / norm)
        passed = bool(rel_res < tol)
        summary[N] = {
            "N": N, "tau_cut": tcut, "max_terms": max_terms,
            "n_candidates": int(B.shape[0]),
            "rel_residual_L2_at_maxterms": rel_res,
            "rel_residual_L2_full_basis": rel_res_full,
            "gamma_class_fit_holds_1e-10": passed,
            "selected_terms": [
                {"alpha": float(cands[i][0]), "beta": float(cands[i][1]), "coef": float(c)}
                for i, c in zip(sel, coefs)
            ],
        }
        Path(out / f"gamma_fit_N_{N}.json").write_text(json.dumps(summary[N], indent=1))
        print(f"stepD N={N}: rel_res({max_terms}t)={rel_res:.3e}  full_basis={rel_res_full:.3e}  "
              f"{'PASS' if passed else 'FAIL'}", flush=True)
    return summary


def stepE(out=None):
    """Residual kernel R_N = K_N - g_N * tilde(g)_N.  Rhat_N = Khat_N * 1_{tau>tau_cut}."""
    out = out or HERE
    cuts = {1: 19.0, 2: 43.0, 3: 60.0}
    summary = {}
    tau_g = np.arange(0.0, 80.0 + 1e-9, 0.05)
    for N in (1, 2, 3):
        tcut = cuts[N]
        Khat = np.array([float(Khat_N_closed(mp.mpf(t), N)) for t in tau_g])
        pospart = np.where(tau_g <= tcut, Khat, 0.0)
        Rhat = Khat - pospart  # == Khat_N for tau > tau_cut, ~0 below
        # R_N(v) = even inverse Fourier of Rhat
        Nf = 2 * (len(tau_g) - 1)
        full = np.concatenate([Rhat[::-1], Rhat[1:]])
        Rv = np.fft.ifft(full).real
        vgrid = np.fft.fftfreq(Nf, d=tau_g[1] - tau_g[0]) * 2 * np.pi
        summary[N] = {
            "N": N, "tau_cut": tcut,
            "Rhat_min": float(np.min(Rhat)),
            "Rhat_zero_on_positivity_range": bool(np.all(np.abs(Rhat[tau_g <= tcut]) < 1e-25)),
            "Rhat_nonpositive_beyond_cut": bool(np.all(Rhat[tau_g > tcut] <= 1e-25)),
            "tau": tau_g.tolist(), "Rhat": Rhat.tolist(),
            "v": [float(v) for v in vgrid], "R_v": [float(r) for r in Rv],
        }
        Path(out / f"remainder_R_N_{N}.json").write_text(json.dumps(summary[N], indent=1))
        print(f"stepE N={N}: Rhat_min={summary[N]['Rhat_min']:.3e}", flush=True)
    Path(out / "remainder_R_N.json").write_text(json.dumps(summary, indent=1))
    return summary


def stepA_outer(out=None):
    """Gasper outer factor ghat^G and the Gasper-basis statement."""
    out = out or HERE
    tau, Kvals, ghat = outer_factor(100.0, lambda t: float(4 * L1_G(mp.mpf(t))), 2048)
    recon = np.abs(ghat) ** 2
    maxdev = float(np.max(np.abs(recon - Kvals)))
    r = {
        "N": "G", "tau_cut": 100.0, "n_tau": len(tau),
        "max_abs_dev_outer_reconstruction": maxdev,
        "outer_factor_holds": bool(maxdev < 1e-10),
        "note": "Khat^G == 16 int_0^1 ln(1/t)/(t(1-t)) [K_{i tau}(a/sqrt t)]^2 dt (continuous Gasper"
                " superposition) to 1.9e-31 abs (stepA); no finite <=8-term basis needed.",
        "tau": [float(t) for t in tau],
        "Khat_G": [float(k) for k in Kvals],
        "ghat_re": [float(g.real) for g in ghat],
        "ghat_im": [float(g.imag) for g in ghat],
    }
    Path(out / "outer_factor_G.json").write_text(json.dumps(r, indent=1))
    print(f"stepA_outer: |ghat^G|^2 - Khat^G maxdev={maxdev:.3e}")
    return r


def smoke():
    print(f"dps={DPS}  T_CUT={mp.nstr(T_CUT,2)}  SUPPORT={mp.nstr(SUPPORT,2)}")
    print("--- K_N(0) double vs conv ---")
    for N in (1, 2, 3):
        print(f"N={N}  K_double(0)={mp.nstr(K_N_double(0,N),14)}  K_conv(0)={mp.nstr(K_N_conv(0,N),14)}")
    print("--- sign near Mythos flips ---")
    for N, taus in ((1, (18, 19, 20)), (2, (42, 43, 44)), (3, (58, 60))):
        print(f"N={N}: " + "  ".join(f"{t}:{'+' if L1(mp.mpf(t),N)>0 else '-'}" for t in taus))
    print("--- Gasper ---")
    for tau in (5, 20, 50):
        jg = j_G(mp.mpf(tau)); jb = j_G_besselk(mp.mpf(tau))
        print(f"tau={tau:3d} jG={mp.nstr(jg,14)} besselk={mp.nstr(jb,14)} d={mp.nstr(abs(jg-jb),3)}")
    print("SMOKE DONE")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", nargs="?", default="smoke")
    ap.add_argument("--workers", type=int, default=None)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    if args.cmd == "smoke":
        smoke()
    elif args.cmd == "stepA":
        stepA(out=args.out)
    elif args.cmd == "stepB":
        stepB(workers=args.workers, out=args.out)
    elif args.cmd == "stepB_band":
        stepB_band(workers=args.workers, out=args.out)
    elif args.cmd == "stepA_outer":
        stepA_outer(out=args.out)
    elif args.cmd == "stepC":
        stepC(out=args.out)
    elif args.cmd == "stepD":
        stepD(out=args.out)
    elif args.cmd == "stepE":
        stepE(out=args.out)
    elif args.cmd == "steps":
        stepC(out=args.out)
        stepD(out=args.out)
        stepE(out=args.out)
    else:
        print(f"unknown cmd: {args.cmd}", file=sys.stderr)
        sys.exit(1)
