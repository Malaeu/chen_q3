"""Test family (support-matched unless stated)."""
import numpy as np

LOG2 = float(np.log(2.0))
LOG3 = float(np.log(3.0))
L_SUP = 1.09            # support diameter, < log 3 = 1.09861
A_SUP = L_SUP / 2       # 0.545


def smoothstep(s):
    s = np.asarray(s, dtype=float)
    out = np.zeros_like(s)
    mid = (s > 0) & (s < 1)
    sm = s[mid]
    a = np.exp(-1.0 / sm); b = np.exp(-1.0 / (1.0 - sm))
    out[mid] = a / (a + b)
    out[s >= 1] = 1.0
    return out


def cut(x, centre, half, wfrac=0.2):
    return smoothstep((half - np.abs(x - centre)) / (half * wfrac))


def mk_bump(b, centre=0.0, half=A_SUP, omega=0.0):
    def v(x):
        x = np.asarray(x, dtype=float)
        g = np.exp(-(x - centre) ** 2 / (2 * b * b)) * cut(x, centre, half)
        return g * np.exp(1j * omega * x) if omega else g.astype(complex)
    return v


def mk_two(b, sign=+1, shift=LOG2 / 2, half=None):
    if half is None:
        half = A_SUP - shift
    def v(x):
        x = np.asarray(x, dtype=float)
        g1 = np.exp(-(x - shift) ** 2 / (2 * b * b)) * cut(x, shift, half)
        g2 = np.exp(-(x + shift) ** 2 / (2 * b * b)) * cut(x, -shift, half)
        return (g1 + sign * g2).astype(complex)
    return v


# ---- canonical f_0 and its cutoffs -------------------------------------
def h_ccm(u):
    return (np.pi ** 2 * u ** 4 - 1.5 * np.pi * u ** 2) * np.exp(-np.pi * u ** 2)


def Phi(x, nmax=6):
    # Phi is even (functional equation); evaluate the series only at |x| >= 0,
    # where u = e^{|x|} >= 1 and n up to ~4 suffices (h(nu) ~ e^{-pi n^2 u^2}).
    x = np.minimum(np.abs(np.asarray(x, dtype=float)), 30.0)
    u = np.exp(x)
    s = np.zeros_like(u)
    for n in range(1, nmax + 1):
        s = s + h_ccm(n * u)
    return 4.0 * np.exp(x / 2.0) * s


_A_CACHE = {}


def A_norm(dx=2e-5, X=6.0):
    key = (dx, X)
    if key not in _A_CACHE:
        xg = np.arange(-X, X + dx, dx)
        _A_CACHE[key] = float(np.sqrt(dx * np.sum(Phi(xg) ** 2)))
    return _A_CACHE[key]


def mk_vR(R):
    A = A_norm()
    def v(x):
        x = np.asarray(x, dtype=float)
        return (Phi(x) / A * smoothstep(R + 1.0 - np.abs(x))).astype(complex)
    return v


def family():
    out = []
    for b in (0.05, 0.1, 0.2, 0.3, 0.5):
        out.append((f"h_b b={b}", mk_bump(b), A_SUP))
    for b in (0.05, 0.1):
        out.append((f"h_b shift +log2/2 b={b}", mk_bump(b, centre=LOG2 / 2, half=A_SUP - LOG2 / 2),
                    A_SUP))
        out.append((f"h_b shift -log2/2 b={b}", mk_bump(b, centre=-LOG2 / 2, half=A_SUP - LOG2 / 2),
                    A_SUP))
        out.append((f"two-bump (+) b={b}", mk_two(b, +1), A_SUP))
        out.append((f"two-bump (-) b={b}", mk_two(b, -1), A_SUP))
    for w in (2.0, 5.0, 10.0):
        out.append((f"h_b e^(i{w:g}x) b=0.2", mk_bump(0.2, omega=w), A_SUP))
    for R in (0.5, 1.0):
        out.append((f"v_R = chi_R f_0  R={R}", mk_vR(R), R + 1.0))
    return out


# =======================================================================
# additions requested by the coordinator (judge's verdict test family)
# =======================================================================
def eta(x):
    """Z^{-1} exp[-1/(1-x^2)] 1_{|x|<1}, Z = its integral."""
    x = np.asarray(x, dtype=float)
    out = np.zeros_like(x)
    m = np.abs(x) < 1.0
    out[m] = np.exp(-1.0 / (1.0 - x[m] ** 2))
    return out / _ETA_Z


_g = np.linspace(-1, 1, 400001)
_ETA_Z = 1.0
_ETA_Z = float(np.trapz(np.where(np.abs(_g) < 1, np.exp(-1.0 / np.maximum(1 - _g ** 2, 1e-300)), 0.0), _g))


def eta_d(x, d):
    return eta(np.asarray(x) / d) / d


# ---- (2) exactly pole-null two-bump tests ------------------------------
DELTA0 = (np.log(3.0) - np.log(2.0)) / 8.0


def _w_raw(x, d=DELTA0):
    """w = (d_x^2 - 1/4) eta_d, computed analytically."""
    x = np.asarray(x, dtype=float)
    s = x / d
    out = np.zeros_like(s)
    m = np.abs(s) < 1.0
    sm = s[m]
    q = 1.0 - sm ** 2
    e = np.exp(-1.0 / q)
    # eta(s) = e/Z ; eta'(s) = e * (-2 s / q^2)/Z ;
    # eta''(s) = e * ( 4 s^2/q^4 - 2/q^2 - 8 s^2/q^3 )/Z
    e2 = e * (4 * sm ** 2 / q ** 4 - 2.0 / q ** 2 - 8 * sm ** 2 / q ** 3) / _ETA_Z
    e0 = e / _ETA_Z
    out[m] = e2 / d ** 3 - 0.25 * e0 / d          # (1/d)eta''(x/d)/d^2 - (1/4)(1/d)eta(x/d)
    return out


_WN = None


def _wnorm():
    global _WN
    if _WN is None:
        gg = np.linspace(-DELTA0, DELTA0, 200001)
        _WN = float(np.sqrt(np.trapz(_w_raw(gg) ** 2, gg)))
    return _WN


def mk_polenull(kind):
    """kind in {'+', '-', 'i'};  v = [w(x-a/2) (+|-|+i) w(x+a/2)] / (sqrt2 ||w||),  a = log2."""
    a = LOG2
    c = {'+': 1.0, '-': -1.0, 'i': 1j}[kind]
    nrm = np.sqrt(2.0) * _wnorm()
    def v(x):
        x = np.asarray(x, dtype=float)
        return (_w_raw(x - a / 2) + c * _w_raw(x + a / 2)).astype(complex) / nrm
    return v


# ---- (3) wide positive control bumps ------------------------------------
def mk_wide(b):
    """h_d(x) = cos(pi x /(2d)) 1_{|x|<=d}, d = b - 0.001, mollified with eta_{0.001}, normalised."""
    d = b - 0.001
    eps = 0.001
    gg = np.linspace(-b - 0.01, b + 0.01, 400001)
    hh = np.where(np.abs(gg) <= d, np.cos(np.pi * gg / (2 * d)), 0.0)
    dg = gg[1] - gg[0]
    ker = eta_d(np.arange(-int(eps / dg) - 2, int(eps / dg) + 3) * dg, eps) * dg
    sm = np.convolve(hh, ker, mode='same')
    nn = float(np.sqrt(np.trapz(sm ** 2, gg)))
    sm = sm / nn
    def v(x):
        x = np.asarray(x, dtype=float)
        return np.interp(x, gg, sm, left=0.0, right=0.0).astype(complex)
    return v


# ---- (4) canonical cutoffs with the explicit quintic cutoff --------------
def _quintic(t):
    t = np.asarray(t, dtype=float)
    out = np.where(t <= 0, 1.0, 0.0)
    m = (t > 0) & (t < 1)
    tm = t[m]
    out[m] = 1 - 10 * tm ** 3 + 15 * tm ** 4 - 6 * tm ** 5
    return out


_QC = None


def _qc_smooth():
    """q_c(t) = q((t-0.01)/0.98) convolved with eta_{1/200}; tabulated."""
    global _QC
    if _QC is None:
        dg = 1e-5
        gg = np.arange(-0.2, 1.2 + dg, dg)
        base = _quintic((gg - 0.01) / 0.98)
        ns = int(round(0.005 / dg))
        ks = np.arange(-ns - 1, ns + 2) * dg
        ker = eta_d(ks, 1.0 / 200.0) * dg
        ker = ker / ker.sum()
        sm = np.convolve(base, ker, mode='same')
        _QC = (gg, sm)
    return _QC


def mk_vR_quintic(R):
    gg, sm = _qc_smooth()
    A = A_norm()
    def v(x):
        x = np.asarray(x, dtype=float)
        t = np.abs(x) - R
        c = np.interp(t, gg, sm, left=1.0, right=0.0)
        return (Phi(x) / A * c).astype(complex)
    return v


def family_extra():
    out = []
    for k, lbl in (('+', 'v_+'), ('-', 'v_-'), ('i', 'v_i')):
        out.append((f"pole-null {lbl}", mk_polenull(k), LOG2 / 2 + DELTA0))
    for b in (3.0, 4.0, 6.0):
        out.append((f"wide cos bump b={b:g} [OUTSIDE window]", mk_wide(b), b))
    for R in (1.0, 2.0):
        out.append((f"v_R quintic chi_R f_0 R={R:g}", mk_vR_quintic(R), R + 1.0))
    return out


# =======================================================================
# THEOREM_CONTROL_CC20 : S={inf}, lambda=1, supp v subset [-log2/2, log2/2],
# and the three linear conditions  int v = 0,  A_+(v) = 0,  A_-(v) = 0.
# w = d_x (d_x^2 - 1/4) eta_delta satisfies all three exactly:
#   int w = 0 (total derivative);  int w e^{+-x/2} = int eta * (-d)(d^2-1/4)e^{+-x/2} = 0.
# Translates keep the conditions (A_pm(U_q v) = e^{+-q/2} A_pm(v) = 0).
# =======================================================================
def _eta_derivs(s):
    """returns e, e', e'', e''' for e(s) = exp(-1/(1-s^2)) on |s|<1 (0 outside)."""
    s = np.asarray(s, dtype=float)
    out = [np.zeros_like(s) for _ in range(4)]
    m = np.abs(s) < 1.0
    sm = s[m]
    q = 1.0 - sm ** 2
    e = np.exp(-1.0 / q)
    e1 = -2 * sm * e / q ** 2
    G = 4 * sm ** 2 / q ** 4 - 2.0 / q ** 2 - 8 * sm ** 2 / q ** 3
    e2 = e * G
    Gp = (8 * sm / q ** 4 + 32 * sm ** 3 / q ** 5 - 24 * sm / q ** 3 - 48 * sm ** 3 / q ** 4)
    e3 = e * (-2 * sm / q ** 2 * G + Gp)
    for k, val in enumerate((e, e1, e2, e3)):
        out[k][m] = val / _ETA_Z
    return out


def _wthm_raw(x, d):
    """w = d_x (d_x^2 - 1/4) eta_d ,  eta_d(x) = eta(x/d)/d."""
    e, e1, e2, e3 = _eta_derivs(np.asarray(x, dtype=float) / d)
    return e3 / d ** 4 - 0.25 * e1 / d ** 2


_WTN = {}


def _wt_norm(d):
    if d not in _WTN:
        g = np.linspace(-d, d, 400001)
        _WTN[d] = float(np.sqrt(np.trapz(_wthm_raw(g, d) ** 2, g)))
    return _WTN[d]


def mk_thm(d, shift=0.0, kind=None, a=0.0):
    nrm = _wt_norm(d)
    if kind is None:
        def v(x):
            return (_wthm_raw(np.asarray(x, dtype=float) - shift, d) / nrm).astype(complex)
        return v
    c = {'+': 1.0, '-': -1.0, 'i': 1j}[kind]
    def v(x):
        x = np.asarray(x, dtype=float)
        return ((_wthm_raw(x - a, d) + c * _wthm_raw(x + a, d)) / (np.sqrt(2.0) * nrm)).astype(complex)
    return v


def family_thm():
    H = LOG2 / 2
    out = []
    for d in (0.05, 0.1, 0.2, 0.3):
        out.append((f"THM w_d d={d:g}", mk_thm(d), H))
    for k, lbl in (('+', '+'), ('-', '-'), ('i', 'i')):
        out.append((f"THM two-bump({lbl}) d=0.08 a=0.25", mk_thm(0.08, kind=k, a=0.25), H))
    out.append((f"THM w_d d=0.1 shifted +0.2", mk_thm(0.1, shift=0.2), H))
    return out
