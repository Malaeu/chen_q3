"""three_lobe preflight core: exact packet of PROSHKA CHAIN verdict section 8.4 (C25).

Conventions (frozen, from (C1) of PROSHKA_VERDICT_GOAL058_FULL_CHAIN_TO_WEIL_2026-09-07.md):
  A(t) = e^{-t/2}/(1-e^{-2t}),  c_A = gamma + log(8 pi) + pi/2,  w_n = Lambda(n)/sqrt(n)
  U_t f(x) = f(x-t),  C_f(t) = Re int conj(f(x)) f(x+t) dx,  M_pm(f) = int f e^{pm x/2}
  Q(f) = D(f) - c_A||f||^2 - 2 sum_{n>=2} w_n C_f(log n) + 2 Re{ M_+(f) conj(M_-(f)) }
  D(f) = int_0^inf A(t) ||U_t f - f||^2 dt
Hermitian polarization (antilinear in the FIRST argument), all generators real:
  D(f,g)     = int_0^inf A(t) [ 2<f,g> - <f,U_t g> - <f,U_{-t} g> ] dt
  Prime(f,g) = - sum_n w_n [ <f,U_{log n} g> + <f,U_{-log n} g> ]
  Pole(f,g)  = conj(M_+(f)) M_-(g) + conj(M_-(f)) M_+(g)
"""
import mpmath as mp
import sympy as sp

# ---------------------------------------------------------------- packet ----
def packet(dps=45):
    mp.mp.dps = dps
    L2 = mp.log(2); L3 = mp.log(3)
    delta = (L3 - L2) / 8
    return dict(L2=L2, L3=L3, delta=delta, centers=[mp.mpf(0), L2, L3],
                cA=mp.euler + mp.log(8*mp.pi) + mp.pi/2,
                w2=L2/mp.sqrt(2), w3=L3/mp.sqrt(3))

# ------------------------------------------------- bump and derivatives -----
_w = sp.symbols('w')
_g = sp.exp(-1/(1-_w**2))
_gd = [sp.simplify(sp.diff(_g, _w, n)) for n in range(5)]
_gf = [sp.lambdify(_w, e, 'mpmath') for e in _gd]

def eta_derivs(x, delta, nmax=4):
    """[eta(x), eta'(x), ..., eta^{(nmax)}(x)] for the packet bump."""
    w = 2*x/delta
    if abs(w) >= 1:
        return [mp.mpf(0)]*(nmax+1)
    s = 2/delta
    return [ _gf[n](w) * s**n for n in range(nmax+1) ]

def phi_vals(x, delta):
    """[phi_0, phi_1, phi_2](x) = [eta, eta', eta'' - eta/4](x)."""
    d = eta_derivs(x, delta, 2)
    return [d[0], d[1], d[2] - d[0]/4]

# --------------------------------------------------- Gauss-Legendre ---------
_GL_CACHE = {}
def gl_nodes(N):
    """N-point Gauss-Legendre nodes/weights on [-1,1] at current mp precision."""
    key = (N, mp.mp.dps)
    if key in _GL_CACHE: return _GL_CACHE[key]
    import numpy as np
    x0, w0 = np.polynomial.legendre.leggauss(N)
    xs, ws = [], []
    for xi, wi in zip(x0, w0):
        x = mp.mpf(float(xi))
        for _ in range(60):                       # Newton on P_N
            p, dp = mp.legendre(N, x), mp.diff(lambda t: mp.legendre(N, t), x)
            dx = p/dp; x = x - dx
            if abs(dx) < mp.mpf(10)**(-(mp.mp.dps+5)): break
        dp = mp.diff(lambda t: mp.legendre(N, t), x)
        xs.append(x); ws.append(2/((1-x**2)*dp**2))
    _GL_CACHE[key] = (xs, ws)
    return xs, ws

def gl_panel(f, a, b, N, panels=1):
    """Composite N-point GL of f on [a,b]."""
    xs, ws = gl_nodes(N)
    a = mp.mpf(a); b = mp.mpf(b)
    tot = mp.mpf(0); h = (b-a)/panels
    for p in range(panels):
        c = a + h*p; d = c + h
        m = (c+d)/2; r = (d-c)/2
        tot += r*sum(w*f(m + r*x) for x, w in zip(xs, ws))
    return tot

# ------------------------------------------------------------- kernel A ----
def A(t):
    return mp.e**(-t/2) / (1 - mp.e**(-2*t))

def A_reg(t):
    """A(t) - 1/(2t), analytic at t=0 (value 1/4)."""
    if t == 0: return mp.mpf(1)/4
    return A(t) - 1/(2*t)

def A_tail(d):
    """int_d^inf A(t) dt = artanh(y) + arctan(y), y = e^{-d/2}  (=(1/2)(log coth(d/4)) + arctan y)."""
    y = mp.e**(-d/2)
    return mp.atanh(y) + mp.atan(y)
