"""Quadrature adapted to the packet bump: both endpoints are infinitely flat, so the
tanh-map + trapezoid gives spectral accuracy (integrand decays doubly exponentially)."""
import mpmath as mp

_CACHE = {}
def tanh_nodes(Y=mp.mpf('4.5'), h=mp.mpf('0.02')):
    key = (str(Y), str(h), mp.mp.dps)
    if key in _CACHE: return _CACHE[key]
    Y = mp.mpf(Y); h = mp.mpf(h)
    n = int(Y/h)
    ys = [h*k for k in range(-n, n+1)]
    ts = [mp.tanh(y) for y in ys]
    wt = [h/mp.cosh(y)**2 for y in ys]
    _CACHE[key] = (ts, wt)
    return ts, wt

def flat_quad(f, a, b, Y='4.5', h='0.02'):
    """int_a^b f, f infinitely flat at both endpoints."""
    ts, wt = tanh_nodes(mp.mpf(Y), mp.mpf(h))
    a = mp.mpf(a); b = mp.mpf(b); m = (a+b)/2; r = (b-a)/2
    return r*sum(w*f(m + r*t) for t, w in zip(ts, wt))

def flat_nodes(a, b, Y='4.5', h='0.02'):
    ts, wt = tanh_nodes(mp.mpf(Y), mp.mpf(h))
    a = mp.mpf(a); b = mp.mpf(b); m = (a+b)/2; r = (b-a)/2
    return [m + r*t for t in ts], [r*w for w in wt]
