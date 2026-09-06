import numpy as np
from numpy.polynomial.legendre import leggauss
from core import Test

L3 = np.log(3.0); HALF = L3/2          # 0.5493061443
A_SH = L3/2

def bump(x, h):                        # C^inf bump on (-h,h), value 1 at 0
    z = np.clip((x/h)**2, 0, 1-1e-16)
    out = np.zeros_like(x)
    m = np.abs(x) < h
    out[m] = np.exp(1.0-1.0/(1.0-z[m]))
    return out

def gauss_bump(b, h):
    return lambda x: np.exp(-x**2/(2*b*b))*bump(x, h)

# --- eta and its scalings ---
_Z = None
def eta(x):
    global _Z
    if _Z is None:
        gx, gw = leggauss(400)
        _Z = float(np.sum(gw*np.where(np.abs(gx) < 1, np.exp(-1/np.maximum(1-gx**2, 1e-300)), 0.0)))
    out = np.zeros_like(np.asarray(x, float))
    m = np.abs(x) < 1
    out[m] = np.exp(-1/(1-np.asarray(x, float)[m]**2))/_Z
    return out
def eta_d(x, d):  return eta(np.asarray(x, float)/d)/d

# --- judge's exactly pole-null tests ---
D0 = (np.log(3.0)-np.log(2.0))/8.0
def w_fun(x, d=D0):
    """(d^2/dx^2 - 1/4) eta_d, by exact second derivative of the bump."""
    x = np.asarray(x, float); z = x/d
    out = np.zeros_like(x); m = np.abs(z) < 1
    zz = z[m]; u = 1-zz**2
    e = np.exp(-1/u)
    # d/dz e = e * (-2z/u^2) ; d2/dz2 e = e*[(-2z/u^2)^2 + (-2/u^2 - 8z^2/u^3)]
    d1 = e*(-2*zz/u**2)
    d2 = e*((2*zz/u**2)**2 + (-2/u**2 - 8*zz**2/u**3))
    global _Z
    eta(0.0)
    out[m] = (d2/(d**3) - 0.25*e/d)/_Z
    return out

def polebump(sign, a=np.log(2.0)):
    """v = [w(x-a/2) (+/- or i) w(x+a/2)] / (sqrt2 ||w||)"""
    c = {'+': 1.0, '-': -1.0, 'i': 1j}[sign]
    def raw(x):
        return w_fun(x-a/2) + c*w_fun(x+a/2)
    gx, gw = leggauss(4000); h = a/2+D0
    xs = h*gx; ws = h*gw
    nrm = np.sqrt(np.sum(ws*np.abs(raw(xs))**2))
    return (lambda x: raw(x)/nrm), h

# --- wide smoothed cosine bumps ---
def wide(b):
    d = b-0.001; dm = 0.001
    gx, gw = leggauss(60); s = dm*gx; wgt = dm*gw*eta_d(dm*gx, dm)
    def fun(x):
        x = np.atleast_1d(np.asarray(x, float))
        Z = x[:, None]-s[None, :]
        V = np.where(np.abs(Z) <= d, np.cos(np.pi*Z/(2*d)), 0.0)
        return V@wgt
    gx2, gw2 = leggauss(6000); xs = b*gx2; ws = b*gw2
    nrm = np.sqrt(np.sum(ws*fun(xs)**2))
    return (lambda x: fun(x)/nrm), b

# --- canonical f_0 and its cutoffs ---
def Phi(x):
    x = np.atleast_1d(np.asarray(x, float))
    if x.size == 0: return x.copy()
    u = np.exp(np.abs(x)); tot = np.zeros_like(x)   # Phi is even; use |x| so that u>=1
    for n in range(1, 400):
        z = n*u
        term = (np.pi**2*z**4 - 1.5*np.pi*z**2)*np.exp(-np.pi*z**2)
        tot += term
        if np.max(np.abs(term)) < 1e-300: break
    return 4*np.exp(np.abs(x)/2)*tot
_A0 = None
_F0S = None
def f0(x):
    global _F0S
    x = np.atleast_1d(np.asarray(x, float))
    if _F0S is None:
        f0_slow(np.array([0.0]))
        from scipy.interpolate import CubicSpline
        xs = np.linspace(0.0, 4.0, 60001)
        _F0S = CubicSpline(xs, Phi(xs)/_A0)
    out = np.zeros_like(x); m = np.abs(x) <= 4.0
    out[m] = _F0S(np.abs(x[m]))
    return out
def f0_slow(x):
    global _A0
    if _A0 is None:
        gx, gw = leggauss(4000); xs = 8*gx; ws = 8*gw
        _A0 = float(np.sqrt(np.sum(ws*Phi(xs)**2)))
    return Phi(x)/_A0
def Anorm():
    f0(0.0); return _A0

def quintic(t):
    t = np.asarray(t, float); out = np.where(t <= 0, 1.0, 0.0)
    m = (t > 0) & (t < 1); tt = t[m]
    out[m] = 1-10*tt**3+15*tt**4-6*tt**5
    return out
def qc(t): return quintic((np.asarray(t, float)-0.01)/0.98)
_GXm, _GWm = leggauss(60)
def chi_R(x, R):
    dm = 1/200.
    s = dm*_GXm; wgt = dm*_GWm*eta_d(s, dm)
    y = np.abs(np.atleast_1d(np.asarray(x, float)))-R
    return qc(y[:, None]-s[None, :])@wgt
def vR(R):
    return (lambda x: chi_R(x, R)*f0(x)), R+1.0
