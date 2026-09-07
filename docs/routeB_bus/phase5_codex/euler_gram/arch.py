"""Archimedean supplier for the Euler-Gram evaluator.

k_inf(xi) = q_inf(xi)/2pi + d_inf(xi)   (SCALARFLOOR/RESONANCE convention)
q_inf(xi) = Re psi(1/4 + i xi/2) - log pi          (exact, scipy digamma)
d_inf(xi) : mellin_d2 table (d_inf.npz, xi = 0(0.25)600), O(xi^-2) beyond.

Sonin phase  theta1(xi) = pi * int_0^xi k_inf
           = theta_RS(xi) + D(xi),   D(xi) = pi * int_0^xi d_inf ,  D(inf)=0
theta_RS = Riemann-Siegel theta = Im logGamma(1/4 + i xi/2) - (xi/2) log pi
(exactly (1/2) int_0^xi q_inf).
"""
import numpy as np, os
from scipy.special import digamma, loggamma
from scipy.interpolate import CubicSpline

HERE = os.path.dirname(os.path.abspath(__file__))
MD2 = os.path.join(HERE, '..', 'mellin_d2')

_z = np.load(os.path.join(MD2, 'd_inf.npz'))
_XI = _z['xi']; _DINF = _z['d']            # xi = 0..600 step 0.25
_XMAX = float(_XI[-1])
_spl = CubicSpline(_XI, _DINF)
# cumulative integral of d_inf on the table, then the analytic tail c/xi
_cum = _spl.antiderivative()
_C_TAIL = float(-_DINF[-1] * _XMAX**2)     # d_inf ~ -C/xi^2  =>  int_xi^inf d = -C/xi
_D_AT_MAX = float(_cum(_XMAX) - _cum(0.0))

def q_inf(xi):
    xi = np.asarray(xi, float)
    return np.real(digamma(0.25 + 0.5j*np.abs(xi))) - np.log(np.pi)

def d_inf(xi):
    x = np.abs(np.asarray(xi, float))
    out = np.where(x <= _XMAX, _spl(np.minimum(x, _XMAX)), -_C_TAIL/np.maximum(x, 1.0)**2)
    return out

def k_inf(xi):
    return q_inf(xi)/(2*np.pi) + d_inf(xi)

def theta_RS(xi):
    x = np.asarray(xi, float)
    return np.imag(loggamma(0.25 + 0.5j*x)) - 0.5*x*np.log(np.pi)

def D_corr(xi):
    """pi * int_0^xi d_inf  (odd in xi)."""
    x = np.asarray(xi, float); ax = np.abs(x)
    inner = np.pi*(_cum(np.minimum(ax, _XMAX)) - _cum(0.0))
    outer = np.pi*(_D_AT_MAX + _C_TAIL*(1.0/np.maximum(ax, _XMAX) - 1.0/_XMAX))
    return np.sign(x)*np.where(ax <= _XMAX, inner, outer)

def theta1(xi):
    return theta_RS(xi) + D_corr(xi)

def kernel(xi, eta):
    """de Branges / model-space reproducing kernel  sin(th(xi)-th(eta)) / (pi (xi-eta))."""
    xi = np.asarray(xi, float); eta = np.asarray(eta, float)
    t1, t2 = theta1(xi), theta1(eta)
    d = xi - eta
    small = np.abs(d) < 1e-7
    dd = np.where(small, 1.0, d)
    out = np.sin(t1 - t2)/(np.pi*dd)
    return np.where(small, k_inf(np.where(small, xi, 0.0)), out)

if __name__ == '__main__':
    print(f"table xi_max={_XMAX}  d_inf(600)={_DINF[-1]:.6e}  C_tail={_C_TAIL:.4f}  D(600)/pi={_D_AT_MAX:.6f}")
    for x in [0.0, 0.5, 1.0, 2.0, 3.0, 5.0, 16.0, 40.0, 120.0, 300.0, 600.0]:
        print(f"  xi={x:7.2f}  q/2pi={q_inf(x)/(2*np.pi):+.8f}  d={d_inf(x):+.8f}  k_inf={k_inf(x):+.8e}  th1={theta1(x):+.6f}  thRS={theta_RS(x):+.6f}")
