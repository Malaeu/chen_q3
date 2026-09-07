"""Margin integrals on the two-lobe channels.

h_T = (d^2 - 1/4)(e^{iTx} eta_4),  eta_4(x) = (1-(x/delta)^2)^4 on |x|<delta,
delta = (log3-log2)/8;  hhat_T(xi) = -(xi^2+1/4) etahat_4(xi-T).
v_{-,T} = (U_{a/2}-U_{-a/2})h_T/sqrt(2H) :  |vhat_-|^2 = (1-cos a xi)|hhat|^2/H
v_{+,T} = (U_{a/2}+U_{-a/2})h_T/sqrt(2H) :  |vhat_+|^2 = (1+cos a xi)|hhat|^2/H
m(v) = -int |vhat|^2 d_2 dxi = (1/2pi) int |vhat|^2 q_2 - int |vhat|^2 k_2.
Folded to xi>=0 using that d_2, q_2, k_2 are even.
"""
import numpy as np
A = np.log(2.0)
DELTA = (np.log(3.0)-np.log(2.0))/8.0
_z, _w = np.polynomial.legendre.leggauss(80)
_z = 0.5*(_z+1); _w = 0.5*_w

def etahat4(zeta):
    zeta = np.atleast_1d(np.asarray(zeta, float))
    return 2*DELTA*np.sum(_w*(1-_z**2)**4*np.cos(DELTA*np.outer(zeta, _z)), axis=1)

def hhat(xi, T):
    xi = np.asarray(xi, float)
    return -(xi**2+0.25)*etahat4(xi-T).reshape(xi.shape)

def Hnorm(T, R=4000.0, h=0.05):
    x = np.arange(-R, R, h) + h/2
    return float(np.sum(hhat(x, T)**2)*h/(2*np.pi))

def weight(xi, T, sign, H=None):
    """|vhat_sign|^2 folded to xi>=0;  sign=-1 (minus channel), +1 (plus)."""
    xi = np.asarray(xi, float)
    H = Hnorm(T) if H is None else H
    return (1.0 + sign*np.cos(A*xi))*(hhat(xi, T)**2 + hhat(-xi, T)**2)/H

def integrate(xi, f):
    return float(np.trapezoid(f, xi))
