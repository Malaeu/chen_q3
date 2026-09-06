"""THEOREM_CONTROL_CC20: supp v in [-log2/2, log2/2] and vhat(0)=vhat(+-i/2)=0.
Construction: v = (d^3 - (1/4) d) u  with u = (1-(x/h)^2)^m 1_{|x|<h}  (m=8).
Then int v = 0 (total derivative) and A_+-(v) = int u' (d^2-1/4)e^{+-x/2} = 0 exactly."""
import numpy as np
M = 8
def _p(z, k):
    z = np.asarray(z, float); u = 1-z**2; m = M
    if k == 0: return u**m
    if k == 1: return -2*m*z*u**(m-1)
    if k == 3: return 12*m*(m-1)*z*u**(m-2) - 8*m*(m-1)*(m-2)*z**3*u**(m-3)
    raise ValueError
def wfun(x, h, c=0.0):
    x = np.asarray(x, float); z = (x-c)/h
    out = np.zeros_like(x); msk = np.abs(z) < 1
    zz = z[msk]
    out[msk] = _p(zz, 3)/h**3 - 0.25*_p(zz, 1)/h
    return out
