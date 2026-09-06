"""Semilocal objects on the DCT-I carrier, with band-limited (alias-free) dilation."""
import numpy as np
from s1_model import Carrier

def build(N):
    C = Carrier(N)
    j = np.arange(N+1)
    c = C.c
    F = C.F
    # "half-frequency DCT": (Fhalf f)_j  ~  h(u_j/2) in unitary coords
    Fhalf = np.sqrt(2.0/N)*np.sqrt(np.outer(c, c))*np.cos(np.pi*np.outer(j, j)/(2.0*N))
    Dil = 0.5*(F@Fhalf)                      # (Dil f)(t) = f(2t), alias-free
    return C, F, Dil

if __name__ == "__main__":
    for N in [400, 800, 1600]:
        C, F, Dil = build(N)
        t = C.t; sq = C.sq
        f = np.exp(-np.pi*t**2)*sq
        g = Dil@f
        gex = np.exp(-np.pi*(2*t)**2)*sq
        print(f"N={N:5d}  ||Dil(gauss)-exact||/||exact|| = {np.linalg.norm(g-gex)/np.linalg.norm(gex):.3e}"
              f"   ||Dil|| = {np.linalg.norm(Dil,2):.8f}  (continuum 2^-1/2 = 0.70710678)")
        Jinv = np.eye(N+1)-Dil
        J = np.linalg.inv(Jinv)
        FS = J@F@Jinv
        print(f"        ||F_S - F_S^T||_max = {np.abs(FS-FS.T).max():.3e}   ||F_S^2-I||_max = {np.abs(FS@FS-np.eye(N+1)).max():.3e}")
        lam = 1.0; nl = int(round(lam/C.delta)); m = nl+1
        blk = 0.5*(FS[:m,:m]+FS[:m,:m].T)
        ev = np.linalg.eigvalsh(blk); i = np.argsort(-np.abs(ev))
        print(f"        alpha_n(F_S) lam=1: {np.array2string(ev[i][:7], precision=8)}")
        ev0 = np.linalg.eigvalsh(F[:m,:m]); i0 = np.argsort(-np.abs(ev0))
        print(f"        alpha_n(F_inf)    : {np.array2string(ev0[i0][:7], precision=8)}")
