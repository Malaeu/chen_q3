"""Decisive cheap test: does a finite carrier reproduce Tr(A(I-P-Q)) + l||v||^2 = L_S ?
Archimedean case S={inf}: L_S = D(v) - c_A ||v||^2 (no prime term)."""
import numpy as np, sys
from s1_model import Carrier
from core import Test, D_minus_cA, D_direct

def build_A(C, T):
    N = C.N
    t = C.t.copy()
    lg = np.log(np.where(t > 0, t, 1.0))
    Lsup = 2*T.half
    A = np.zeros((N+1, N+1))
    # banded in log ratio
    for j in range(1, N+1):
        lo = t[j]*np.exp(-Lsup); hi = t[j]*np.exp(Lsup)
        k0 = max(1, int(np.ceil(lo/C.delta))); k1 = min(N, int(np.floor(hi/C.delta)))
        if k1 < k0: continue
        kk = np.arange(k0, k1+1)
        s = lg[j]-lg[kk]
        val = np.real(T.f(s))
        A[j, kk] = C.delta*np.sqrt(C.c[j]*C.c[kk])*val/np.sqrt(t[j]*t[kk])
    return 0.5*(A+A.T)

if __name__ == "__main__":
    b = 0.2; half = 0.5493
    T = Test(lambda x: np.exp(-x**2/(2*b*b))*np.exp(-1/np.maximum(1-(x/half)**2, 1e-300)), half, "g0.2")
    LS_arch = D_minus_cA(T)
    print(f"||v||^2 = {T.nrm2:.12f}")
    print(f"L_S(arch) = D - c_A||v||^2 = {LS_arch:.12f}   (direct D route: {D_direct(T)-5.3721834192*T.nrm2:.12f})")
    lam = 1.0
    for N in [800, 1600, 3200]:
        C = Carrier(N)
        nlam = int(round(lam/C.delta))
        A = build_A(C, T)
        F = C.F
        trA = np.trace(A)
        trAP = np.trace(A[:nlam+1, :nlam+1])
        FAF = F@A@F
        trAQ = np.trace(FAF[:nlam+1, :nlam+1])
        val = trA-trAP-trAQ
        print(f"  N={N:5d} T={C.T:6.2f} nlam={nlam:4d} | Tr A={trA:12.6f} Tr AP={trAP:12.6f} Tr AQ={trAQ:12.6f} "
              f"=> Tr(A(I-P-Q))={val:12.6f}   vs L_S={LS_arch:.6f}")
