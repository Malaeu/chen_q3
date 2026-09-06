import numpy as np, mpmath as mp
from s1_model import Carrier, slepian_legendre, m_mp

# --- independent identity for m(tau): from the self-dual Gaussian f(t)=e^{-pi t^2} ---
# vhat(tau) = (1/2) pi^{-(1/4 - i tau/2)} Gamma(1/4 - i tau/2), and F v = v forces
#   m(tau) = pi^{-i tau} Gamma(1/4 - i tau/2) / Gamma(1/4 + i tau/2)
mp.mp.dps = 30
print("== m(tau) from the Gamma-quotient identity (independent derivation) ==")
for tau in [0.0, 0.5, 1.0, 3.0, 10.0, 40.0]:
    lhs = m_mp(tau)
    rhs = mp.pi**(-1j*mp.mpf(tau))*mp.gamma(mp.mpf(1)/4-1j*mp.mpf(tau)/2)/mp.gamma(mp.mpf(1)/4+1j*mp.mpf(tau)/2)
    print(f"  tau={tau:6}  |m-mgamma|={float(abs(lhs-rhs)):.3e}")

# --- carrier validation ---
print("\n== DCT-I carrier ==")
for N in [800, 1600, 3200, 6400]:
    C = Carrier(N)
    F = C.F
    err_inv = np.abs(F@F - np.eye(N+1)).max()
    err_sym = np.abs(F-F.T).max()
    # Gaussian fixed point
    g = np.exp(-np.pi*C.t**2)*C.sq
    err_g = np.linalg.norm(F@g-g)/np.linalg.norm(g)
    print(f"  N={N:5d} delta={C.delta:.6f} T={C.T:.3f} | F^2-I |={err_inv:.2e}  |F-F^T|={err_sym:.2e}  Gauss rel.err={err_g:.2e}")

print("\n== alpha_n = eigenvalues of P_lambda F P_lambda on ran P ; alpha_n^2 vs Slepian ==")
for lam in [1.0, np.sqrt(2.0), 2.0]:
    c = 2*np.pi*lam**2
    ref = slepian_legendre(c, nmax=8)
    print(f"  lambda={lam:.6f}  c=2 pi lambda^2={c:.6f}")
    for N in [1600, 3200, 6400]:
        C = Carrier(N)
        nP = int(np.floor(lam/C.delta))+1     # indices j with t_j <= lambda
        blk = C.F[:nP, :nP]
        ev = np.linalg.eigvalsh(blk)
        idx = np.argsort(-np.abs(ev))
        a = ev[idx][:8]
        rel = [abs(a[i]**2-ref[i])/ref[i] for i in range(5)]
        print(f"    N={N:5d} nP={nP:4d}  alpha={np.array2string(a[:5], precision=10)}")
        print(f"              alpha^2 rel.err vs Slepian: {['%.2e'%r for r in rel]}")
