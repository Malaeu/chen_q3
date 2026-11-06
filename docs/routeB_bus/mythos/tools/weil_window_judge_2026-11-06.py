"""Weil quadratic form on window m (additive variable, Suzuki 2606.09096 §1.1 normalization).

v supported in [-a, a], a = log(m)/2, so f = v * v~ is supported in [-log m, log m].
W(f) = Pole(f) - Prime(f) - (log 4pi + gamma) f(0) - ArchInt(f)
  Pole(f)  = int f(x)(e^{x/2}+e^{-x/2}) dx  = 2 V(1/2) V(-1/2),  V(s) = int v(y) e^{s y} dy
  Prime(f) = sum_{log n < 2a} Lambda(n)/sqrt(n) (f(log n) + f(-log n))
  ArchInt  = int_0^inf {f(x)+f(-x)-2e^{-x/2}f(0)} e^{x/2}/(e^x-e^{-x}) dx
RH <=> W(v*v~) >= 0 for all v.  Discriminator (K1): W(f) = sum over zeros gamma of |v^(gamma)|^2.
K_m (pole constraints): V(1/2) = V(-1/2) = 0.
"""
import numpy as np, sys
from numpy.polynomial.legendre import leggauss, legval

EG = 0.5772156649015329
K = int(sys.argv[2]) if len(sys.argv) > 2 else 16      # basis size

def vonmangoldt(n):
    for p in range(2, n + 1):
        if n % p == 0:
            k = n
            while k % p == 0: k //= p
            return np.log(p) if k == 1 else 0.0
    return 0.0

def basis(y, a):
    # smooth-ish basis: (1-(y/a)^2)^2 * P_k(y/a), zero outside [-a,a]
    t = y / a
    inside = np.abs(t) < 1
    B = np.zeros((K,) + np.shape(y))
    for k in range(K):
        c = np.zeros(k + 1); c[k] = 1
        B[k] = np.where(inside, (1 - t**2)**2 * legval(t, c), 0.0)
    return B

def F_at(x, a, ny=160):
    """F[j,k] = int v_j(y) v_k(y - x) dy  (= f_{jk}(x)), x >= -2a .. 2a"""
    lo, hi = max(-a, x - a), min(a, x + a)
    if hi <= lo: return np.zeros((K, K))
    u, w = leggauss(ny)
    y = 0.5 * (hi - lo) * u + 0.5 * (hi + lo); w = 0.5 * (hi - lo) * w
    Bj = basis(y, a); Bk = basis(y - x, a)
    return (Bj * w) @ Bk.T

def forms(m):
    a = np.log(m) / 2
    # Gram
    u, w = leggauss(200); y = a * u; w = a * w
    B = basis(y, a); G = (B * w) @ B.T
    Vp = B @ (w * np.exp(y / 2)); Vm = B @ (w * np.exp(-y / 2))
    Pole = np.outer(Vp, Vm) + np.outer(Vm, Vp)            # symmetric version of 2V(1/2)V(-1/2)
    F0 = F_at(0.0, a)
    # archimedean integral on (0, 2a] + analytic tail
    xs, wx = leggauss(240); c = 2 * a
    xs = 0.5 * c * (xs + 1); wx = 0.5 * c * wx
    Arch = np.zeros((K, K))
    for x, wi in zip(xs, wx):
        Fx = F_at(x, a); Fmx = Fx.T                      # f_jk(-x) = f_kj(x)
        Arch += wi * (Fx + Fmx - 2 * np.exp(-x / 2) * F0) * np.exp(x / 2) / (np.exp(x) - np.exp(-x))
    Arch += -F0 * (-np.log(np.tanh(c / 2)))               # int_c^inf -f(0)/sinh x dx
    A = Pole - (np.log(4 * np.pi) + EG) * F0 - Arch       # pole + archimedean
    P = np.zeros((K, K)); nodes = []
    for n in range(2, int(np.ceil(m)) + 1):
        L = vonmangoldt(n)
        if L and np.log(n) < 2 * a - 1e-12:
            Fx = F_at(np.log(n), a); P += L / np.sqrt(n) * (Fx + Fx.T); nodes.append(n)
    A = (A + A.T) / 2; P = (P + P.T) / 2
    return a, G, A, P, Vp, Vm, nodes

def zero_side(m, coef, zeros):
    a = np.log(m) / 2
    u, w = leggauss(3000); y = a * u; w = a * w
    v = coef @ basis(y, a)
    vh = np.exp(1j * np.outer(zeros, y)) @ (w * v)
    return 2 * np.sum(np.abs(vh)**2)                     # +gamma and -gamma

def restrict(M, Q):
    return Q.T @ M @ Q

def lam_min(M, G):
    # generalized eigen M c = lam G c (G SPD)
    Lc = np.linalg.cholesky(G); Li = np.linalg.inv(Lc)
    return np.linalg.eigvalsh(Li @ M @ Li.T)

if __name__ == "__main__":
    zeros = np.load("zeros.npy")
    ms = [float(s) for s in sys.argv[1].split(",")]
    for m in ms:
        a, G, A, P, Vp, Vm, nodes = forms(m)
        W = A - P
        # discriminator: random v, prime side vs zero side
        rng = np.random.default_rng(1); cf = rng.standard_normal(K) / (1 + np.arange(K))**2
        lhs = cf @ W @ cf; rhs = zero_side(m, cf, zeros)
        # K_m: null space of [Vp, Vm]
        C = np.vstack([Vp, Vm]); _, _, Vt = np.linalg.svd(C); Q = Vt[2:].T
        Gk, Ak, Pk, Wk = (restrict(X, Q) for X in (G, A, P, W))
        lw = lam_min(Wk, Gk); la = lam_min(Ak, Gk)
        # how much of archimedean reserve the primes eat: max Rayleigh P/A on K_m (A>0 there?)
        if la[0] > 0:
            eat = lam_min(Pk, Ak)[-1]
        else:
            eat = np.nan
        print(f"m={m:6.2f}  L=log m={2*a:5.3f}  prime powers={nodes}")
        print(f"   check prime-side W={lhs:.6e}  zero-side={rhs:.6e}  rel.diff={abs(lhs-rhs)/abs(rhs):.1e}")
        print(f"   on K_m:  lam_min(W)={lw[0]:.3e}   lam_min(arch only)={la[0]:.3e}   max P/A (prime share of arch reserve)={eat:.4f}")
        print(f"   full space: lam_min(W)={lam_min(W,G)[0]:.3e}")
