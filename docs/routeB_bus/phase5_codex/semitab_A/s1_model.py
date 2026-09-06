"""S1: archimedean Fourier involution F_inf in the log model; DCT-I carrier; validation."""
import numpy as np, mpmath as mp

# ---------- 1. multiplier m(tau) ----------
def m_mp(tau):
    tau = mp.mpf(tau)
    s = mp.mpf(1)/2 - 1j*tau
    return 2*(2*mp.pi)**(-s) * mp.gamma(s) * mp.cos(mp.pi*s/2)

def check_multiplier():
    mp.mp.dps = 40
    out = []
    for tau in [0, 0.5, 1, 3, 10, 40, 200]:
        val = m_mp(tau)
        out.append((tau, float(abs(val)), complex(val)))
    return out

# ---------- 2. direct kernel check: (Fv)(x) = int kappa(x+y) v(y) dy ----------
# consistency of kappa with the multiplier: khat(tau) = m(tau)
def check_kappa_ft(tau):
    mp.mp.dps = 30
    # khat(tau) = int 2 e^{s/2} cos(2 pi e^s) e^{-i tau s} ds = 2 int_0^inf u^{-1/2-i tau} cos(2 pi u) du
    f = lambda u: 2*u**(mp.mpf(-0.5)-1j*tau)*mp.cos(2*mp.pi*u)
    val = mp.quadosc(f, [0, mp.inf], omega=2*mp.pi)
    return complex(val), complex(m_mp(tau))

# ---------- 3. DCT-I self-dual carrier ----------
class Carrier:
    def __init__(self, N):
        self.N = N
        self.delta = 1.0/np.sqrt(2.0*N)
        self.T = N*self.delta
        self.t = np.arange(N+1)*self.delta          # t_0=0 ... t_N=T
        c = np.ones(N+1); c[0] = 0.5; c[-1] = 0.5   # trapezoid weights
        self.c = c
        self.sq = np.sqrt(self.delta*c)             # unitary coords: F~_j = sq_j * f(t_j)
        j = np.arange(N+1)
        self.F = (np.sqrt(2.0/N)*np.sqrt(np.outer(c, c))
                  * np.cos(np.pi*np.outer(j, j)/N))
    def x(self):                                    # log coordinate (t_0 = 0 excluded)
        with np.errstate(divide='ignore'):
            return np.log(self.t)

# ---------- 4. independent prolate eigenvalues (Legendre basis, differential operator) ----------
def slepian_legendre(c, nmax=40, K=400):
    """lambda_n(c) for even n via the prolate differential operator in the normalized
    Legendre basis, then mu_n = 2 beta_0 / sum_k beta_k Pk(0), lambda_n = c mu_n^2/(2 pi).
    Uses only the differential operator + Legendre values: independent of any quadrature
    of the integral kernel."""
    ks = np.arange(0, 2*K, 2)                      # even Legendre degrees only
    n = len(ks)
    d = np.empty(n); e = np.empty(n-1)
    for i, k in enumerate(ks):
        k = float(k)
        d[i] = -k*(k+1) - c**2*(2*k*(k+1)-1)/((2*k+3)*(2*k-1))
    for i in range(n-1):
        k = float(ks[i])
        e[i] = -c**2*(k+1)*(k+2)/((2*k+3)*np.sqrt((2*k+1)*(2*k+5)))
    from scipy.linalg import eigh_tridiagonal
    w, V = eigh_tridiagonal(d, e)
    order = np.argsort(-w)                          # chi_0 > chi_1 > ... (least oscillatory first)
    w = w[order]; V = V[:, order]
    # P_k(0) for even k: (-1)^{k/2} (k-1)!!/k!!  ; normalized \bar P_k = sqrt((2k+1)/2) P_k
    Pk0 = np.empty(n)
    val = 1.0
    for i, k in enumerate(ks):
        if k == 0:
            val = 1.0
        else:
            val = val * (-(k-1.0)/k)                # P_{k}(0) = -(k-1)/k * P_{k-2}(0)
        Pk0[i] = val
    norm = np.sqrt((2*ks+1)/2.0)
    Pbar0 = Pk0*norm
    # int_{-1}^{1} \bar P_k = 0 except k=0: int P_0 = 2, \bar P_0 = sqrt(1/2) P_0 -> int = 2/sqrt(2)
    lams = []
    for j in range(min(nmax, n)):
        b = V[:, j]
        num = b[0]*np.sqrt(2.0)                     # int_{-1}^1 psi = b_0 * 2/sqrt(2)
        den = np.dot(b, Pbar0)
        mu = num/den
        lams.append(c*mu**2/(2*np.pi))
    return np.array(lams)

def slepian_gl(c, ngl=600, nmax=10):
    """cross-check: eigenvalues of the even-sector sinc concentration operator by
    Gauss-Legendre quadrature -- a different discretisation of a different formula."""
    x, w = np.polynomial.legendre.leggauss(ngl)
    # even sector on [0,1]: kernel K(x,y) = (sin(c(x-y))/(pi(x-y)) + sin(c(x+y))/(pi(x+y)))
    x = 0.5*(x+1); w = 0.5*w
    X = x[:, None]; Y = x[None, :]
    def sinc_(a):
        out = np.empty_like(a); small = np.abs(a) < 1e-12
        out[~small] = np.sin(c*a[~small])/(np.pi*a[~small])
        out[small] = c/np.pi
        return out
    K = sinc_(X-Y) + sinc_(X+Y)
    M = np.sqrt(w)[:, None]*K*np.sqrt(w)[None, :]
    ev = np.linalg.eigvalsh(M)[::-1]
    return ev[:nmax]

if __name__ == "__main__":
    print("== |m(tau)| ==")
    for tau, a, v in check_multiplier():
        print(f"  tau={tau:8}  |m|={a:.20f}   m={v}")
    print("== khat(tau) vs m(tau) ==")
    for tau in [0.0, 1.0, 3.0]:
        q, mm = check_kappa_ft(tau)
        print(f"  tau={tau}: quad={q}  m={mm}  diff={abs(q-mm):.3e}")
    print("== Slepian lambda_n(c=2pi), even sector ==")
    c = 2*np.pi
    L1 = slepian_legendre(c, nmax=8)
    L2 = slepian_gl(c, nmax=8)
    for i in range(8):
        print(f"  n={2*i:2d}  legendre/diffop={L1[i]:.16e}   GL-sinc={L2[i]:.16e}  rel.diff={abs(L1[i]-L2[i])/abs(L1[i]):.2e}")
