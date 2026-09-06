"""
Implementation B of the semilocal sign-table probe (S = {infinity, 2}).

Model: log variable x = log u, H = L^2(R, dx).
  f(u) = u^{-1/2} v(log u)   is unitary L^2(R,dx) -> L^2(R_+, du)   [ int |f|^2 du = int |v|^2 dx ]
  (F_inf f)(u) = 2 int_0^inf f(t) cos(2 pi u t) dt
  transported:  (F_inf v)(x) = int kappa(x+y) v(y) dy,  kappa(s) = 2 e^{s/2} cos(2 pi e^s)
  Fourier multiplier (ghat(tau) = int g(x) e^{-i tau x} dx):
      (F_inf v)^(tau) = chi(tau) vhat(-tau)
      chi(tau) = 2 (2pi)^{-1/2 + i tau} Gamma(1/2 - i tau) cos(pi (1/2 - i tau)/2),  |chi| = 1.

Discretisation: uniform grid x_i = (i - i0) * DELTA, DELTA = log 2 / m, N points, torus of length N*DELTA.
Orthonormal coordinates c_i = sqrt(DELTA) v(x_i); operators are N x N matrices in those coordinates.
Dilation by 2 = shift by exactly m grid points, so J_S and B_S are exact circulants.
"""
import numpy as np
import mpmath as mp

LOG2 = float(np.log(2.0))

# ---------------------------------------------------------------- constants
mp.mp.dps = 30
C_A = float(mp.euler + mp.log(8 * mp.pi) + mp.pi / 2)          # 5.372183419225665...
C_A_MP = mp.euler + mp.log(8 * mp.pi) + mp.pi / 2


# ---------------------------------------------------------------- grid
class Grid:
    def __init__(self, m=64, x_min=-38.0, x_max=5.0):
        self.m = m
        self.d = LOG2 / m
        n_left = int(round(-x_min / self.d))
        n_right = int(round(x_max / self.d))
        N = n_left + n_right + 1
        if N % 2 == 0:                      # keep N odd: no Nyquist frequency
            N += 1
            n_right += 1
        self.N = N
        self.i0 = n_left
        self.x = (np.arange(N) - n_left) * self.d
        self.X = N * self.d                 # torus length
        self.rev = (2 * n_left - np.arange(N)) % N
        self.tau = 2.0 * np.pi * np.fft.fftfreq(N, d=self.d)

    def idx_le(self, xc):
        """indices with x <= xc (xc must be a grid point up to rounding)"""
        return np.where(self.x <= xc + 0.5 * self.d)[0]

    def __repr__(self):
        return (f"Grid(m={self.m}, N={self.N}, d={self.d:.6g}, "
                f"x in [{self.x[0]:.4f},{self.x[-1]:.4f}], tau_max={np.pi/self.d:.4g})")


# ---------------------------------------------------------------- chi
def chi_of_tau(tau):
    """archimedean multiplier, computed in mpmath (Gamma and cos individually over/underflow)."""
    out = np.empty(len(tau), dtype=complex)
    two_pi = 2 * mp.pi
    for i, t in enumerate(tau):
        s = mp.mpc(0.5, -float(t))
        val = 2 * mp.power(two_pi, -s) * mp.gamma(s) * mp.cos(mp.pi * s / 2)
        out[i] = complex(val)
    return out


class Fourier:
    """discrete F_inf: exactly unitary, self-adjoint, involutive on the torus."""
    def __init__(self, g: Grid, chi=None):
        self.g = g
        self.chi = chi_of_tau(g.tau) if chi is None else chi
        self.chi_abs_err = float(np.max(np.abs(np.abs(self.chi) - 1.0)))
        self.chi = self.chi / np.abs(self.chi)      # enforce exact unimodularity

    def apply(self, V):
        """V: (N,) or (N,k) array in orthonormal coordinates."""
        W = V[self.g.rev]
        return np.fft.ifft(self.chi[:, None] * np.fft.fft(W, axis=0), axis=0) if W.ndim == 2 \
            else np.fft.ifft(self.chi * np.fft.fft(W))

    def matrix(self):
        return np.real(self.apply(np.eye(self.g.N)))


# ---------------------------------------------------------------- Euler intertwiners J_S, B_S  (S_f = {2})
class EulerS:
    """J_S = sum_{k>=0} 2^{-k/2} U_{-k log2}   (v(x) -> v(x + k log2)),  circulant, exact on this grid.
       J_S^{-1} = I - 2^{-1/2} U_{-log2},  B_S = J_S^{-*} = I - 2^{-1/2} U_{log2}."""
    def __init__(self, g: Grid):
        self.g = g
        r = 2.0 ** -0.5
        # multiplier of U_{-a} is e^{i a tau}; J^{-1} multiplier = 1 - r e^{i log2 tau}
        self.jinv_hat = 1.0 - r * np.exp(1j * LOG2 * g.tau)
        self.j_hat = 1.0 / self.jinv_hat
        self.b_hat = 1.0 - r * np.exp(-1j * LOG2 * g.tau)     # U_{log2}: multiplier e^{-i a tau}
        self.a_S = 1.0 - r
        self.b_S = 1.0 + r

    def _mul(self, hat, V):
        return np.fft.ifft(hat[:, None] * np.fft.fft(V, axis=0), axis=0) if V.ndim == 2 \
            else np.fft.ifft(hat * np.fft.fft(V))

    def J(self, V):    return self._mul(self.j_hat, V)
    def Jinv(self, V): return self._mul(self.jinv_hat, V)
    def B(self, V):    return self._mul(self.b_hat, V)


def build_FS(g: Grid, F: Fourier, E: EulerS):
    """F_S = J_S F_inf J_S^{-1}   (real, symmetric, involutive)."""
    I = np.eye(g.N)
    M = E.J(F.apply(E.Jinv(I)))
    return np.real(M)


# ---------------------------------------------------------------- test functions
def smoothstep(s):
    """C^inf step: 0 for s<=0, 1 for s>=1."""
    s = np.asarray(s, dtype=float)
    out = np.zeros_like(s)
    mid = (s > 0) & (s < 1)
    sm = s[mid]
    a = np.exp(-1.0 / sm)
    b = np.exp(-1.0 / (1.0 - sm))
    out[mid] = a / (a + b)
    out[s >= 1] = 1.0
    return out


def cutoff(x, centre, half, w_frac=0.15):
    """C^inf, = 1 on |x-centre| <= half*(1-w_frac), = 0 on |x-centre| >= half."""
    w = half * w_frac
    return smoothstep((half - np.abs(x - centre)) / w)


def bump(x, b, centre=0.0, half=0.5450, omega=0.0):
    v = np.exp(-(x - centre) ** 2 / (2 * b * b)) * cutoff(x, centre, half)
    if omega != 0.0:
        v = v * np.exp(1j * omega * x)
    return v


# ---------------------------------------------------------------- f_0 (canonical.tex)
def h_ccm(u):
    return (np.pi ** 2 * u ** 4 - 1.5 * np.pi * u ** 2) * np.exp(-np.pi * u ** 2)


def Phi(x, nmax=60):
    x = np.asarray(x, dtype=float)
    u = np.exp(x)
    s = np.zeros_like(u)
    for n in range(1, nmax + 1):
        s = s + h_ccm(n * u)
    return 4.0 * np.exp(x / 2.0) * s


def chi_R(x, R):
    """= 1 on [-R,R], 0 outside [-R-1,R+1], smooth."""
    return smoothstep(R + 1.0 - np.abs(x))
