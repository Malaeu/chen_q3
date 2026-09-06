"""Physical-variable model: L^2(R_+, du) even sector.

grid   u_i = i*delta,  i = 0..N,  delta = 1/sqrt(2N),  U_max = N*delta = sqrt(N/2)
weights w_i = delta * k_i,  k_0 = k_N = 1/2, else 1        (trapezoid)
orthonormal coordinates c_i = sqrt(w_i) f(u_i)

F_inf : (F f)(u) = 2 int_0^inf f(t) cos(2 pi u t) dt
        Nystrom matrix  sqrt(w_i w_j) * 2 cos(2 pi u_i u_j)
                      = sqrt(2/N) sqrt(k_i k_j) cos(pi i j / N)   = orthogonal DCT-I
        -> exactly symmetric, exactly involutive.

dilation D: (D f)(u) = f(2u)  ->  exact on this grid (i -> 2i), nilpotent on it.
J_S^{-1} = I - D,  J_S = sum_{k>=0} D^k  (finite: D^{K+1}=0),  F_S = J_S F_inf J_S^{-1}.
"""
import numpy as np


class PhysModel:
    def __init__(self, N):
        self.N = N
        self.delta = 1.0 / np.sqrt(2.0 * N)
        self.u = np.arange(N + 1) * self.delta
        self.U = self.u[-1]
        k = np.ones(N + 1)
        k[0] = k[-1] = 0.5
        self.k = k
        self.w = self.delta * k
        self.n = N + 1

    def Fmat(self):
        i = np.arange(self.N + 1)
        M = np.sqrt(2.0 / self.N) * np.sqrt(self.k)[:, None] * np.sqrt(self.k)[None, :] \
            * np.cos(np.pi * np.outer(i, i) / self.N)
        return M

    def Dmat(self):
        """(D c)_i = sqrt(w_i/w_{2i}) c_{2i} for 1 <= i, 2i <= N ; row 0 = 0."""
        n = self.n
        D = np.zeros((n, n))
        for i in range(1, n):
            j = 2 * i
            if j <= self.N:
                D[i, j] = np.sqrt(self.w[i] / self.w[j])
        return D

    def JS_pair(self):
        D = self.Dmat()
        Jinv = np.eye(self.n) - D
        # J = sum_k D^k  (D nilpotent)
        J = np.eye(self.n)
        Dk = np.eye(self.n)
        while True:
            Dk = Dk @ D
            if np.max(np.abs(Dk)) == 0.0:
                break
            J = J + Dk
        return J, Jinv

    def to_log(self, c, xg):
        """physical orthonormal vector c -> values vtil(x) of the log-model function
           vtil(x) = e^{x/2} f(e^x),  f_i = c_i / sqrt(w_i).  Cubic interpolation in u;
           for u < delta use f(0) (analytic continuation of a smooth f), for u > U -> 0."""
        f = np.zeros_like(c, dtype=c.dtype)
        f[1:] = c[1:] / np.sqrt(self.w[1:])
        f[0] = c[0] / np.sqrt(self.w[0])
        uu = np.exp(xg)
        out = np.zeros(len(xg), dtype=complex)
        inside = uu <= self.U
        if np.iscomplexobj(f):
            re = np.interp(uu[inside], self.u, f.real)
            im = np.interp(uu[inside], self.u, f.imag)
            out[inside] = re + 1j * im
        else:
            out[inside] = np.interp(uu[inside], self.u, f)
        return np.exp(xg / 2.0) * out
