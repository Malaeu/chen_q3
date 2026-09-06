"""Finite carrier: self-dual DCT-I grid; P, F_inf, F_S=J F J^{-1}, Sonin projector, traces."""
import numpy as np
from s1_model import Carrier

class Model:
    def __init__(self, N, lam):
        self.C = Carrier(N); self.N = N; self.lam = lam
        d = self.C.delta
        self.nlam = int(round(lam/d))
        self.on_grid = abs(self.nlam*d - lam) < 1e-12
        self.m = self.nlam+1                       # indices 0..nlam are ran P
        self.F = self.C.F
        sq = self.C.sq
        self.rat = sq[:, None]                     # helper

    # ---- J and J^{-1} in unitary coordinates ----
    def Jinv_cols(self, cols):
        """(J^{-1})[:, cols] as a dense (N+1, len(cols)) array.
           (J^{-1} f)_j = f_j - (sq_j/sq_{2j}) f_{2j}   (j>=1, 2j<=N); identity at j=0."""
        N = self.N; sq = self.C.sq
        out = np.zeros((N+1, len(cols)))
        for c, j0 in enumerate(cols):
            out[j0, c] = 1.0
        # column j0 of J^{-1}: entries at row j0 (=1) and at row j0/2 if j0 even, j0/2>=1
        for c, j0 in enumerate(cols):
            if j0 >= 2 and j0 % 2 == 0:
                j = j0//2
                out[j, c] += -(sq[j]/sq[j0])
        return out

    def Japply(self, X):
        """J @ X ; (J f)_j = sum_{k>=0, 2^k j<=N} (sq_j/sq_{2^k j}) f_{2^k j}, j>=1; (J f)_0=f_0."""
        N = self.N; sq = self.C.sq
        Y = X.copy()
        j = np.arange(1, N+1)
        step = 1
        while True:
            step *= 2
            idx = j[j*step <= N]
            if idx.size == 0: break
            Y[idx] += (sq[idx]/sq[idx*step])[:, None]*X[idx*step]
        return Y

    def FS_cols(self, cols):
        """columns of F_S = J F J^{-1}."""
        Z = self.Jinv_cols(cols)                    # (N+1, k) sparse-ish
        W = self.F @ Z
        return self.Japply(W)

    def FS_rows(self, rows):
        """rows of F_S: (F_S^T)[:, rows] = (J^{-1})^T F J^T ... use F_S^T = J^{-T} F J^T"""
        # (F_S)^T = (J F J^{-1})^T = J^{-T} F J^T
        N = self.N; sq = self.C.sq
        # J^T @ e_r  == column r of J^T == row r of J, as a vector
        E = np.zeros((N+1, len(rows)))
        for c, r in enumerate(rows):
            E[r, c] = 1.0
        JT = self.JTapply(E)
        W = self.F @ JT
        return self.JinvTapply(W)

    def JTapply(self, X):
        N = self.N; sq = self.C.sq
        Y = X.copy()
        j = np.arange(1, N+1)
        step = 1
        while True:
            step *= 2
            idx = j[j*step <= N]
            if idx.size == 0: break
            Y[idx*step] += (sq[idx]/sq[idx*step])[:, None]*X[idx]
        return Y

    def JinvTapply(self, X):
        N = self.N; sq = self.C.sq
        Y = X.copy()
        j = np.arange(2, N+1, 2)
        Y[j] += -(sq[j//2]/sq[j])[:, None]*X[j//2]
        return Y
