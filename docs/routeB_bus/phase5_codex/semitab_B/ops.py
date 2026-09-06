"""Operator side.  F_inf = exact DCT-I involution on the grid u_i = i*delta, delta = 1/sqrt(2N).

Euler intertwiner: B_S = I - (1/2)H, (H f)(u) = f(u/2), built EXACTLY from the DCT
(halving only lowers frequency, so it never aliases; the opposite map f -> f(2u) doubles
the bandwidth and DOES alias on a Nyquist-critical grid, so it is never used).
F_S = B_S F_inf B_S^{-1} is an exact involution but only approximately symmetric on the
grid (the continuum identity F D_2 = (1/2) D_{1/2} F needs the untruncated line).
Therefore the pair is built from SUBSPACES, which are accurate:
   ran Q = F_S(ran P)  computed by applying B_S F B_S^{-1} to ran P, then orthonormalised.
P and Q are then honest orthogonal projections and the Halmos block algebra is exact:
   alpha_n^2 = eig(P Q P|ran P),  zeta_n = (Q xi_n - alpha^2 xi_n)/(alpha s),
   D_S = P + Q - (I - S_S)  with block form [[a^2, a s],[a s, -a^2]].
"""
import numpy as np
from phys import PhysModel

LOG2 = float(np.log(2.0))


class SemiLocal:
    def __init__(self, N, semilocal=True, verbose=True):
        self.M = PhysModel(N)
        M = self.M
        i = np.arange(N + 1)
        sk = np.sqrt(M.k)
        self.F = np.sqrt(2.0 / N) * sk[:, None] * sk[None, :] * np.cos(np.pi * np.outer(i, i) / N)
        self.semilocal = semilocal
        self.inv_err = float(np.max(np.abs(self.F @ self.F - np.eye(M.n))))
        if not semilocal:
            self.FS = self.F
            self.BS = np.eye(M.n)
            self.bs_min = self.bs_max = 1.0
            self.asym = 0.0
        else:
            Eh = np.sqrt(2.0 / N) * sk[:, None] * sk[None, :] \
                * np.cos(np.pi * np.outer(i, i) / (2 * N))
            H = Eh @ self.F
            del Eh
            self.BS = np.eye(M.n) - 0.5 * H
            s = np.linalg.svd(self.BS, compute_uv=False)
            self.bs_min, self.bs_max = float(s.min()), float(s.max())
            del H
            self.FS = self.BS @ np.linalg.solve(self.BS.T, self.F.T).T
            self.asym = float(np.max(np.abs(self.FS - self.FS.T)))
            self.involution_err = float(np.max(np.abs(self.FS @ self.FS - np.eye(M.n))))
        if verbose:
            tag = "S={inf,2}" if semilocal else "S={inf} (archimedean control)"
            print(f"[{tag}]  N={N} delta={M.delta:.6g} U_max={M.U:.3f} dim={M.n}")
            print(f"  ||F_inf^2 - I||_max = {self.inv_err:.3e}   ||F_inf-F_inf^T|| = "
                  f"{np.max(np.abs(self.F-self.F.T)):.3e}")
            if semilocal:
                print(f"  ||F_S^2 - I||_max   = {self.involution_err:.3e}  (exact involution by algebra)")
                print(f"  ||F_S - F_S^T||_max = {self.asym:.3e}  (discretisation; subspace route used)")
                print(f"  sing.val(B_S) in [{self.bs_min:.6f}, {self.bs_max:.6f}]  "
                      f"vs a_S={1-2**-0.5:.6f}, b_S={1+2**-0.5:.6f}")

    def pair(self, lam, tol=1e-6, use_sym=False):
        M = self.M
        FS = 0.5 * (self.FS + self.FS.T) if use_sym else self.FS
        n = M.n
        idxP = np.where(M.u <= lam + 1e-12)[0]
        idxO = np.setdiff1d(np.arange(n), idxP)
        Wr = FS[:, idxP]
        gram_err = float(np.max(np.abs(Wr.T @ Wr - np.eye(len(idxP)))))
        Wt, _ = np.linalg.qr(Wr)
        Y = Wt[idxP, :]
        u_, sv, vt = np.linalg.svd(Y)
        a2 = np.clip(sv ** 2, 0.0, 1.0)
        XIp = u_                                    # columns: eigenvectors of Y Y^T = P Q P
        keep = a2 > tol ** 2
        a2 = a2[keep]
        XI = np.zeros((n, int(keep.sum())))
        XI[idxP, :] = XIp[:, :len(a2)]
        # sign of alpha from <xi, F_S xi>
        sgn = np.sign(np.einsum('ij,ij->j', XI, 0.5 * (FS + FS.T) @ XI))
        al = sgn * np.sqrt(a2)
        s = np.sqrt(np.maximum(1.0 - a2, 1e-300))
        # zeta = (I-P) Q xi / ||(I-P) Q xi||  -- no cancellation, valid also when s -> 0
        QXI = Wt @ (Wt.T @ XI)
        Z = QXI.copy(); Z[pr_idx := idxP, :] = 0.0
        znorm = np.linalg.norm(Z, axis=0)          # = |alpha| s
        ZETA = Z * np.sign(al)[None, :] / np.where(znorm > 0, znorm, 1.0)
        s_from_z = znorm / np.maximum(np.abs(al), 1e-300)
        nrm = np.linalg.norm(ZETA, axis=0)
        chk = dict(gram_err=gram_err, alpha_max=float(np.max(np.abs(al))),
                   s_consistency=float(np.max(np.abs(s_from_z - s))),
                   zeta_norm_err=float(np.max(np.abs(nrm - 1))),
                   xi_zeta_ip=float(np.max(np.abs(XI.T @ ZETA))),
                   P_zeta=float(np.max(np.abs(ZETA[idxP, :]))))
        return dict(lam=lam, idxP=idxP, idxO=idxO, alpha=al, XI=XI, ZETA=ZETA, W=Wt,
                    s=s, checks=chk, ell=2 * np.log(lam))

    def sonin_check(self, pr):
        n = self.M.n
        P = np.zeros((n, n)); P[pr['idxP'], pr['idxP']] = 1.0
        Q = pr['W'] @ pr['W'].T
        al, XI, ZETA, s = pr['alpha'], pr['XI'], pr['ZETA'], pr['s']
        D = (XI * (al ** 2)) @ XI.T + (XI * (al * s)) @ ZETA.T + (ZETA * (al * s)) @ XI.T \
            - (ZETA * (al ** 2)) @ ZETA.T
        S = np.eye(n) - P - Q + D
        return dict(S2_err=float(np.max(np.abs(S @ S - S))),
                    SP=float(np.max(np.abs(S @ P))), SQ=float(np.max(np.abs(S @ Q))),
                    rankS=float(np.trace(S)))


def theta_matrix(M, v):
    n = M.n
    r = np.zeros(n); r[1:] = np.sqrt(M.w[1:] / M.u[1:])
    lu = np.zeros(n); lu[1:] = np.log(M.u[1:]); lu[0] = -1e3
    T = np.zeros((n, n), dtype=complex)
    for a in range(1, n, 1024):
        b = min(n, a + 1024)
        d = lu[a:b, None] - lu[None, :]
        T[a:b, :] = r[a:b, None] * r[None, :] * np.asarray(v(d), dtype=complex)
    T[:, 0] = 0.0
    return T


def quantities(pr, T, norm2):
    idxO = pr['idxO']
    al, XI, ZETA, W, s = pr['alpha'], pr['XI'], pr['ZETA'], pr['W'], pr['s']
    Th = T.conj().T
    Px, Pz = Th @ XI, Th @ ZETA
    a_xi = np.sum(np.abs(Px) ** 2, axis=0)
    a_ze = np.sum(np.abs(Pz) ** 2, axis=0)
    cross = 2 * np.real(np.sum(np.conj(Px) * Pz, axis=0))
    blk = al ** 2 * (a_xi - a_ze) + al * s * cross
    trD = float(np.sum(blk))
    E_S = trD - pr['ell'] * norm2
    G = T[idxO, :]
    tr_out = float(np.sum(np.abs(G) ** 2))
    tr_Q = float(np.sum(np.abs(G.conj().T @ W[idxO, :]) ** 2))
    tr_D = -float(np.sum(al ** 2 * np.sum(np.abs(G.conj().T @ ZETA[idxO, :]) ** 2, axis=0)))
    N_S = tr_out - tr_Q + tr_D
    return dict(N_S=N_S, E_S=E_S, trD=trD, tr_out=tr_out, tr_Q=tr_Q, tr_Dout=tr_D, blocks=blk)
