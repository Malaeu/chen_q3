"""Euler-Gram evaluator of the semilocal Sonin density k_2 (SCALARFLOOR Thm 3, (18)-(22)).

In Mellin (Fourier) coordinates the archimedean Sonin space H_0 becomes a reproducing
kernel space  H = F H_0  subset L^2(R,dxi)  with kernel K(xi,eta) = <w_eta,w_xi>
(module fastk); U_a acts as multiplication by e^{-i a xi}, so B = I - r U_a acts as
multiplication by b(xi) = 1 - r e^{-i a xi} and

      G = P_H M_{|b|^2} P_H ,     g0 = (1-r)^2 <= G <= (1+r)^2 = g1 ,
      k_2(xi0) = |b(xi0)|^2 <w_xi0, G^{-1} w_xi0>.

Trial space: span{E_j}, E_j(xi) = K(xi_j,xi) (reproducing kernels at nodes xi_j).
  Gamma_{jl} = <E_j,E_l> = K(xi_l,xi_j)                        EXACT (projector identity)
  X_{jl}     = int 2cos(a xi) conj(E_j) E_l dxi                quadrature
  Y_{jl}     = int 4cos^2(a xi) conj(E_j) E_l dxi              quadrature
  G = (1+r^2) Gamma - r X
For xi0:  p_j = K(xi0,xi_j),  E(y) = p^H G^{-1} p  (LOWER bound, monotone in the span)
  c = G^{-1}p, y = sum c_j E_j, psi = 2cos(a xi) y,
  |y|^2 = c^H Gamma c, <y,psi> = c^H X c, |psi|^2 = c^H Y c, q = X c,
  |P psi|^2 in [ q^H Gamma^{-1} q , |psi|^2 ],
  <w,Gy> = (1+r^2) p^H c - r (X_ext c)_{xi0},
  |Gy|^2 = (1+r^2)^2 |y|^2 - 2(1+r^2) r Re<y,psi> + r^2 |P psi|^2,
  |z|^2  = k_inf(xi0) - 2 Re<w,Gy> + |Gy|^2,
  k_2 <= |b|^2 ( E + |z|^2_max / g0 ).
"""
import numpy as np
import fastk

A_LOG2 = np.log(2.0)
R2 = 2.0**-0.5
G0 = (1-R2)**2
G1 = (1+R2)**2

def babs2(xi, a=A_LOG2, r=R2):
    return 1.0 + r*r - 2*r*np.cos(a*np.asarray(xi, float))

def q_two(xi, jmax=400, a=A_LOG2, r=R2):
    from scipy.special import digamma
    xi = np.asarray(xi, float)
    q = np.real(digamma(0.25+0.5j*xi)) - np.log(np.pi)
    j = np.arange(1, jmax+1)
    q -= 2*a*np.sum((r**j)[:, None]*np.cos(np.outer(j, a*xi)), axis=0)
    return q

def make_nodes(lo, hi, over=1.5, kmin=0.02):
    """nodes with local spacing 1/(over*k_inf) (Nyquist of the de Branges space)."""
    fk = fastk.FastKern(M=100, nmode=10)
    xs = [lo]; x = lo
    while x < hi:
        kk = max(float(fk.diag(fk.data(np.array([x])))[0]), kmin)
        x = x + 1.0/(over*kk)
        xs.append(x)
    return np.array(xs)

def uniform_grid(U, h):
    n = int(round(2*U/h))
    return (np.arange(n)+0.5)*h - U, np.full(n, h)

class EulerGram:
    def __init__(self, nodes, U=1200.0, h=0.05, fk=None, blk=4000, verbose=False,
                 a=A_LOG2, r=R2):
        self.fk = fk or fastk.FastKern(M=100, nmode=10)
        self.nodes = np.asarray(nodes, float)
        self.a, self.r = a, r
        n = self.nodes.size
        Dn = self.fk.data(self.nodes)
        self.Dn = Dn
        KB = self.fk.block(Dn, Dn)                      # KB[i,j] = K(xi_i,xi_j)
        self.Gamma = KB.T.copy()                        # Gamma_{jl} = K(xi_l,xi_j)
        self.Gamma = 0.5*(self.Gamma + self.Gamma.conj().T)
        self.X = np.zeros((n, n), complex)
        self.X2 = np.zeros((n, n), complex)
        self.Gq = np.zeros((n, n), complex)             # quadrature Gram (diagnostic)
        g, w = uniform_grid(U, h)
        self.U, self.h = U, h
        for s in range(0, g.size, blk):
            e = min(s+blk, g.size)
            Dg = self.fk.data(g[s:e])
            Eb = self.fk.block(Dn, Dg).T                # (nb, n): E_j(xi_g)
            cs = np.cos(a*g[s:e])
            self.Gq += Eb.conj().T @ (w[s:e][:, None]*Eb)
            self.X += Eb.conj().T @ ((w[s:e]*2*cs)[:, None]*Eb)
            self.X2 += Eb.conj().T @ ((w[s:e]*2*np.cos(2*a*g[s:e]))[:, None]*Eb)
            if verbose and (s//blk) % 5 == 0:
                print(f"   grid {e}/{g.size}", flush=True)
        for Mx in (self.X, self.X2, self.Gq):
            Mx[:] = 0.5*(Mx + Mx.conj().T)
        self.Y = 2*self.Gamma + self.X2          # |psi|^2 kernel, exact non-oscillatory part
        self.G = (1+r*r)*self.Gamma - r*self.X
        self._orth()

    def _orth(self, tol=1e-9):
        lam, V = np.linalg.eigh(self.Gamma)
        keep = lam > tol*lam.max()
        self.B = V[:, keep]/np.sqrt(lam[keep])          # Gamma-orthonormalising map
        self.rank = int(keep.sum())
        self.Gt = self.B.conj().T @ self.G @ self.B
        self.Gt = 0.5*(self.Gt + self.Gt.conj().T)
        self.gev = np.linalg.eigvalsh(self.Gt)
        self.Gti = np.linalg.inv(self.Gt)
        self.Yt = self.B.conj().T @ self.Y @ self.B
        self.Xt = self.B.conj().T @ self.X @ self.B

    def gram_error(self):
        return float(np.abs(self.Gq - self.Gamma).max())

    def eval(self, xi0, blk=4000, full=True, U=None, h=None):
        """k_2 lower/upper at the points xi0."""
        xi0 = np.atleast_1d(np.asarray(xi0, float))
        D0 = self.fk.data(xi0)
        P = self.fk.block(D0, self.Dn)                  # [m,j] = K(xi0_m, xi_j) = p_j
        pt = self.B.conj().T @ P.T                      # (rank, m)   p~
        ct = self.Gti @ pt                              # (rank, m)   c~ = Gt^{-1} p~
        E = np.real(np.einsum('im,im->m', pt.conj(), ct))
        kinf = self.fk.diag(D0)
        comp = np.real(np.einsum('im,im->m', pt.conj(), pt))    # |P_S w|^2
        out = dict(xi=xi0, kinf=kinf, E=E, comp=comp, b2=babs2(xi0, self.a, self.r))
        out['k2_lo'] = out['b2']*E
        if not full:
            return out
        # residual sandwich
        ny2 = np.real(np.einsum('im,im->m', ct.conj(), ct))          # |y|^2
        Xc = self.Xt @ ct                                            # q~ = X~ c~
        ypsi = np.real(np.einsum('im,im->m', ct.conj(), Xc))
        npsi2 = np.real(np.einsum('im,im->m', ct.conj(), self.Yt @ ct))
        Ppsi_lo = np.real(np.einsum('im,im->m', Xc.conj(), Xc))      # |P_S psi|^2
        Xe = self._Xext(xi0, blk, U, h)                              # (m,n)
        Xet = (Xe @ self.B).T                                        # (rank, m)
        wpsi = np.einsum('im,im->m', Xet, ct)                        # <w,psi> = sum_j c_j X_{0j}
        wy = E.astype(complex)                                       # y(xi0) = E (real at optimum)
        r = self.r; s1 = 1+r*r
        wGy = s1*wy - r*wpsi
        Ppsi_hi = np.maximum(npsi2, Ppsi_lo)
        Gy2_hi = s1*s1*ny2 - 2*s1*r*ypsi + r*r*Ppsi_hi
        z2 = np.maximum(kinf - 2*np.real(wGy) + Gy2_hi, 0.0)
        out.update(z2=z2, Ppsi_lo=Ppsi_lo, Ppsi_hi=Ppsi_hi, ny2=ny2)
        out['k2_hi'] = out['b2']*(E + z2/G0)
        return out

    def _Xext(self, xi0, blk=4000, U=None, h=None):
        U = U or self.U; h = h or self.h
        g, w = uniform_grid(U, h)
        n = self.nodes.size
        Xe = np.zeros((xi0.size, n), complex)
        for s in range(0, g.size, blk):
            e = min(s+blk, g.size)
            Dg = self.fk.data(g[s:e])
            E0 = self.fk.block(self.fk.data(xi0), Dg).T          # (nb, m)
            Ej = self.fk.block(self.Dn, Dg).T                    # (nb, n)
            cs = np.cos(self.a*g[s:e])
            Xe += E0.conj().T @ ((w[s:e]*2*cs)[:, None]*Ej)
        return Xe
