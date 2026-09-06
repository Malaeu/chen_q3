import numpy as np, time, sys, json
from numpy.polynomial.legendre import leggauss
from s1_model import Carrier
from semilocal import build as sl_build
from core import Test, D_minus_cA, prime_sum, primes_upto, Angles, C_A
import tests_family as TF

TOL = 1e-10

# ---------------- carrier operators ----------------
_cache = {}
def ops(N):
    if N in _cache: return _cache[N]
    C, F, Dil = sl_build(N)
    n = N+1
    Jinv = np.eye(n)-Dil
    J = np.linalg.inv(Jinv)
    FSsrc = J@F@Jinv
    G = J.T@J; w, U = np.linalg.eigh(G)
    V = J@((U*(w**-0.5))@U.T)
    FSpol = V@F@V.T
    diag = dict(asym_src=float(np.abs(FSsrc-FSsrc.T).max()),
                dist_src_pol=float(np.linalg.norm(FSsrc-FSpol, 2)),
                sym_pol=float(np.abs(FSpol-FSpol.T).max()),
                inv_pol=float(np.abs(FSpol@FSpol-np.eye(n)).max()),
                inv_src=float(np.abs(FSsrc@FSsrc-np.eye(n)).max()),
                Bs_min=float(np.linalg.svd(Jinv, compute_uv=False)[-1]),
                Bs_max=float(np.linalg.svd(Jinv, compute_uv=False)[0]),
                xrange=(float(np.log(C.delta)), float(np.log(C.T))))
    _cache[N] = (C, {'arch': F, 'src': FSsrc, 'pol': FSpol}, diag)
    return _cache[N]

_geo = {}
def geom(N, lam, key):
    k = (N, lam, key)
    if k in _geo: return _geo[k]
    C, Fs, _ = ops(N); Fop = Fs[key]; n = C.N+1
    m = int(round(lam/C.delta))+1
    Cq = Fop[:, :m]
    Uq, sq_, _ = np.linalg.svd(Cq, full_matrices=False); Uq = Uq[:, sq_ > TOL]
    Z = np.zeros((n, m+Uq.shape[1])); Z[np.arange(m), np.arange(m)] = 1.0; Z[:, m:] = Uq
    Up, sp_, _ = np.linalg.svd(Z, full_matrices=False); Up = Up[:, sp_ > 1e-8]
    blk = 0.5*(Fop[:m, :m]+Fop[:m, :m].T)
    al = np.linalg.eigvalsh(blk); al = al[np.argsort(-np.abs(al))]
    _geo[k] = dict(m=m, Uq=Uq, Up=Up, alpha=al, nker=n-Up.shape[1], rankPi=Up.shape[1],
                   nblk=int(np.sum(np.abs(al) > 1e-6)))
    return _geo[k]

def build_A(C, T):
    N = C.N; t = C.t
    lg = np.log(np.where(t > 0, t, 1.0)); Ls = 2*T.half
    A = np.zeros((N+1, N+1))
    for j in range(1, N+1):
        k0 = max(1, int(np.ceil(t[j]*np.exp(-Ls)/C.delta)))
        k1 = min(N, int(np.floor(t[j]*np.exp(Ls)/C.delta)))
        if k1 < k0: continue
        kk = np.arange(k0, k1+1)
        A[j, kk] = C.delta*np.sqrt(C.c[j]*C.c[kk])*np.real(T.f(lg[j]-lg[kk]))/np.sqrt(t[j]*t[kk])
    return 0.5*(A+A.T)

def carrier_EN(N, lam, key, T, A=None):
    C, _, _ = ops(N); g = geom(N, lam, key)
    if A is None: A = build_A(C, T)
    m = g['m']; ell = 2*np.log(lam)
    trA = float(np.trace(A)); trAP = float(np.trace(A[:m, :m]))
    trAQ = float(np.sum(g['Uq']*(A@g['Uq'])))
    trAPi = float(np.sum(g['Up']*(A@g['Up'])))
    N_S = trA-trAPi
    E_S = trAP+trAQ-trAPi-ell*T.nrm2
    return dict(N_S=N_S, E_S=E_S, LS_model=N_S-E_S, trA=trA, trAP=trAP, trAQ=trAQ, trAPi=trAPi)

# ------------- independent (spectral) E_S, archimedean only -------------
class PanelInterp:
    def __init__(self, ang, npan, nq, lam):
        self.e = np.linspace(0, lam, npan+1); self.nq = nq; self.t = ang.t
    def __call__(self, vals, x):
        x = np.atleast_1d(x); out = np.zeros_like(x)
        for i, xi in enumerate(x):
            p = min(max(int(xi/(self.e[1]-self.e[0])), 0), len(self.e)-2)
            sl = slice(p*self.nq, (p+1)*self.nq)
            tt = self.t[sl]; vv = vals[sl]
            wgt = np.ones(self.nq)
            for k in range(self.nq):
                wgt[k] = 1.0/np.prod(tt[k]-np.delete(tt, k))
            d = xi-tt
            if np.any(np.abs(d) < 1e-14):
                out[i] = vv[np.argmin(np.abs(d))]
            else:
                num = np.sum(wgt/d*vv); den = np.sum(wgt/d); out[i] = num/den
        return out

def E_spec(lam, T, npan=8, nq=60, nmax=None):
    ang = Angles(lam, npan=npan, nq=nq)
    itp = PanelInterp(ang, npan, nq, lam)
    h = 2*T.half; ll = np.log(lam)
    gx, gw = leggauss(300)
    X = ll-h/2+(h/2)*gx; WX = (h/2)*gw
    Y = ll+h/2+(h/2)*gx; WY = (h/2)*gw
    K = np.real(T.f(X[:, None]-Y[None, :]))
    tot = 0.0; terms = []
    nm = nmax or len(ang.alpha)
    for n in range(nm):
        a = ang.alpha[n]
        if abs(a) < 1e-13 or abs(a) >= 1: continue
        s = np.sqrt(1-a*a)
        xi_t = itp(ang.xi(n), np.exp(X))
        xit = np.exp(X/2)*xi_t
        zet = np.exp(Y/2)*ang.Fxi(n, np.exp(Y))/s
        cross = (WX*xit)@K@(WY*zet)
        tot += (a/s)*2*cross
        terms.append((a, (a/s)*2*cross))
        if abs(a) < 1e-11: break
    return tot-2*np.log(lam)*T.nrm2, terms
