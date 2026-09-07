# DIAGNOSTIC_NEVER_A_PROOF: sign of the scalar floor F(h_T) on the high-modulation family h_T = (d^2-1/4)(e^{iTx} eta_4)
import sys, numpy as np, mpmath as mp
sys.path.insert(0,'/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/mellin_d2')
import dens
from multiprocessing import Pool
a=np.log(2.0); d=(np.log(3)-np.log(2))/8
def ell2(xi):
    xi=float(xi); g=complex(dens.gamma_S(xi,primes=(2,))); t=complex(dens.t_S(xi,primes=(2,)))
    return 2*(g*t).real
# eta_4 hat (nonunitary, real even): 2 delta int_0^1 (1-z^2)^4 cos(delta xi z) dz  -> numeric
zs,ws=np.polynomial.legendre.leggauss(60); zs=(zs+1)/2; ws=ws/2
def etahat(xi): return 2*d*np.sum(ws*(1-zs**2)**4*np.cos(d*xi*zs))
def hThat(xi,T): return -(xi**2+0.25)*etahat(xi-T)
if __name__=='__main__':
    Ts=[float(x) for x in sys.argv[1:]] or [30,60,120,240]
    # grid: around +T and -T within +-R (etahat ~ xi^-5 beyond), plus coarse elsewhere
    R=250.0; pts=set()
    for T in Ts:
        for s in (+1,-1): pts.update(np.round(np.arange(s*T-R,s*T+R,0.25),4).tolist())
    pts=sorted(p for p in pts if p>=0)  # even integrand: use xi>=0 and double
    with Pool(22) as P: L=np.array(P.map(ell2,pts,chunksize=16))
    Ld=dict(zip(pts,L))
    print(f"grid {len(pts)} pts; ell2 range [{L.min():.4f},{L.max():.4f}]")
    for T in Ts:
        xs=np.array([p for p in pts if abs(p-T)<=R]); l=np.array([Ld[p] for p in xs])
        H=None
        # W = (1-cos a xi)|hhat|^2 / H ; H from Parseval over the full line: int |hhat|^2 dxi / 2pi with hhat two-sided
        allx=np.arange(-T-R,T+R,0.25); hh=np.array([hThat(x,T) for x in allx]); H=np.sum(hh**2)*0.25/(2*np.pi)
        hp=np.array([hThat(x,T) for x in xs]); hm=np.array([hThat(-x,T) for x in xs])   # contributions at +xi and -xi (ell2 even)
        W=(1+np.cos(a*xs))*(hp**2+hm**2)/H
        F=-np.sum(W*l)*0.25; mass=np.sum(W)*0.25
        # also the plain margin proxy: which sign dominates near +T
        print(f"T={T:6.1f}: Qsc_plus(v+,T) = {F:+.6e}   W-mass covered {mass/(2*np.pi):.4f} of 2pi   ell2(T)={Ld.get(round(T,4),float('nan')):+.5f}  mean ell2 on band={l.mean():+.5f}")
