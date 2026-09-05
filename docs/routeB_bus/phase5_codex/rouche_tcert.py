"""Probe 27 (2026-09-06): Rouche boundary ratio Q(D)=sup_{dD}|Xi/Xi(0)-F/F(0)|/|F/F(0)| for the CCM ground-vector transform F on
rectangles [0,T]x[0.01,0.05]; reports T_cert(m) = first T with Q>=1. Usage: .venv/bin/python rouche_tcert.py m N dps iters Tmin Tmax
(m=13: 120 150 120 20 200; m=23: 160 240 160 200 440; m=43: 344 850 8 400 640 -- dps ~ 2N+160 as in q3-sat43).
Coefficients pass arb->mpf via decimal string (never float). DIAGNOSTIC_NEVER_A_PROOF. Results: Progress_Log 2026-09-06."""
import sys, math
sys.path.insert(0,'docs/routeB_bus/phase5_scripts')
from flint import arb, ctx
import mpmath as mp
from edge_ledger_build import CCMArbBuilder, inverse_iteration_ground
mp.mp.dps=260
def xi(s): return (s-1)*mp.pi**(-s/2)*mp.gamma(s/2+1)*mp.zeta(s)
Xi0=xi(mp.mpf(1)/2)
def Xi(z): return xi(mp.mpf(1)/2+1j*z)
def ground(m,N,dps,iters):
    ctx.dps=dps; B=CCMArbBuilder(m,N); K=B.even_block()
    lam,v,res=inverse_iteration_ground(K,N+1,iters)
    return mp.mpf(lam.mid().str(30,radius=False)), [mp.mpf(x.mid().str(250, radius=False)) for x in v]
def F_from_even(v,L):
    c0=v[0]; c=[x/mp.sqrt(2) for x in v[1:]]
    def F(z):
        z=mp.mpmathify(z); tot=c0/z
        for n,cn in enumerate(c,start=1):
            a=2*mp.pi*n/L; tot+= cn*(1/(z-a)+1/(z+a))
        return 2*mp.sin(z*L/2)*tot
    return F
def Q_rect(F,F0,T,h1,h2,nb):
    pts=[mp.mpc(T*k/nb,h) for k in range(nb+1) for h in (h1,h2)]+[mp.mpc(x,h1+(h2-h1)*k/nb) for k in range(nb+1) for x in (0,T)]
    best=(0,None)
    for z in pts:
        Fz=F(z)/F0; q=abs(Xi(z)/Xi0-Fz)/abs(Fz)
        if q>best[0]: best=(q,z)
    return best
import sys as _s
m,N,dps,iters,Tmin,Tmax=[int(a) for a in _s.argv[1:7]]
for (m,N,dps,iters) in [(m,N,dps,iters)]:
    L=mp.log(m); lam,v=ground(m,N,dps,iters); F=F_from_even(v,L); F0=L*v[0]
    print("cell (%d,%d) iters=%d lambda1=%s"%(m,N,iters,mp.nstr(lam,6))); sys.stdout.flush()
    import json; json.dump({"m":m,"N":N,"dps":dps,"lambda1":mp.nstr(lam,40),"v_even":[mp.nstr(x,250) for x in v]}, open("docs/routeB_bus/phase5_codex/out/ground_%d_%d.json"%(m,N),"w"))
    for T in list(range(Tmin,Tmax+1,20)):
        nb=max(80,2*T)
        q,z=Q_rect(F,F0,T,mp.mpf('0.01'),mp.mpf('0.05'),nb)
        print("   near-axis band [0.01,0.05]  T=%3d  Q=%s at z=%s"%(T,mp.nstr(q,8),mp.nstr(z,6))); sys.stdout.flush()
        if q>=1: print("   T_cert(%d) in [%d,%d)"%(m,T-20,T)); break
