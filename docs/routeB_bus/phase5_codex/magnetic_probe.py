import sys, mpmath as mp
from pathlib import Path
sys.path.insert(0,'docs/routeB_bus/phase5_scripts')
from flint import arb, arb_mat, ctx
from edge_ledger_build import CCMArbBuilder
ctx.dps=80; mp.mp.dps=60
for m in (13,23,43):
    b=CCMArbBuilder(m,m); K=b.even_block(); n=K.nrows()
    Km=mp.matrix(n,n)
    for i in range(n):
        for j in range(n): Km[i,j]=mp.mpf(K[i,j].mid().str(50,radius=False))
    E,V=mp.eigsy(Km); lam1=min(E); k=[i for i in range(n) if E[i]==lam1][0]; v=[V[i,k] for i in range(n)]
    absoff=[[abs(Km[i,j]) if i!=j else mp.mpf(0) for j in range(n)] for i in range(n)]
    Vpot=[Km[i,i]-sum(absoff[i]) for i in range(n)]
    mag=sum(absoff[i][j]*abs(v[i]-(-Km[i,j]/absoff[i][j])*v[j])**2 for i in range(n) for j in range(i+1,n) if absoff[i][j]>0)
    Pp=sum(Vpot[i]*abs(v[i])**2 for i in range(n) if Vpot[i]>0); Pm=sum(-Vpot[i]*abs(v[i])**2 for i in range(n) if Vpot[i]<0)
    neg=sum(1 for x in Vpot if x<0)
    print(f"m={m} dim={n}: lambda1={mp.nstr(lam1,6)}  on ground v: magnetic={mp.nstr(mag,8)}  V+ part={mp.nstr(Pp,8)}  V- part={mp.nstr(Pm,8)}  identity residual={mp.nstr(mag+Pp-Pm-lam1,3)}")
    print(f"   #negative potentials {neg}/{n}; V_i range [{mp.nstr(min(Vpot),5)}, {mp.nstr(max(Vpot),5)}]; K_ii range [{mp.nstr(min(Km[i,i] for i in range(n)),5)}, {mp.nstr(max(Km[i,i] for i in range(n)),5)}]; phases tau_ij: all real (K real) -> tau = -sign(K_ij): #negative off-diag entries = {sum(1 for i in range(n) for j in range(i+1,n) if Km[i,j]<0)} of {n*(n-1)//2}")
    print(f"   ratio magnetic/V- on ground = {mp.nstr(mag/Pm,6)}   (1 means the vortex exactly pays the debt at the ground)", flush=True)
