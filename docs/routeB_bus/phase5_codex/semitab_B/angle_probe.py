import numpy as np, sys
sys.path.insert(0,'.')
from ops import SemiLocal
for N in (512,1024,2048,4096):
    for tag,sem in (('arch',False),('semi',True)):
        sl=SemiLocal(N,semilocal=sem,verbose=False)
        pr=sl.pair(1.0,tol=1e-10); a=np.abs(pr['alpha']); a=np.sort(a)[::-1]
        cnt={t:int((a>t).sum()) for t in (1e-2,1e-3,1e-6,1e-8)}
        tail=[float(a[k]) if k<len(a) else float('nan') for k in (5,10,20,30,40,60)]
        print(f"N={N:5d} {tag} Umax={np.sqrt(N/2):.1f} dimP={pr.get('m', 'na')} counts>1e-2,1e-3,1e-6,1e-8: {cnt[1e-2]},{cnt[1e-3]},{cnt[1e-6]},{cnt[1e-8]}  |alpha| at n=5,10,20,30,40,60: "+" ".join(f"{x:.4f}" for x in tail), flush=True)
        del sl
