from pathlib import Path
import csv,json,sys,time
import mpmath as mp
P=Path(__file__).resolve().parent;BUS=P.parents[1]
sys.path.insert(0,str(BUS/'capacity_matrix_2026-11-02'))
from capacity import Erow
mp.mp.dps=80
z=[mp.mpf(x['gamma']) for x in csv.DictReader((BUS/'capacity_matrix_2026-11-02/zeros.csv').open())]
rows=[]
for m in [24,80,120]:
 L=mp.log(m);k=1+mp.mpf(1)/4*(1+mp.log(L))/L;T=k*2*mp.pi*m/L;g=[x for x in z if x<T];t=time.monotonic();E=mp.matrix([Erow(x,m) for x in g]);prep=time.monotonic()-t;t=time.monotonic();u,s,v=mp.svd_r(E,full_matrices=True);elapsed=time.monotonic()-t
 row=dict(m=m,q=len(g),d=m+1,prepare_seconds=prep,svd_seconds=elapsed,sigma_min=mp.nstr(s[len(s)-1],60),SVD_residual=mp.nstr(mp.norm(E-u*mp.diag(s)*v[:len(g),:]),20));rows.append(row);print(json.dumps(row),flush=True)
(P/'benchmark.json').write_text(json.dumps(rows,indent=2)+'\n')
