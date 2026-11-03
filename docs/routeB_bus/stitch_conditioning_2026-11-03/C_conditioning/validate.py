"""Selected raw MP120 full-SVD replay, independent of inverse iteration."""
from core import *
mp.mp.dps=120
out=json.loads((P/'validation_120.json').read_text()) if (P/'validation_120.json').exists() else []
for world,m,c in [('dh',24,'.25'),('zeta',80,'.25'),('zeta',120,'.25')]:
 if any(x['world']==world and x['m']==m for x in out):continue
 t=time.monotonic();E,_,_,_=rows_for(world,m,cutoff(m,c));U,s,V=mp.svd(E);sm=s[len(s)-1];left=U[:,len(s)-1];right=V[len(s)-1,:].T
 ref=json.loads((P/'cells'/f'{world}_m{m}.json').read_text());row=next(r for r in ref['rows'] if r['cut']=='c_quarter' and r['variant']=='base');rel=abs(sm/mp.mpf(row['sigma_min'])-1)
 out.append(dict(world=world,m=m,c=c,dps=120,method='FULL_MP_SVD',sigma=mp.nstr(sm,100),relative_to_MP80=mp.nstr(rel,20),relative_forward_residual=mp.nstr(mp.norm(E*right-sm*left)/sm,20),relative_adjoint_residual=mp.nstr(mp.norm(E.T*left-sm*right)/sm,20),seconds=time.monotonic()-t))
 (P/'validation_120.json').write_text(json.dumps(out,indent=2)+'\n');print(world,m,'validation',out[-1],flush=True)
