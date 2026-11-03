from core import *
mp.mp.dps=80;out=[]
for m in [24,80,120]:
 E,labels,heights,metric=rows_for('zeta',m,cutoff(m,'0.25'));s=sigma_min(E);U,b=row_basis(E)
 old=json.loads((P/'benchmark.json').read_text());ref=mp.mpf(next(r['sigma_min'] for r in old if r['m']==m))
 r=dict(m=m,q=E.rows,sigma_min=mp.nstr(s['sigma'],60),iterations=s['iterations'],relative_residual=mp.nstr(s['relative_residual'],15),seconds=s['seconds'],MGS_seconds=b['seconds'],sigma_relative_difference=mp.nstr(abs(s['sigma']-ref)/ref,20),row_orthogonality=mp.nstr(mp.norm(U*U.T-mp.eye(U.rows)),20));out.append(r);print(json.dumps(r),flush=True)
(P/'benchmark_fast.json').write_text(json.dumps(out,indent=2)+'\n')
