"""Independent integral/source checks, precision replay and negative witness."""
from pathlib import Path
import json,csv
import mpmath as mp
from innovation import coefficients,source_g

root=Path(__file__).resolve().parent
mp.mp.dps=100
checks=[]
for world in ['zeta','dh']:
    b=coefficients(240,world)
    weights=[(mp.log(n),b[n]/mp.sqrt(n)) for n in range(2,241)]
    alpha=mp.mpf('.5') if world=='zeta' else mp.mpf('1.5')
    c=-mp.euler-mp.log(8*mp.pi)-mp.pi/2 if world=='zeta' else -mp.euler-mp.log(8*mp.pi/5)+mp.pi/2
    for t in [mp.mpf(1)/128,mp.log(20),mp.log(55),mp.log(120),mp.log(240)]:
        def integrand(s):
            return mp.mpf('.5') if not s else s*mp.exp(-alpha*s)/(-mp.expm1(-2*s))
        arch=2*mp.quad(integrand,[0,t])+2*t*mp.quad(lambda s:mp.exp(-alpha*s)/(-mp.expm1(-2*s)),[t,mp.inf])
        arith=-2*mp.fsum(w*(t-ln) for ln,w in weights if ln<t)
        pole=32*mp.sinh(t/4)**2 if world=='zeta' else 0
        independent=-(c*t+arch+arith+pole)/2
        checks.append(dict(world=world,length=mp.nstr(t,40),absolute_difference=mp.nstr(abs(independent-source_g(t,world,weights)),60)))

precision=[];witness=[]
for world in ['zeta','dh']:
    for mesh in [64,128]:
        low=list(csv.DictReader((root/f'{world}_mesh{mesh}_dps100.csv').open()))
        high=list(csv.DictReader((root/f'{world}_mesh{mesh}_dps160.csv').open()))
        change=max(abs(mp.mpf(a['innovation'])-mp.mpf(b['innovation']))/max(abs(mp.mpf(b['innovation'])),mp.mpf('1e-90')) for a,b in zip(low,high))
        signmatch=all(a['positive']==b['positive'] for a,b in zip(low,high))
        precision.append(dict(world=world,mesh=mesh,rows=len(low),maximum_relative_change=mp.nstr(change,60),all_signs_match=signmatch))
        if world!='dh':continue
        a=[];n=None
        for row in high[1:]:
            reflection=mp.mpf(row['reflection']);p=len(a)+1
            a=[a[j-1]-reflection*a[p-j-1] for j in range(1,p)]+[reflection]
            if row['positive']=='False':n=int(row['increments']);break
        if n is None:continue
        w=[-x for x in reversed(a)]+[mp.mpf(1)]
        b=coefficients(240,world);weights=[(mp.log(k),b[k]/mp.sqrt(k)) for k in range(2,241)]
        g=[source_g(mp.mpf(k)/mesh,world,weights) for k in range(n+1)]
        r=[-2*g[1]]+[2*g[k]-g[k-1]-g[k+1] for k in range(1,n)]
        direct=r[0]*mp.fsum(x*x for x in w)+2*mp.fsum(r[k]*mp.fsum(w[i]*w[i+k] for i in range(n-k)) for k in range(1,n))
        norm=mp.fsum(x*x for x in w)
        record=dict(mesh=mesh,increments=n,length=mp.nstr(mp.mpf(n)/mesh,35),direct_quadratic=mp.nstr(direct,70),normalized_rayleigh=mp.nstr(direct/norm,70),recursion_innovation=row['innovation'],relative_witness_replay_error=mp.nstr(abs(direct-mp.mpf(row['innovation']))/abs(direct),60),negative=direct<0,coefficients=[mp.nstr(x,60) for x in w])
        (root/f'dh_mesh{mesh}_negative_witness.json').write_text(json.dumps(record,indent=2)+'\n')
        witness.append({k:v for k,v in record.items() if k!='coefficients'})
result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',integral_source_checks=checks,precision_checks=precision,negative_witness_checks=witness)
assert max(mp.mpf(x['absolute_difference']) for x in checks)<mp.mpf('1e-90')
assert all(x['all_signs_match'] for x in precision)
assert all(x['negative'] for x in witness)
(root/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
