"""Preregistered source modifications; finite diagnostics only."""
from pathlib import Path
import sys, csv, json, argparse, time
import mpmath as mp
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parents[1]/'suzuki_W_2026-11-02'/'prediction'))
from scan import g_function

def run(world,mesh,dps=100,end=6):
    mp.mp.dps=dps; start=time.monotonic(); h=mp.mpf(1)/mesh
    base,atoms=g_function('zeta',end); N=int(end*mesh)
    def g(t):
        exact=mp.fsum(c*(t-a) for a,c,n in atoms if a<t)
        if world=='true_zeta':return base(t)
        if world=='half_atoms':return base(t)-exact/2
        if world=='three_halves_atoms':return base(t)+exact/2
        a=mp.log(2)
        smooth=4*mp.exp(t/2)-(2*t+4-2*a)*mp.exp(a/2) if t>a else mp.mpf(0)
        return base(t)-exact+smooth
    gs=[g(k*h) for k in range(N+1)]
    r=[-2*gs[1]]+[2*gs[k]-gs[k-1]-gs[k+1] for k in range(1,N)]
    v=r[0]; coeff=[]; rows=[]; negative=0; first=None; witness=None
    for n in range(1,N+1):
        if n>1:
            p=n-1
            reflection=(r[p]-mp.fsum(coeff[j-1]*r[p-j] for j in range(1,p)))/v
            coeff=[coeff[j-1]-reflection*coeff[p-j-1] for j in range(1,p)]+[reflection]
            v*=1-reflection**2
        else:reflection=mp.mpf(0)
        if abs(v)<mp.mpf(10)**(-dps+20):raise ArithmeticError('unresolved nonstructural pivot')
        negative+=int(v<0)
        if v<0 and first is None:
            first=n; w=[-x for x in reversed(coeff)]+[mp.mpf(1)]
            direct=r[0]*mp.fsum(x*x for x in w)+2*mp.fsum(r[k]*mp.fsum(w[i]*w[i+k] for i in range(n-k)) for k in range(1,n))
            witness=dict(n=n,t=str(n*h),innovation=mp.nstr(v,dps),direct=mp.nstr(direct,dps),relative_error=mp.nstr(abs(direct-v)/abs(v),20),normalized_rayleigh=mp.nstr(direct/mp.fsum(x*x for x in w),50),coefficients=[mp.nstr(x,dps) for x in w])
        rows.append(dict(world=world,mesh=mesh,dps=dps,n=n,t=str(n*h),sigma2=mp.nstr(v,dps),negative_pivots=negative,reflection=mp.nstr(reflection,35)))
    out=ROOT/'controls';out.mkdir(exist_ok=True);tag=f'{world}_mesh{mesh}_dps{dps}'
    with (out/(tag+'.csv')).open('w') as f:
        writer=csv.DictWriter(f,fieldnames=rows[0]);writer.writeheader();writer.writerows(rows)
    result=dict(world=world,mesh=mesh,dps=dps,first_negative_n=first,first_negative_t=str(first*h) if first else None,last_sigma2=rows[-1]['sigma2'],negative_pivots=negative,witness=witness,seconds=time.monotonic()-start)
    (out/(tag+'.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='witness'}),flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--dps',type=int,default=100);p.add_argument('--mesh',type=int,nargs='+',default=[32,64]);a=p.parse_args()
    for mesh in a.mesh:
        for world in ['true_zeta','half_atoms','three_halves_atoms','smooth_atoms']:run(world,mesh,a.dps)
