"""Nested screw-increment geometry. Finite floating diagnostic, never a proof."""
from pathlib import Path
import argparse,csv,json,time
import mpmath as mp

def coefficients(M,world):
    if world=='zeta':
        b=[mp.mpf(0)]*(M+1)
        for n in range(2,M+1):
            for p in range(2,n+1):
                if n%p==0:
                    k=n
                    while k%p==0:k//=p
                    b[n]=mp.log(p) if k==1 else mp.mpf(0)
                    break
        return b
    tau=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
    a=[mp.mpf(0),mp.mpf(1),tau,-tau,-mp.mpf(1)]
    b=[mp.mpf(0)]*(M+1)
    for n in range(2,M+1):
        b[n]=a[n%5]*mp.log(n)-mp.fsum(b[d]*a[(n//d)%5] for d in range(2,n) if n%d==0)
    return b

def source_g(t,world,weights):
    if not t:return mp.mpf(0)
    alpha=mp.mpf('.5') if world=='zeta' else mp.mpf('1.5')
    c=-mp.euler-mp.log(8*mp.pi)-mp.pi/2 if world=='zeta' else -mp.euler-mp.log(8*mp.pi/5)+mp.pi/2
    x=mp.exp(-t/2)
    odd=mp.polylog(2,x)-mp.polylog(2,-x)
    tail=odd+(2 if world=='zeta' else -2)*mp.im(mp.polylog(2,1j*x))
    S=mp.polygamma(1,alpha/2)/4-tail
    arithmetic=mp.fsum(w*(t-logn) for logn,w in weights if logn<t)
    pole=32*mp.sinh(t/4)**2 if world=='zeta' else mp.mpf(0)
    return -(c*t+2*S-2*arithmetic+pole)/2

def run(mesh,world,dps,out):
    mp.mp.dps=dps;start=time.monotonic();b=coefficients(240,world)
    weights=[(mp.log(n),b[n]/mp.sqrt(n)) for n in range(2,241)]
    N=int(mp.floor(mesh*mp.log(240)))
    g=[source_g(mp.mpf(k)/mesh,world,weights) for k in range(N+1)]
    r=[-2*g[1]]+[2*g[k]-g[k-1]-g[k+1] for k in range(1,N)]
    v=r[0];a=[];rows=[];first=None;positive=True;monotone=True;prev=v
    def record(size,reflection):
        nonlocal first,positive,monotone,prev
        if v<=0 and first is None:first=size
        positive=positive and v>0
        if v>prev+mp.mpf(10)**(-dps//2)*max(1,abs(prev)):monotone=False
        rows.append(dict(world=world,mesh=mesh,dps=dps,increments=size,length=mp.nstr(mp.mpf(size)/mesh,35),m_equivalent=mp.nstr(mp.exp(mp.mpf(size)/mesh),35),innovation=mp.nstr(v,70),reflection=mp.nstr(reflection,50),positive=v>0))
        prev=v
    record(1,mp.mpf(0))
    for p in range(1,N):
        if not v:raise ArithmeticError('Exact zero innovation; cannot continue unpivoted recursion')
        reflection=(r[p]-mp.fsum(a[j-1]*r[p-j] for j in range(1,p)))/v
        a=[a[j-1]-reflection*a[p-j-1] for j in range(1,p)]+[reflection]
        v*=1-reflection**2
        record(p+1,reflection)
    out.mkdir(parents=True,exist_ok=True);stem=f'{world}_mesh{mesh}_dps{dps}'
    with (out/(stem+'.csv')).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
    report=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world=world,mesh=mesh,dps=dps,increments=N,max_length=rows[-1]['length'],all_positive=positive,all_nonincreasing=monotone,first_nonpositive=rows[first-1] if first else None,first_innovation=rows[0]['innovation'],last_innovation=rows[-1]['innovation'],minimum_innovation=mp.nstr(min(mp.mpf(x['innovation']) for x in rows),70),seconds=time.monotonic()-start)
    (out/(stem+'.json')).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
    return report

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--mesh',type=int,nargs='+',default=[64,128]);p.add_argument('--dps',type=int,default=100);p.add_argument('--world',nargs='+',default=['zeta','dh']);p.add_argument('--output',type=Path,default=Path(__file__).resolve().parent);a=p.parse_args()
    for mesh in a.mesh:
        for world in a.world:run(mesh,world,a.dps,a.output)
