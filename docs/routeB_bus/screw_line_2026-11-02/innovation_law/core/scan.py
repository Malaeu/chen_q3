"""Source-only signed Levinson diagnostics. No positivity or RH assumption.
python3 scan.py --mesh 32 64 128 256 --world zeta dh plant --dps 100
"""
from pathlib import Path
import argparse,csv,json,time,hashlib
import mpmath as mp
OUT=Path(__file__).resolve().parent

def coefficients(M,world):
    b=[mp.mpf(0)]*(M+1)
    if world!='dh':
        prime=[True]*(M+1)
        for p in range(2,M+1):
            if prime[p]:
                for k in range(p*p,M+1,p):prime[k]=False
                n=p
                while n<=M:b[n]=mp.log(p);n*=p
    else:
        tau=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
        aa=[mp.mpf(0),mp.mpf(1),tau,-tau,-mp.mpf(1)]
        for n in range(2,M+1):
            b[n]=aa[n%5]*mp.log(n)-mp.fsum(b[d]*aa[(n//d)%5] for d in range(2,n) if n%d==0)
    return b

def source(world,end):
    M=int(mp.ceil(mp.exp(end)));b=coefficients(M,world)
    atoms=[(mp.log(n),b[n]/mp.sqrt(n),n) for n in range(2,M+1) if b[n]]
    alpha=mp.mpf('1.5') if world=='dh' else mp.mpf('.5')
    c=-mp.euler-mp.log(8*mp.pi/(5 if world=='dh' else 1))+(1 if world=='dh' else -1)*mp.pi/2
    trig=mp.polygamma(1,alpha/2)/4
    w=2*mp.pi/mp.log(2)+mp.j/4
    def g(t):
        t=abs(t)
        if not t:return mp.mpf(0)
        if t>mp.mpf('.2'):
            q=mp.exp(-2*t);term=mp.exp(-alpha*t);tail=mp.mpf(0);r=0
            while True:
                v=term/(alpha+2*r)**2;tail+=v
                if abs(v)/(1-q)<mp.eps/100:break
                term*=q;r+=1
        else:
            x=mp.exp(-t/2)
            tail=mp.polylog(2,x)-mp.polylog(2,-x)+(2 if world!='dh' else -2)*mp.im(mp.polylog(2,mp.j*x))
        v=-c*t/2-trig+tail+mp.fsum(weight*(t-a) for a,weight,n in atoms if a<t)
        if world!='dh':v-=16*mp.sinh(t/4)**2
        if world=='plant':v+=4*mp.re((mp.cos(w*t)-1)/w**2)
        return v
    return g,atoms

def fmt(x,dps):return mp.nstr(x,dps)

def run(world,mesh,dps,end=6):
    mp.mp.dps=dps;start=time.monotonic();N=int(end*mesh);h=mp.mpf(1)/mesh
    g,atoms=source(world,end);gs=[g(k*h) for k in range(N+1)]
    rr=[-2*gs[1]]+[2*gs[k]-gs[k-1]-gs[k+1] for k in range(1,N)]
    v=rr[0];aa=[];rows=[];first=None;negative=0;stop=None;snapshots={};checks=[]
    def snapshot(size):
        # chronological increment residual coefficients, last coefficient one
        ww=[-x for x in reversed(aa)]+[mp.mpf(1)]
        snapshots[str(size)]={'time':fmt(size*h,dps),'coefficients':[fmt(x,dps) for x in ww],'schur':fmt(v,dps)}
        return ww
    def record(size,reflection):
        nonlocal negative,first
        guard=mp.power(10,-dps+25)*max(1,abs(rr[0]),abs(v))
        if abs(v)<=guard:raise ArithmeticError(f'Unresolved pivot at {size}: {v}, guard {guard}')
        negative+=int(v<0)
        if v<0 and first is None:first=size
        rows.append({'world':world,'mesh':mesh,'dps':dps,'prefix':size,'t':fmt(size*h,30),'sigma2':fmt(v,dps),'reflection':fmt(reflection,dps),'negative_inertia':negative,'positive_history':negative==0,'sigma2_over_local':fmt(v/rr[0],40),'guard':fmt(guard,10)})
        if size in (mesh,3*mesh,6*mesh) or size==first:snapshot(size)
    record(1,mp.mpf(0))
    for p in range(1,N):
        reflection=(rr[p]-mp.fsum(aa[j-1]*rr[p-j] for j in range(1,p)))/v
        aa=[aa[j-1]-reflection*aa[p-j-1] for j in range(1,p)]+[reflection]
        v*=1-reflection**2;record(p+1,reflection)
        if (p+1)%256==0:print(world,mesh,dps,p+1,'negative',negative,flush=True)
    # independent dense point-kernel Schur vs increment recursion
    for n in (8,16,32):
        K=mp.matrix([[gs[abs(i-j)]-gs[i+1]-gs[j+1] for j in range(n)] for i in range(n)])
        bb=K[:n-1,n-1];direct=K[n-1,n-1]-(bb.T*mp.lu_solve(K[:n-1,:n-1],bb))[0]
        checks.append({'kind':'point_kernel_dense_schur','prefix':n,'absolute_error':fmt(abs(direct-mp.mpf(rows[n-1]['sigma2'])),30)})
    if first:
        ww=[mp.mpf(x) for x in snapshots[str(first)]['coefficients']]
        direct=rr[0]*mp.fsum(x*x for x in ww)+2*mp.fsum(rr[k]*mp.fsum(ww[i]*ww[i+k] for i in range(first-k)) for k in range(1,first))
        vv=mp.mpf(rows[first-1]['sigma2'])
        checks.append({'kind':'first_negative_direct_quadratic','prefix':first,'direct':fmt(direct,dps),'normalized_rayleigh':fmt(direct/mp.fsum(x*x for x in ww),dps),'relative_error':fmt(abs(direct-vv)/abs(vv),30),'negative':direct<0})
    stem=f'{world}_mesh{mesh}_dps{dps}'
    with (OUT/(stem+'.csv')).open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=rows[0]);writer.writeheader();writer.writerows(rows)
    record={'status':'DIAGNOSTIC_NEVER_A_PROOF','world':world,'mesh':mesh,'dps':dps,'end':end,'rows':len(rows),'first_negative_prefix':first,'first_negative_time':fmt(first*h,30) if first else None,'negative_inertia_final':negative,'first_sigma2':rows[0]['sigma2'],'last_sigma2':rows[-1]['sigma2'],'g_values':[fmt(x,dps) for x in gs],'r_values':[fmt(x,dps) for x in rr],'snapshots':snapshots,'checks':checks,'seconds':time.monotonic()-start,'source_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (OUT/(stem+'.json')).write_text(json.dumps(record,indent=2)+'\n')
    print('DONE',world,mesh,dps,'firstnegative',record['first_negative_time'],'last',fmt(v,20),'seconds',record['seconds'],flush=True)
    return record

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--mesh',nargs='+',type=int,default=[32,64,128,256]);p.add_argument('--world',nargs='+',default=['zeta','dh','plant']);p.add_argument('--dps',type=int,default=100);a=p.parse_args()
    for mesh in a.mesh:
        for world in a.world:run(world,mesh,a.dps)
