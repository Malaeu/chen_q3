"""Local-envelope zeta-zero residuals; DIAGNOSTIC_NEVER_A_PROOF.

Fresh 180-dps literal eigensystems, not promoted 100-dps coefficients.
delta = half the smaller adjacent positive-zero gap (first zero: next gap).
"""
from pathlib import Path
import sys,csv,json,argparse,time
import mpmath as mp
OUT=Path(__file__).resolve().parent
def fmt(x):return mp.nstr(x,170)
def save(name,rows):
    with (OUT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
def load(m,dps=180):
    order=160 if dps==180 else 192
    r=json.loads((OUT/f'core_m{m}_dps{dps}_gl{order}.json').read_text())
    V=mp.matrix(r['V']);indices=list(range(8))+[m//2,m-2]
    C=mp.matrix([[V[n,i] for i in indices] for n in range(m+1)])
    L=mp.log(m)
    return dict(m=m,L=L,b=L/2,C=C,indices=indices,omega=[2*mp.pi*n/L for n in range(m+1)],d=[mp.mpf(1)]+[mp.sqrt(2)]*m)
def sp(x):return (x*mp.cos(x)-mp.sin(x))/(x*x) if x else mp.mpf(0)
def basis(a,t,derivative=False):
    b=a['b'];L=a['L'];ss=mp.sin(b*t);cc=mp.cos(b*t);out=[]
    for n,om in enumerate(a['omega']):
        if abs(t-om)<mp.mpf('1e-30'):
            z=a['d'][n]*(-1)**n*b/mp.sqrt(L)
            q=z*b*(sp((t-om)*b)+sp((t+om)*b)) if derivative else z*(mp.sinc((t-om)*b)+mp.sinc((t+om)*b))
        else:
            den=t*t-om*om
            q=2*a['d'][n]/mp.sqrt(L)*((ss+b*t*cc)/den-2*t*t*ss/(den*den) if derivative else t*ss/den)
        out.append(q)
    return mp.matrix(out)
def all_values(a,t,derivative=False):return a['C'].T*basis(a,t,derivative)
def one(a,j,t,derivative=False):return mp.fdot(a['C'][:,j],basis(a,t,derivative))
def prepare():
    mp.mp.dps=180;zz=[];k=1
    while True:
        g=mp.im(mp.zetazero(k));zz.append(g)
        if g>300:break
        if k%20==0:print('zero',k,flush=True)
        k+=1
    rows=[]
    for j,g in enumerate(zz[:-1]):
        ng=zz[j+1]-g;pg=g-zz[j-1] if j else None
        delta=min(pg,ng)/2 if j else ng/2
        rows.append(dict(k=j+1,gamma=fmt(g),previous_gap=fmt(pg) if pg is not None else '',next_gap=fmt(ng),
                         delta=fmt(delta),left=fmt(g-delta),right=fmt(g+delta)))
    save('zeros.csv',rows)
    (OUT/'zero_metadata.json').write_text(json.dumps(dict(dps=180,count=len(rows),last_gamma=fmt(zz[-2]),
        next_gamma_above_300=fmt(zz[-1]),delta='half min(previous gap,next gap); first positive zero uses next gap only'),indent=2)+'\n')
def run(m,panels=32):
    mp.mp.dps=180;start=time.monotonic();a=load(m);rows=[]
    for z in csv.DictReader((OUT/'zeros.csv').open()):
        k=int(z['k']);g=mp.mpf(z['gamma']);delta=mp.mpf(z['delta']);left=g-delta;right=g+delta
        grid=[left+(right-left)*q/panels for q in range(panels+1)]
        vv=[all_values(a,t) for t in grid];dd=[all_values(a,t,True) for t in grid];atg=all_values(a,g)
        for j,i in enumerate(a['indices']):
            candidates=[(abs(v[j]),t,'grid') for t,v in zip(grid,vv)]+[(abs(atg[j]),g,'gamma')]
            scale=max(abs(v[j]) for v in dd);count=0
            if scale:
                for q in range(panels):
                    if dd[q][j]*dd[q+1][j]<0:
                        fun=lambda t:one(a,j,t,True)/scale
                        root=mp.findroot(fun,(grid[q],grid[q+1]),solver='anderson',tol=mp.mpf('1e-70'),maxsteps=150)
                        if not grid[q]<=root<=grid[q+1]:raise ArithmeticError('stationary root left bracket')
                        candidates.append((abs(one(a,j,root)),root,'stationary'));count+=1
            den,argmax,kind=max(candidates,key=lambda x:x[0]);num=abs(atg[j])
            if argmax==left or argmax==right:kind='endpoint'
            assert den>0 and num<=den
            rows.append(dict(m=m,i=i,role='cluster' if i<8 else 'control',k=k,gamma=fmt(g),delta=fmt(delta),
                numerator=fmt(num),denominator=fmt(den),rho=fmt(num/den),argmax=fmt(argmax),peak_location=kind,
                stationary_count=count,grid_subintervals=panels,dps=180))
        if k%20==0:print('m',m,'zero',k,'seconds',time.monotonic()-start,flush=True)
    save(f'samples_m{m}.csv',rows)
    print('DONE',m,time.monotonic()-start,flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--prepare',action='store_true');p.add_argument('--m',type=int);p.add_argument('--panels',type=int,default=32);q=p.parse_args()
    if q.prepare:prepare()
    if q.m:run(q.m,q.panels)
