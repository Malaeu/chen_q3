"""Full-line heat fits with window length and modal resolution explicitly separated."""
from pathlib import Path
import sys,argparse,json,csv,hashlib,time,importlib.util
import numpy as np
from scipy.optimize import minimize_scalar
import mpmath as mp
OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(OUT.parent))
import heat_fit as heat
import heat_review as review

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def fmt(x):return mp.nstr(x,mp.mp.dps)
def theta(x):
    x=abs(x);u=mp.exp(2*x);total=mp.mpf(0);n=1
    while mp.pi*n*n*u<mp.mpf('2.5')*mp.mp.prec:
        z=mp.pi*n*n*u
        total+=(16*z*z-24*z)*mp.exp(-z);n+=1
    return mp.exp(x/2)*total

def physical_projection(src,L,N):
    hv=[theta(L*(y-mp.mpf('.5'))) for y,w in src.nodes]
    return mp.matrix([mp.sqrt(L)*(1 if n==0 else mp.sqrt(2))*mp.fsum(w*hv[i]*src.trig[n][i][1] for i,(y,w) in enumerate(src.nodes)) for n in range(N+1)])

def get_builder(args):
    old=sys.argv;sys.argv=['matrix',str(args.matrix_order),str(args.dps)]
    spec=importlib.util.spec_from_file_location('resolution_matrix',OUT/'matrix_core.py')
    src=importlib.util.module_from_spec(spec);spec.loader.exec_module(src);sys.argv=old
    return src

def run(args):
    src=get_builder(args);mp.mp.dps=args.dps;start=time.monotonic()
    cache=Path('/tmp')/f'heat_spectrum_dps{args.dps}_gl{args.spectral_order}_T{args.T}_step4.json'
    tt,ww=heat.spectral_nodes(args.spectral_order,args.T,4,cache)
    cells=[(8,68)] if args.validation else [(8,44),(8,56),(8,68),(12,44)]
    literal=json.loads((OUT.parent/'main_results.json').read_text())
    literal_s={int(r['m']):mp.mpf(r['s']) for r in literal['results'] if r['family']=='heat'}
    _,_,variance=review.heat_moments()
    allrows=[];allraw=[]
    for wm in sorted(set(m for m,n in cells)):
        Ns=[n for m,n in cells if m==wm];NN=max(Ns);L=mp.log(wm)
        # Atom cutoff is the physical window, independent of modal N.
        src.atoms=[(k,mp.log(k),src.mang(k)/mp.sqrt(k)) for k in range(2,wm+1) if src.mang(k)]
        K,_=src.matrices(L,NN);EA=src.even(K,NN,NN)
        phys_h=physical_projection(src,L,NN)
        BW=heat.projection_matrix(dict(m=NN,L=L),tt,ww)
        print('WINDOW',wm,'Nmax',NN,'elapsed',time.monotonic()-start,flush=True)
        for N in Ns:
            A=EA[:N+1,:N+1];ev,V=mp.eigsy(A);f=V[:,0];h=phys_h[:N+1,:]
            if mp.fdot(f,h)<0:f=-f
            f/=mp.norm(f);lam=ev[0]
            B=BW[:N+1,:];baseline=mp.fdot(f,h)**2/mp.fdot(h,h)
            bn=np.array(B.tolist(),dtype=float);tn=np.array([float(t*t) for t in tt]);fn=np.array(list(f),dtype=float)
            def objective(s):
                p=bn@np.exp(-s*tn);e=fn-p*np.dot(fn,p)/np.dot(p,p);return np.dot(e,e)
            grid=np.unique(np.concatenate(([0.],np.linspace(0,.02,201),np.geomspace(.02,1.,81))))
            vals=[objective(s) for s in grid];candidates=[(vals[0],0.),(vals[-1],1.)]
            for i in range(1,len(grid)-1):
                if vals[i]<=vals[i-1] and vals[i]<=vals[i+1]:
                    q=minimize_scalar(objective,bounds=(grid[i-1],grid[i+1]),method='bounded',options={'xatol':1e-15})
                    candidates.append((q.fun,q.x))
            approx=min(candidates)[1]
            def calc(s):return heat.heat_vectors(B,tt,s)
            def grad(s):
                p,dp=calc(s);return mp.fdot(f,dp)*mp.fdot(p,p)-mp.fdot(f,p)*mp.fdot(p,dp)
            s=mp.mpf(0) if approx==0 else mp.findroot(grad,(mp.mpf(str(approx))*mp.mpf('.999'),mp.mpf(str(approx))*mp.mpf('1.001')),tol=mp.power(10,-args.dps+25),maxsteps=30)
            assert s>=0
            p,dp=calc(s);norm2=mp.fdot(p,p);coef=mp.fdot(f,p)/norm2;e=f-coef*p
            energy=mp.fdot(p,A*p)/norm2
            p0,_=calc(mp.mpf(0));control=mp.norm(p0-h)/mp.norm(h)
            bound=review.large_s_overlap_bound(f[0],L,1,variance)
            row=dict(window_m=wm,N=N,L=fmt(L),dps=args.dps,matrix_order=args.matrix_order,spectral_order=args.spectral_order,T=args.T,
                     lambda0=fmt(lam),gap=fmt(ev[1]-ev[0]),s_star=fmt(s),literal_N_equals_m_s=fmt(literal_s[wm]),
                     s_minus_literal=fmt(s-literal_s[wm]),s_ratio_to_literal=fmt(s/literal_s[wm]),
                     w0=fmt(baseline),w_star=fmt(mp.fdot(f,p)**2/norm2),residual_squared=fmt(mp.fdot(e,e)),
                     coefficient_c=fmt(coef),heat_projection_norm_squared=fmt(norm2),Rayleigh_energy=fmt(energy),energy_over_lambda0=fmt(energy/lam),
                     eigenpair_residual=fmt(mp.norm(A*f-lam*f)),stationary_residual=fmt(grad(s)),
                     zero_time_projection_relative_error=fmt(control),all_s_ge_1_overlap_upper=fmt(bound['overlap_squared_upper']))
            raw=dict(**row,ground_even_coefficients=[fmt(z) for z in f],physical_h_coefficients=[fmt(z) for z in h],
                     heat_coefficients=[fmt(z) for z in p],heat_derivative_coefficients=[fmt(z) for z in dp],
                     residual_coefficients=[fmt(z) for z in e],eigenvalues=[fmt(z) for z in ev],
                     active_atoms=[dict(k=k,log_k=fmt(a),weight=fmt(w)) for k,a,w in src.atoms if a<L],
                     source_hashes={str(x.relative_to(OUT.parent)):sha(x) for x in (OUT/'matrix_core.py',OUT/'resolution_fit.py',OUT.parent/'heat_fit.py',OUT.parent/'heat_review.py')},
                     spectral_cache=dict(path=str(cache),sha256=sha(cache)),float_grid_candidates=[[float(v),float(t)] for v,t in candidates],
                     scope='Finite resolution diagnostic; best-found compact stationary candidate, no interval global optimum certificate')
            allrows.append(row);allraw.append(raw)
            tag='validation' if args.validation else 'main'
            (OUT/f'{tag}_results.json').write_text(json.dumps(dict(results=allraw,status='DIAGNOSTIC_NEVER_A_PROOF',elapsed=time.monotonic()-start),indent=2)+'\n')
            with (OUT/f'{tag}_fits.csv').open('w',newline='') as out:
                cw=csv.DictWriter(out,fieldnames=list(allrows[0]));cw.writeheader();cw.writerows(allrows)
            print('FIT',wm,N,'s',mp.nstr(s,25),'residual2',mp.nstr(mp.fdot(e,e),15),'E/lam',mp.nstr(energy/lam,15),flush=True)
    print('DONE',time.monotonic()-start,flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--dps',type=int,default=140);ap.add_argument('--matrix-order',type=int,default=128);ap.add_argument('--spectral-order',type=int,default=56);ap.add_argument('--T',type=int,default=320);ap.add_argument('--validation',action='store_true');run(ap.parse_args())
