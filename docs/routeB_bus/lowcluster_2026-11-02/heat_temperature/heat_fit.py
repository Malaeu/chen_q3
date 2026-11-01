"""Full-line forward heat followed by literal CCM projection.

DIAGNOSTIC_NEVER_A_PROOF. No periodic heat or modal-damping surrogate.
Run: uv run --with mpmath --with numpy --with scipy python3 heat_fit.py
"""
from pathlib import Path
import argparse, csv, hashlib, json, sys, time
import mpmath as mp
import numpy as np
from scipy.optimize import minimize_scalar

OUT=Path(__file__).resolve().parent
PARENT=OUT.parent

def fmt(x): return mp.nstr(x,80)
def csvout(name,rows):
    with (OUT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]); w.writeheader(); w.writerows(rows)
def H(t):
    z=mp.mpf('.5')+mp.j*t
    return mp.re(2*z*(z-1)*mp.pi**(-z/2)*mp.gamma(z/2)*mp.zeta(z))
def source(m,high=False):
    base=OUT if m==8 else PARENT
    suffix='dps140_gl160' if high and m in (8,24) else 'dps100_gl128'
    path=base/f'core_m{m}_{suffix}.json'
    d=json.loads(path.read_text()); A=mp.matrix(d['A']); f=mp.matrix(d['V'])[:,0]
    J=mp.matrix(d['ladder']['projected_profile_coefficients'])
    if mp.fdot(f,J[:,0])<0:f=-f
    f=f/mp.norm(f)
    return dict(m=m,L=mp.log(m),A=A,f=f,h=J[:,0],h2=J[:,1],h4=J[:,2],
                lam=mp.mpf(d['lambda_'][0]),path=path,
                sha256=hashlib.sha256(path.read_bytes()).hexdigest())
def spectral_nodes(order,T,step,cache):
    if cache.exists():
        r=json.loads(cache.read_text())
        return [mp.mpf(x) for x in r['t']], [mp.mpf(x) for x in r['weightsH_over_pi']]
    gn,gw=mp.gauss_quadrature(order,'legendre');tt=[];ww=[]
    for j in range(int(T/step)):
        mid=mp.mpf(str(step))*(j+mp.mpf('.5'));half=mp.mpf(str(step))/2
        for z,w in zip(gn,gw):
            t=mid+half*z; tt.append(t);ww.append(half*w*H(t)/mp.pi)
        if j%8==0:print('spectral panel',j,'/',int(T/step),flush=True)
    cache.write_text(json.dumps(dict(dps=mp.mp.dps,order=order,T=T,step=step,
        t=[mp.nstr(t,mp.mp.dps) for t in tt],weightsH_over_pi=[mp.nstr(w,mp.mp.dps) for w in ww])))
    return tt,ww
def projection_matrix(d,tt,ww):
    L=d['L'];b=L/2;ss=[mp.sin(b*t) for t in tt];B=mp.matrix(d['m']+1,len(tt))
    for n in range(d['m']+1):
        dn=mp.sqrt(2) if n else mp.mpf(1);om=2*mp.pi*n/L
        for j,t in enumerate(tt):
            if abs(t-om)<mp.mpf('1e-40'):
                bn=dn*(-1)**n*b/mp.sqrt(L)*(mp.sinc((t-om)*b)+mp.sinc((t+om)*b))
            else:bn=2*dn*t*ss[j]/(mp.sqrt(L)*(t*t-om*om))
            B[n,j]=ww[j]*bn
    return B
def heat_vectors(B,tt,s):
    ex=[mp.exp(-s*t*t) for t in tt]
    v=B*mp.matrix(ex);dv=B*mp.matrix([-t*t*x for t,x in zip(tt,ex)])
    return v,dv
def poly_vectors(d,s):
    return d['h']+s*d['h2']+s*s*d['h4']/2,d['h2']+s*d['h4']
def objective_derivative(d,v,dv):
    a=mp.fdot(d['f'],v);b=mp.fdot(v,v)
    return mp.fdot(d['f'],dv)*b-a*mp.fdot(v,dv)
def measures(d,v):
    f=d['f'];b=mp.fdot(v,v);c=mp.fdot(f,v)/b;e=f-c*v
    energy=mp.fdot(v,d['A']*v)/b
    return dict(c=fmt(c),norm_v_squared=fmt(b),w=fmt(mp.fdot(f,v)**2/b),
                residual_squared=fmt(mp.fdot(e,e)),energy=fmt(energy),
                energy_over_lambda0=fmt(energy/d['lam']))
def run(args):
    start=time.monotonic();mp.mp.dps=args.dps
    cache=Path('/tmp')/f'heat_spectrum_dps{args.dps}_gl{args.order}_T{args.T}_step{args.step}.json'
    tt,ww=spectral_nodes(args.order,args.T,args.step,cache)
    rows=[];details=[];scans=[];controls=[]
    for m in args.ms:
        d=source(m,args.high_source);B=projection_matrix(d,tt,ww)
        bn=np.array(B.tolist(),dtype=float);tn=np.array([float(t*t) for t in tt]);fn=np.array(list(d['f']),dtype=float)
        hh=np.array(list(d['h']),dtype=float);h2=np.array(list(d['h2']),dtype=float);h4=np.array(list(d['h4']),dtype=float)
        v0,dv0=heat_vectors(B,tt,mp.mpf(0))
        controls.append(dict(m=m,h_projection_relative_error=fmt(mp.norm(v0-d['h'])/mp.norm(d['h'])),
                             h2_projection_relative_error=fmt(mp.norm(dv0-d['h2'])/mp.norm(d['h2']))))
        baseline=measures(d,d['h'])
        grid=np.unique(np.concatenate(([0.],np.linspace(0,.02,201),np.geomspace(1e-7,100,161))))
        for family in ('heat','quadratic'):
            def vf(s):return bn@np.exp(-s*tn) if family=='heat' else hh+s*h2+s*s*h4/2
            def obj(s):
                v=vf(s);e=fn-v*np.dot(fn,v)/np.dot(v,v)
                return np.dot(e,e)
            vals=[obj(s) for s in grid];candidates=[(vals[0],0.),(vals[-1],grid[-1])]
            for i in range(1,len(grid)-1):
                if vals[i]<=vals[i-1] and vals[i]<=vals[i+1]:
                    rr=minimize_scalar(obj,bounds=(grid[i-1],grid[i+1]),method='bounded',options={'xatol':1e-15})
                    candidates.append((rr.fun,rr.x))
            approx=min(candidates)[1]
            calc=(lambda s:heat_vectors(B,tt,s)) if family=='heat' else (lambda s:poly_vectors(d,s))
            if approx==0:s=mp.mpf(0)
            else:
                def grad(s):return objective_derivative(d,*calc(s))
                s=mp.findroot(grad,(mp.mpf(str(approx))*.999,mp.mpf(str(approx))*1.001),tol=mp.mpf('1e-65'),maxsteps=30)
            v,dv=calc(s);ms=measures(d,v)
            row=dict(m=m,family=family,s=fmt(s),s_times_m=fmt(s*m),s_times_log_m=fmt(s*d['L']),s_times_m_squared=fmt(s*m*m),
                     w0=baseline['w'],baseline_residual_squared=baseline['residual_squared'],lambda0=fmt(d['lam']),**ms,
                     stationary_residual=fmt(objective_derivative(d,v,dv)),dps=args.dps,quadrature_order=args.order,T=args.T)
            rows.append(row)
            details.append(dict(**row,projected_vector=[fmt(x) for x in v],source=str(d['path'].relative_to(PARENT)),source_sha256=d['sha256'],
                                grid_candidates=[[float(x),float(y)] for x,y in candidates]))
            for sg,val in zip(grid,vals):scans.append(dict(m=m,family=family,s=sg,residual_squared_float_scan=val))
            print('FIT',m,family,'s',fmt(s),'residual',ms['residual_squared'],'E/lambda',ms['energy_over_lambda0'],flush=True)
        if args.tag=='main':
            csvout('fits.csv',rows);csvout('projection_controls.csv',controls);csvout('scan.csv',scans)
        (OUT/f'{args.tag}_results.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',domain='s>=0',
            method='full-line Fourier integral then physical support/modal projection',dps=args.dps,order=args.order,T=args.T,
            step=args.step,controls=controls,results=details,elapsed_seconds=time.monotonic()-start),indent=2)+'\n')
    print('DONE',time.monotonic()-start,flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--dps',type=int,default=100);p.add_argument('--order',type=int,default=40)
    p.add_argument('--T',type=int,default=256);p.add_argument('--step',type=int,default=4);p.add_argument('--ms',type=int,nargs='+',default=[8,12,16,20,24])
    p.add_argument('--high-source',action='store_true');p.add_argument('--tag',default='main');run(p.parse_args())
