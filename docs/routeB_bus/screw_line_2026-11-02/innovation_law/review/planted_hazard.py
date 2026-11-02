"""Finite quartet leverage control. DIAGNOSTIC_NEVER_A_PROOF.

Read core arbitrary-precision source samples; independently factor positive
baseline and a rank-four (2 positive, 2 negative) quartet update.
Run after core/scan.py: python3 planted_hazard.py --mesh 32 64 128 256
"""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import argparse,csv,json,hashlib
import numpy as np
from scipy.linalg import toeplitz,cholesky,solve_triangular,eigvalsh
import mpmath as mp

OUT=Path(__file__).resolve().parent
CORE=OUT.parent/'core'

def run(mesh):
    zpath=CORE/f'zeta_mesh{mesh}_dps100.json'
    ppath=CORE/f'plant_mesh{mesh}_dps100.json'
    z=json.loads(zpath.read_text()); p=json.loads(ppath.read_text())
    zr=np.array(z['r_values'],dtype=float);pr=np.array(p['r_values'],dtype=float)
    n=len(zr); h=1/mesh; w=2*np.pi/np.log(2)+.25j
    q=8*(1-np.cos(w*h))/w**2
    phase=np.exp(.5j*np.angle(q)); times=np.arange(n)*h
    modes=np.column_stack([np.cos(w*times),np.sin(w*times)])*phase
    V=np.sqrt(abs(q))*modes.real; U=np.sqrt(abs(q))*modes.imag
    TZ=toeplitz(zr);TP=toeplitz(pr);C=TZ+V@V.T
    L=cholesky(C,lower=True);Y=solve_triangular(L,U,lower=True)
    theta=np.zeros((2,2)); detprev=1.;rows=[];first=None
    for k in range(n):
        theta+=np.outer(Y[k],Y[k]);ev=np.linalg.eigvalsh(theta)
        det=float(np.linalg.det(np.eye(2)-theta));signedpivot=L[k,k]**2*det/detprev
        if first is None and ev[-1]>1:first=k+1
        rows.append(dict(mesh=mesh,prefix=k+1,t=(k+1)/mesh,theta_min=ev[0],theta_max=ev[1],margin=1-ev[1],det_I_minus_theta=det,negative_index=int(sum(ev>1)),C_pivot=L[k,k]**2,plant_pivot_from_determinant_ratio=signedpivot))
        detprev=det
    table=list(csv.DictReader((CORE/f'plant_mesh{mesh}_dps100.csv').open()))
    agreement=[]
    for a,b in zip(rows,table):
        target=float(b['sigma2']);a['core_plant_pivot']=target
        a['relative_pivot_error']=abs(a['plant_pivot_from_determinant_ratio']-target)/max(abs(target),1e-300)
        agreement.append(int(b['negative_inertia'])==a['negative_index'])
    with (OUT/f'plant_hazard_mesh{mesh}.csv').open('w',newline='') as f:
        wr=csv.DictWriter(f,fieldnames=rows[0]);wr.writeheader();wr.writerows(rows)
    crossing=[]
    for nn in (first-1,first):
        if nn and nn>0:
            e=eigvalsh(TP[:nn,:nn],subset_by_index=[0,0])[0]
            crossing.append({'prefix':nn,'t':nn/mesh,'signed_kernel_eigen_min_float':float(e),'theta_max':rows[nn-1]['theta_max']})
    factor_error=np.max(np.abs(TP-(C-U@U.T)))
    chol_error=np.linalg.norm(C-L@L.T,np.inf)/np.linalg.norm(C,np.inf)
    whiten_error=np.linalg.norm(L@Y-U,np.inf)/np.linalg.norm(U,np.inf)
    summary=dict(status='DIAGNOSTIC_NEVER_A_PROOF',mesh=mesh,n=n,first_theta_crossing=first,first_negative_core=p['first_negative_prefix'],crossing_checks=crossing,all_negative_inertias_match=all(agreement),max_relative_pivot_error=max(x['relative_pivot_error'] for x in rows),quartet_matrix_reconstruction_max_abs=float(factor_error),cholesky_relative_residual=float(chol_error),whitening_relative_residual=float(whiten_error),minimum_C_pivot=float(np.min(np.diag(L)**2)),final_theta_eigenvalues=[float(v) for v in ev],min_step_theta_max=float(min(rows[i]['theta_max']-rows[i-1]['theta_max'] for i in range(1,n))),source_input_hashes={str(x.name):hashlib.sha256(x.read_bytes()).hexdigest() for x in (zpath,ppath)},arithmetic_precision='source entries 100 decimal digits; low-rank hazard and factorization IEEE float64; no interval certificate')
    assert first==p['first_negative_prefix']
    assert all(agreement)
    assert chol_error<1e-12 and whiten_error<1e-12 and factor_error<1e-12
    (OUT/f'plant_hazard_mesh{mesh}.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary),flush=True)

def mp_control():
    mp.mp.dps=80;mesh=32
    z=json.loads((CORE/'zeta_mesh32_dps100.json').read_text());p=json.loads((CORE/'plant_mesh32_dps100.json').read_text())
    zr=list(map(mp.mpf,z['r_values']));pr=list(map(mp.mpf,p['r_values']))
    h=mp.mpf(1)/mesh;w=2*mp.pi/mp.log(2)+mp.j/4;q=8*(1-mp.cos(w*h))/w**2
    phase=mp.exp(mp.j*mp.arg(q)/2);scale=mp.sqrt(abs(q)); checks=[]
    for n in (24,p['first_negative_prefix']):
        V=mp.matrix(n,2);U=mp.matrix(n,2)
        for i in range(n):
            for j,f in enumerate((mp.cos,mp.sin)):
                value=scale*phase*f(w*i*h);V[i,j]=mp.re(value);U[i,j]=mp.im(value)
        TZ=mp.matrix([[zr[abs(i-j)] for j in range(n)] for i in range(n)])
        TP=mp.matrix([[pr[abs(i-j)] for j in range(n)] for i in range(n)])
        C=TZ+V*V.T
        def get_theta(nn):
            cc=C[:nn,:nn];uu=U[:nn,:];theta=mp.matrix(2)
            solved=[mp.lu_solve(cc,uu[:,j]) for j in range(2)]
            for i in range(2):
                for j in range(2):theta[i,j]=(uu[:,i].T*solved[j])[0]
            return theta
        theta=get_theta(n);oldtheta=get_theta(n-1)
        cvec=C[:n-1,n-1];sp=C[n-1,n-1]-(cvec.T*mp.lu_solve(C[:n-1,:n-1],cvec))[0]
        ratio=sp*mp.det(mp.eye(2)-theta)/mp.det(mp.eye(2)-oldtheta)
        target=mp.mpf(list(csv.DictReader((CORE/'plant_mesh32_dps100.csv').open()))[n-1]['sigma2'])
        err=mp.norm(TP-C+U*U.T)
        checks.append({'prefix':n,'quartet_factor_frobenius_error':mp.nstr(err,30),'theta_eigenvalues':[mp.nstr(x,40) for x in mp.eigsy(theta,eigvals_only=True)],'pivot':mp.nstr(ratio,50),'relative_pivot_error':mp.nstr(abs(ratio-target)/abs(target),30)})
        assert err<mp.mpf('1e-70') and abs(ratio-target)/abs(target)<mp.mpf('1e-65')
    (OUT/'mp_hazard_validation.json').write_text(json.dumps({'status':'DIAGNOSTIC_NEVER_A_PROOF','dps':80,'checks':checks},indent=2)+'\n')
    print('MP controls',json.dumps(checks),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--mesh',type=int,nargs='+',default=[32,64,128,256]);ap.add_argument('--mp-control',action='store_true');args=ap.parse_args()
    for m in args.mesh:run(m)
    if args.mp_control:mp_control()
