"""Small-source-geometry diagnostics, binary64. No full CCM or prime spectrum run."""
from pathlib import Path
import numpy as np
import math,json,hashlib
rows=[];sign_rows=[]
for power in (512,768,1024):
    L=power*math.log(2); M=1 << (power//64)
    j=np.arange(-M,M+1,dtype=float); om=2*math.pi*j/L
    ell0=-math.expm1(-L/2)/(np.sqrt(L)*(.5+1j*om))
    r0=np.conj(ell0); b=np.ones(2*M+1)/np.sqrt(2*M+1)
    C=np.column_stack([ell0,r0,b]); G=C.conj().T@C
    def project(v):return v-C@np.linalg.solve(G,C.conj().T@v)
    for delta,gamma in ((.125,1.),(.25,14.),(.375,.75)):
        w=delta+1j*gamma
        ell=-np.expm1(-w*L)/(np.sqrt(L)*(w+1j*om))
        right=np.exp(-1j*gamma*L)*np.conj(ell)
        p=project(right);q=project(ell)
        aa=float(np.vdot(p,p).real);bb=float(np.vdot(q,q).real)
        z=np.vdot(p,q)
        disc=max(0.,aa*bb-z.imag*z.imag)
        eig_formula=z.real-math.sqrt(disc)
        _,R=np.linalg.qr(np.column_stack([p,q]),mode='reduced')
        H2=R@np.array([[0.,1.],[1.,0.]])@R.conj().T
        eig_qr=float(np.linalg.eigvalsh(H2)[0])
        kap=1/(2*delta)-1/((delta+.5)**2+gamma**2)
        residual=max(np.max(np.abs(C.conj().T@p)),np.max(np.abs(C.conj().T@q)))
        assert abs(eig_qr-eig_formula)<2e-11
        assert residual<2e-11
        rows.append({'m':'2^'+str(power),'epsilon':'1/64','M':M,'delta':delta,'gamma':gamma,
                     'scaled_negative_eigenvalue':eig_formula,'predicted_limit':-kap,
                     'limit_difference':eig_formula+kap,'projected_overlap_abs':float(abs(z)),
                     'qr_formula_error':abs(eig_qr-eig_formula),'constraint_residual':float(residual)})
    tail=143/321489; a2=math.log(2)/256
    for name,idx in [('positive',0),('negative',round(L/(2*math.log(2))))]:
        assert abs(idx)<=M
        e=np.zeros(2*M+1,dtype=complex);e[idx+M]=1
        c=project(e);c/=np.linalg.norm(c)
        dist=float(np.linalg.norm(c-e))
        diag=2*(1-math.log(2)/L)*math.cos(2*math.pi*idx*math.log(2)/L)
        lower=a2*(diag-4*dist)-2*tail
        upper=a2*(diag+4*dist)+2*tail
        assert (lower>0) if name=='positive' else (upper<0)
        sign_rows.append({'m':'2^'+str(power),'epsilon':'1/64','M':M,'direction':name,'j':idx,
                          'distance_to_original_mode':dist,'sigma8_form_lower_budget':lower,
                          'sigma8_form_upper_budget':upper})
out={'status':'PASS_DIAGNOSTIC_NOT_INTERVAL','pair_cases':len(rows),'damped_sign_cases':len(sign_rows),
     'precision':'binary64','source':'original projected modes; auxiliary single-pair geometry and sigma8 damped source only',
     'actual_zero_claim':False,'full_prime_sums_evaluated':False,'actual_Km_spectral_runs':0,
     'pair_rows':rows,'damped_sign_rows':sign_rows,
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('projected_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
