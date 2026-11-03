"""Tiny manufactured spectral controls for native low2 engine, no CCM rebuild."""
from pathlib import Path
import json, subprocess
import mpmath as mp

P=Path(__file__).resolve().parent
mp.mp.dps=205

def main():
    rows=[];n=5;u=mp.matrix([1,2,3,4,5]);Q=mp.eye(n)-2*(u*u.T)/(u.T*u)[0]
    for name,lam in [('near_null',[mp.mpf('1e-90'),mp.mpf('1e-80'),mp.mpf('.5'),1,2]),
                     ('negative',[-mp.mpf('.7'),-mp.mpf('.2'),0,1,2]),
                     ('diagonal',[-mp.mpf('.7'),-mp.mpf('.2'),0,1,2])]:
        R=mp.eye(n) if name=='diagonal' else Q
        A=R*mp.diag(lam)*R.T
        payload=f'{n} 600\n'+'\n'.join(mp.nstr(A[i,j],205) for i in range(n) for j in range(n))+'\n'
        proc=subprocess.run([str(P.parent/'spectra/loweig')],input=payload,text=True,capture_output=True,check=True)
        d=json.loads(proc.stdout);ev=list(map(mp.mpf,d['lambda']));vv=[mp.matrix(list(map(mp.mpf,v))) for v in d['v']]
        errors=[abs(ev[k]-lam[k]) for k in range(2)]
        verrors=[min(mp.norm(vv[k]-R[:,k]),mp.norm(vv[k]+R[:,k])) for k in range(2)]
        residuals=[max(abs(z) for z in A*vv[k]-ev[k]*vv[k]) for k in range(2)]
        orthog=abs((vv[0].T*vv[1])[0])
        assert max(errors+residuals)<mp.mpf('1e-172')
        assert max(verrors)<mp.mpf('1e-90')
        assert orthog<mp.mpf('1e-90')
        rows.append(dict(control=name,bits=600,n=n,lambda_errors=list(map(str,errors)),vector_sign_aligned_l2_errors=list(map(str,verrors)),residual_infinity=list(map(str,residuals)),pair_orthogonality=str(orthog)))
    result=dict(status='PASS_TINY_MANUFACTURED_CONTROLS_NOT_GENERAL_CERTIFICATE',checks=rows,scope='Two low eigenpairs of 5x5 rational-Householder manufactured matrices and diagonal matrix; no source CCM eigensolve.')
    (P/'native_controls.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
