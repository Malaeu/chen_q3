"""Owner-authorized Task A instrument fix. Original source/results unchanged.

Uses the original primitives directly; full-line quadrature and quartet
polarization follow the original task_a.py. Numerical DIAG, not intervals.
"""
from pathlib import Path
import importlib.util,json,hashlib,platform,time,datetime
import mpmath as mp

OUT=Path(__file__).resolve().parent
ORIGINAL=OUT.parent/'scripts/task_a.py'
SOURCE=OUT.parent/'SOURCE_VERDICT.md'
spec=importlib.util.spec_from_file_location('original_task_a',ORIGINAL)
original=importlib.util.module_from_spec(spec);spec.loader.exec_module(original)
C,F,g,atoms=original.C,original.F,original.g,original.atoms
TS=['0','0.5','1','1.5','2']
PREREG='c64e6038675138381df066e711aed895e22b550f'

def git_blob(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

def prime_tail_bound(t,cut):
    """Analytic integral majorant. See RESULT.md for proof, v>=b>11.99."""
    b=mp.log(cut)-t
    D=b-mp.mpf('.5')-9/b
    assert b>mp.mpf('11.99') and D>0
    polynomial_coefficient_ratio=1+mp.mpf('28.5')/b**2+mp.mpf('217.5625')/b**4+mp.mpf('442.875')/b**6+mp.mpf('112.6875')/b**8
    assert polynomial_coefficient_ratio<2
    raw=4*mp.exp(t/2)/mp.sqrt(2*mp.pi)*(b+t)*b**8*mp.exp(b/2-b*b/2)/D
    # Deliberate 0.1% slack, then round upward to eight significant digits.
    # This is not an interval library; the analytic bound is the raw formula.
    slack=raw*mp.mpf('1.001')
    unit=mp.power(10,mp.floor(mp.log10(slack))-7)
    upper=mp.ceil(slack/unit)*unit
    return dict(b=str(b),D=str(D),coefficient_ratio=str(polynomial_coefficient_ratio),analytic_majorant=str(raw),reported_upper=str(upper),below_1e_18=bool(upper<mp.mpf('1e-18')))

def zero_tail_bound(t):
    return mp.fsum(2*(k+1)**2*(k*k+mp.mpf('.25'))**2*(k*k+mp.mpf('.5'))**2*mp.exp(mp.mpf('.125')-mp.mpf(k*k)/2+t/2) for k in range(60,101))*mp.mpf('1.0000000001')

def main():
    assert git_blob(SOURCE.read_bytes())=='2b5e02a0aa816da34c204f2a56a9033e6ac6b542'
    started=datetime.datetime.now(datetime.timezone.utc).isoformat();wall=time.monotonic()
    with mp.workdps(70): maximum=int(mp.floor(mp.exp(14)))
    aa=atoms(maximum)
    rows=[];dps_meta=[]
    for dps in [50,70]:
        mp.mp.dps=dps
        zeros=[];k=1
        while True:
            z=mp.zetazero(k)
            if z.imag>60:break
            zeros.append(z-mp.mpf('.5'));k+=1
        u=mp.mpf(1)/3+7j
        Gu=mp.quad(lambda x:g(x)*mp.exp(u*x),[-mp.inf,-8,-4,0,4,8,mp.inf])
        cstar=mp.euler+mp.log(8*mp.pi)+mp.pi/2
        logs={p:mp.log(p) for _,p in aa}
        dps_meta.append(dict(dps=dps,positive_zero_count=len(zeros),next_zero_height=str(z.imag),quartet_moment_quad_real=str(Gu.real),quartet_moment_quad_imag=str(Gu.imag),quartet_moment_transform_real=str(F(u).real),quartet_moment_transform_imag=str(F(u).imag),cstar=str(cstar)))
        for ts in TS:
            t=mp.mpf(ts);cut=int(mp.floor(mp.exp(t+12)))
            def integrand(s):
                if not s:return mp.mpf(0)
                return mp.exp(-s/2)/(-mp.expm1(-2*s))*(2*C(t)-C(t-s)-C(t+s))
            H=mp.quad(integrand,[0,mp.mpf('.1'),1,4,8,16,32,mp.inf])-cstar*C(t)
            S=mp.fsum(logs[p]/mp.sqrt(n)*(C(t-mp.log(n))+C(t+mp.log(n))) for n,p in aa if n<=cut)
            Z=2*mp.re(mp.fsum(F(z)**2*mp.exp(z*t) for z in zeros))
            pa=2*mp.re(Gu**2*(mp.exp(u*t)+mp.exp(-u*t)))
            pz=2*mp.re(F(u)**2*(mp.exp(u*t)+mp.exp(-u*t)))
            tail=prime_tail_bound(t,cut)
            for world,ar_add,z_add in [('zeta',mp.mpf(0),mp.mpf(0)),('zeta_plus_quartet',pa,pz)]:
                ar=H-S+ar_add;zero=Z+z_add;gate=mp.mpf('1e-15')
                delta=-mp.mpf('1e-10')*C(t);shifted=ar+delta
                baseline_pass=bool(abs(ar-zero)<=gate)
                plant_fail=bool(abs(shifted-zero)>gate)
                ok=baseline_pass and plant_fail and tail['below_1e_18']
                row=dict(t=ts,dps=dps,world=world,cutoff=cut,H=str(H),S=str(S),C_t=str(C(t)),quartet_arithmetic_addition=str(ar_add),quartet_zero_addition=str(z_add),arithmetic=str(ar),zero=str(zero),baseline_residual=str(ar-zero),baseline_pass=baseline_pass,gate=str(gate),cstar_shift='1e-10',shift_delta=str(delta),shifted_arithmetic=str(shifted),shifted_residual=str(shifted-zero),plant_fail=plant_fail,prime_tail=tail,zero_tail_bound=str(zero_tail_bound(t)),cancellation_ratio_zero=str((abs(H)+abs(S))/abs(zero)),status='PASS' if ok else 'INSTRUMENT_FAILURE')
                rows.append(row)
            data=dict(status='PASS' if all(r['status']=='PASS' for r in rows) else 'INSTRUMENT_FAILURE',complete=len(rows)==20,rows=rows,dps_metadata=dps_meta,preregistration_commit=PREREG,base_commit='2cd805e0abf59d21ab103410548e9b011e5ee7a5',source_git_blob=git_blob(SOURCE.read_bytes()),source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),original_script_git_blob=git_blob(ORIGINAL.read_bytes()),original_script_sha256=hashlib.sha256(ORIGINAL.read_bytes()).hexdigest(),python=platform.python_version(),mpmath=mp.__version__,started_utc=started,seconds=time.monotonic()-wall,interval_certificate=False)
            (OUT/'results.json').write_text(json.dumps(data,indent=2)+'\n')
            print(json.dumps(dict(t=ts,dps=dps,zeta_residual=rows[-2]['baseline_residual'],quartet_residual=rows[-1]['baseline_residual'],prime_tail_bound=tail['reported_upper'],plant_residual=rows[-2]['shifted_residual'],status=rows[-2]['status'])),flush=True)
    if data['status']!='PASS':raise SystemExit('INSTRUMENT_FAILURE')
if __name__=='__main__':main()
