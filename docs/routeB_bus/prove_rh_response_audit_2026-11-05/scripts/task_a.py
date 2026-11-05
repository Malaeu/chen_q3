"""Literal prescribed Task A; no cutoff retuning. Diagnostic mp arithmetic."""
import json,sys,time,hashlib,platform
from pathlib import Path
import mpmath as mp
import numpy as np
OUT=Path(__file__).resolve().parents[1]
TS=['0','.5','1','2','3','4','5','6']
def C(t):
    z=t*t
    return ((((z-mp.mpf('28.5'))*z+mp.mpf('217.5625'))*z-mp.mpf('442.875'))*z+mp.mpf('112.6875'))*mp.exp(-z/2)/mp.sqrt(2*mp.pi)
def F(u):return u*u*(u*u-mp.mpf('.25'))*mp.exp(u*u/4)
def g(x):return (16*x**4-49*x*x+mp.mpf('12.5'))*mp.exp(-x*x)/mp.sqrt(mp.pi)
def atoms(N):
    sieve=np.ones(N+1,dtype=bool);sieve[:2]=False;ans=[]
    for p in range(2,N+1):
        if sieve[p]:
            sieve[p*p::p]=False;n=p
            while n<=N:ans.append((n,p));n*=p
    return sorted(ans)
def main():
    N=int(mp.ceil(mp.exp(15)))+100;aa=atoms(N);results=[];start=time.time()
    for dps in [60,80]:
        mp.mp.dps=dps
        zeros=[];k=1
        while True:
            z=mp.zetazero(k)
            if z.imag>60:break
            zeros.append(z-mp.mpf('.5'));k+=1
        # All zeros counted with multiplicity. N(T)<=T^2 for T>=60 is a
        # deliberately loose classical counting majorant. Each integer shell
        # has <=2(k+1)^2 zeros counting both ordinates. |delta|<=1/2.
        def ztail(t):
            return mp.fsum(2*(k+1)**2*(k*k+mp.mpf('.25'))**2*(k*k+mp.mpf('.5'))**2*mp.exp(mp.mpf('.125')-mp.mpf(k*k)/2+t/2) for k in range(60,101)) * mp.mpf('1.0000000001')
        u=mp.mpf(1)/3+7j
        # Builder Q=4 Re(c c^T) on even sector, polarized on translated
        # even g: sum over +/-u,+/-conj(u). Compute moments independently
        # by full-line quadrature instead of substituting F.
        Gu=mp.quad(lambda x:g(x)*mp.exp(u*x),[-mp.inf,-8,-4,0,4,8,mp.inf])
        cstar=mp.euler+mp.log(8*mp.pi)+mp.pi/2
        logs={p:mp.log(p) for _,p in aa}
        for ts in TS:
            t=mp.mpf(ts);cut=int(mp.floor(mp.exp(t+9)))
            def integrand(s):
                if not s:return mp.mpf(0)
                # The even second difference has a removable endpoint.
                return mp.exp(-s/2)/(-mp.expm1(-2*s))*(2*C(t)-C(t-s)-C(t+s))
            H=mp.quad(integrand,[0,mp.mpf('.1'),1,4,8,16,32,mp.inf])-cstar*C(t)
            S=mp.fsum(logs[p]/mp.sqrt(n)*(C(t-mp.log(n))+C(t+mp.log(n))) for n,p in aa if n<=cut)
            Z=2*mp.re(mp.fsum(F(z)**2*mp.exp(z*t) for z in zeros))
            plant_ar=2*mp.re(Gu**2*(mp.exp(u*t)+mp.exp(-u*t)))
            plant_z=2*mp.re(F(u)**2*(mp.exp(u*t)+mp.exp(-u*t)))
            n,p=next((n,p) for n,p in aa if n>cut)
            omitted=logs[p]/mp.sqrt(n)*(C(t-mp.log(n))+C(t+mp.log(n)))
            # For n>cut, log n-t>9. Polynomial C is positive there;
            # thus one omitted prime gives a strict positive lower bound.
            for world,pa,pz in [('zeta',mp.mpf(0),mp.mpf(0)),('plant',plant_ar,plant_z)]:
                ar=H-S+pa;zero=Z+pz;budget=mp.mpf('1e-40')*(abs(H)+abs(S))
                shifted=ar-mp.mpf('1e-30')*C(t)
                row=dict(dps=dps,t=ts,world=world,H=str(H),S=str(S),arithmetic=str(ar),zero=str(zero),plant_arithmetic=str(pa),plant_zero=str(pz),gate_budget=str(budget),difference=str(ar-zero),gate=bool(abs(ar-zero)<=budget),cancellation_ratio_zero=str((abs(H)+abs(S))/abs(zero)),cancellation_ratio_truncated=str((abs(H)+abs(S))/abs(ar)),zero_tail_bound=str(ztail(t)),first_omitted_atom=n,first_omitted_atom_value=str(omitted),shift_delta=str(-mp.mpf('1e-30')*C(t)),shifted_arithmetic=str(shifted),shift_gate=bool(abs(shifted-zero)<=budget),responsible_term='positive omitted prime-power tail beyond floor(exp(t+9))',status='IDENTITY_FAILURE' if abs(ar-zero)>budget else 'PASS')
                results.append(row)
            print(json.dumps({k:results[-2][k] for k in ['dps','t','arithmetic','zero','difference','gate']}),flush=True)
            (OUT/'task_a.json').write_text(json.dumps(dict(rows=results,seconds=time.time()-start,zero_count_positive=len(zeros),mpmath=mp.__version__,python=platform.python_version(),zero_tail_convention='N(T)<=T^2 at T>=60; both signs shell bound; strip |delta|<=1/2; shells60..100 plus geometric remainder absorbed by factor1.0000000001',preregistration_commit='8e0e8da16bd0489777f3221455b854647f65b71f'),indent=2)+'\n')
if __name__=='__main__':main()
