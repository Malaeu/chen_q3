# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Independent coverage and direct-square head checks; no interval claims."""
import csv, gzip, hashlib, json, math, time
from pathlib import Path
import numpy as np
HERE=Path(__file__).resolve().parent
MAX=10_000_000

def progress(i,total,start,label):
    f=i/total; t=time.monotonic()-start; k=int(30*f)
    print(f"[{'#'*k}{'.'*(30-k)}] {100*f:.1f}% ETA {t*(1-f)/max(f,1e-20):.1f}s {label}",flush=True)

def main():
    start=time.monotonic(); selected={10,100,1000,10000,100000,1000000,10000000}
    samples={}; count=0; next_n=3; minhead=math.inf
    chunks=sorted(HERE.glob('core_scan_*.csv.gz'))
    assert chunks
    for i,p in enumerate(chunks):
        with gzip.open(p,'rt') as f:
            for r in csv.DictReader(f):
                n=int(r['N']); assert n==next_n,(p,n,next_n)
                h=float(r['head_approx_long_double']); b=float(r['b_approx_long_double'])
                assert math.isfinite(h) and math.isfinite(b) and h>=0
                if n in selected:samples[n]=h
                minhead=min(minhead,h);count+=1;next_n+=1
        progress(i+1,len(chunks),start,'scan coverage and gzip CRC')
    assert next_n==MAX+1 and count==MAX-2 and set(samples)==selected
    expected=[]; previous=None; signrows=0
    signfiles=list(HERE.glob('core_signs_*.csv.gz'));assert len(signfiles)==1
    with gzip.open(signfiles[0],'rt') as f:
        for r in csv.DictReader(f):
            n=int(r['N']);assert n==signrows+3
            sign=int(r['b_sign_certified']);assert sign in (-1,1)
            if previous is not None and previous!=sign:expected.append(n-1)
            previous=sign;signrows+=1
    assert signrows==MAX-1
    with (HERE/'core_crossings.csv').open() as f:actual=[int(r['N']) for r in csv.DictReader(f)]
    assert expected==actual
    with (HERE/'core_full_H.csv').open() as f:full=list(csv.DictReader(f))
    fullns={int(r['N']) for r in full}; assert set(n for n in actual if n<=10000)<=fullns
    for r in full:
        n=int(r['N']);k=math.isqrt(n**3);k+=k*k<n**3
        assert int(r['K'])==k
        assert abs(float(r['head'])+float(r['shoulder'])-float(r['full_H']))<1e-12
    # Independent Eratosthenes arithmetic, then direct positive sum rather than
    # cancellation-prone A-2xB+x²C used by the production prefix scanner.
    prime=np.ones(MAX+1,dtype=bool);prime[:2]=False
    for p in range(2,math.isqrt(MAX)+1):
        if prime[p]:prime[p*p::p]=False
    mu=np.ones(MAX+1,dtype=np.int8);mu[0]=0;psi=np.zeros(MAX+1)
    primes=np.flatnonzero(prime)
    for p0 in primes:
        p=int(p0);mu[p::p]*=-1
        if p*p<=MAX:mu[p*p::p*p]=0
        q=p
        while q<=MAX:
            psi[q]=math.log(p)
            if q>MAX//p:break
            q*=p
    np.cumsum(psi,out=psi)
    checks=[]
    for j,n in enumerate(sorted(selected)):
        k=np.arange(1,n+1,dtype=np.float64);L=math.log(n)
        a=mu[1:n+1]*np.log(n/k)/L
        s=float(np.sum(a/k));rr=psi[1:n+1]-k*L*s
        direct=float(np.sum(rr*rr/(k*(k+1)))/(L*L))
        delta=abs(direct-samples[n]);assert delta<=1e-8,(n,direct,samples[n],delta)
        checks.append(dict(N=n,direct_positive_head=direct,production_head=samples[n],absolute_difference=delta,tolerance=1e-8))
        progress(j+1,len(selected),start,'independent direct-square head')
    out=dict(status='PASS',head_rows=count,sign_rows=signrows,crossings=len(actual),full_core_rows=len(full),all_requested_crossings_through_10000_present=True,min_stored_head=minhead,direct_head_checks=checks,arithmetic_scope='Independent float64 diagnostic check; certified signs are supplied by the MPFR production pass, not inferred here.',seconds=time.monotonic()-start)
    (HERE/'OUTPUT_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2),flush=True)
if __name__=='__main__':main()
