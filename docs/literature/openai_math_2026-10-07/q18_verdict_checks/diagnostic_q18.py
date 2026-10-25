"""Finite noninterval diagnostics of literal theta identities; no zero assignments."""
from __future__ import annotations
from pathlib import Path
from math import isqrt
import json, hashlib
import mpmath as mp
mp.mp.dps=50
ROOT=Path(__file__).resolve().parent
A=mp.mpf(160)
def lam(n: int):
    if n<2:return mp.mpf(0)
    for p in range(2,isqrt(n)+1):
        if n%p==0:
            x=n
            while x%p==0:x//=p
            return mp.log(p) if x==1 else mp.mpf(0)
    return mp.log(n)
def phi(q,t):
    q=mp.mpf(q);t=mp.mpf(t);x=q*mp.exp(t)
    return mp.exp(t/2)*(4*mp.pi**2*x**4-6*mp.pi*x**2)*mp.exp(-mp.pi*x*x)
def Phi(t):
    t=abs(mp.mpf(t))
    jmax=max(3,int(mp.ceil(mp.sqrt(A/mp.pi)*mp.exp(-t)))+2)
    return mp.fsum(phi(j,t) for j in range(1,jmax+1))
def full_theta(m,t):
    return mp.fsum(lam(n)/mp.sqrt(n)*Phi(t+mp.log(n)) for n in range(2,m+1))
def original_series(m,t):
    cap=int(mp.ceil(mp.sqrt(A/mp.pi)*mp.exp(-t)))+3
    return mp.fsum(mp.fsum(lam(n) for n in range(2,min(k,m)+1) if k%n==0)*phi(k,t) for k in range(1,cap+1))
def rational_dual(m,t):
    # t is the unreflected input: the exact dual is evaluated at -t.
    total=mp.mpf(0)
    for n in range(2,m+1):
        weight=lam(n)
        if not weight:continue
        cap=int(mp.ceil(n*mp.exp(t)*mp.sqrt(A/mp.pi)))+3
        total+=weight/n*mp.fsum(phi(mp.mpf(j)/n,-t) for j in range(1,cap+1))
    return total
rows=[]
for m,tstr in [(2,'-0.7'),(5,'0.2'),(8,'0.7'),(7,'-1.1')]:
    t=mp.mpf(tstr)
    actual=full_theta(m,t);direct=original_series(m,t);dual=rational_dual(m,t)
    err=max(abs(actual-direct),abs(actual-dual))
    assert err<mp.mpf('1e-40')*max(1,abs(actual))
    rows.append({'m':m,'t':tstr,'source':mp.nstr(actual,22),'max_identity_error':mp.nstr(err,8)})
# Actual finite source is not even; do not infer anything about its compressed spectrum.
x=full_theta(2,mp.mpf('.4'));xr=full_theta(2,-mp.mpf('.4'))
assert abs(x-xr)>mp.mpf('0.01')
not_even={'m':2,'t':'0.4','Theta(t)-Theta(-t)':mp.nstr(x-xr,22)}
# Moving theta-index edge; head has exactly log(k), not an approximation to d_m.
edge=[]
for m in (32,128,512,2048):
    s=mp.mpf('0.15');t=-mp.log(m)+s
    head=mp.fsum(mp.log(k)*phi(k,t) for k in range(2,m+1))
    total=full_theta(m,t);tail=total-head
    norm=mp.sqrt(m)*mp.log(m)
    beta=2*mp.pi*mp.exp(5*s/2)*mp.exp(-mp.pi*mp.exp(2*s))
    edge.append({'m':m,'s':'0.15','head_scaled':mp.nstr(head/norm,18),'tail_scaled':mp.nstr(tail/norm,18),'total_scaled':mp.nstr(total/norm,18),'predicted_head_limit':mp.nstr(-beta,18),'predicted_tail_limit':mp.nstr(beta,18)})
# Common continuum correction at the moving edge (actual m fixed; K auxiliary).
repair=[]
m=5
A_m=mp.fsum(lam(n)/n for n in range(2,m+1))
for cut in (16,64,256):
    t=-mp.log(cut)+mp.mpf('.1')
    head=mp.fsum(mp.fsum(lam(n) for n in range(2,min(k,m)+1) if k%n==0)*phi(k,t) for k in range(1,cut+1))
    betaK=2*mp.pi*cut**3*mp.exp(5*t/2)*mp.exp(-mp.pi*cut**2*mp.exp(2*t))
    error=full_theta(m,t)-head-A_m*betaK
    repair.append({'m':m,'K':cut,'pointwise_repaired_error':mp.nstr(error,20),'sqrtK_times_error':mp.nstr(mp.sqrt(cut)*error,20)})
out={'status':'PASS_NONINTERVAL_DIAGNOSTICS_NOT_ASYMPTOTIC_PROOF','mpmath':mp.__version__,'dps':mp.mp.dps,'identity_cases':rows,'not_even_control':not_even,'moving_edge_cases':edge,'repair_cases':repair,'diagnostic_cases':len(rows)+1+len(edge)+len(repair),'hypothetical_zero_numerical_values_used':False,'full_CCM_spectrum_computed':False,'arb_runs':0,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'diagnostic_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
