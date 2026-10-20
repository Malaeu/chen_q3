"""Small non-interval diagnostics only: literal mu, not CCM spectral values."""
import mpmath as mp
from pathlib import Path
import json
mp.mp.dps=45

def mu(n):
    s=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;s=-s
            if n%p==0:return 0
        p+=1
    return -s if n>1 else s

def exact_pair_integral(D,T,h,log_weight):
    out=mp.mpc(0)
    for d in range(D+1,2*D+1):
        a=mu(d)*(mp.log(mp.mpf(d)/D) if log_weight else 1)
        for e in range(D+1,2*D+1):
            b=mu(e)*(mp.log(mp.mpf(e)/D) if log_weight else 1)
            lo=max(T,d,e);hi=2*T
            if lo>=hi:continue
            if d==e:I=mp.mpf(hi-lo)
            else:
                w=2*mp.pi*h*(mp.mpf(1)/d-mp.mpf(1)/e)
                I=(mp.exp(1j*w*hi)-mp.exp(1j*w*lo))/(1j*w)
            out+=a*b*I
    assert abs(mp.im(out))<mp.mpf('1e-35')
    return mp.re(out)

rows=[]
for D,T,h,log_weight in [(4,4,1,False),(4,4,8,True),(8,8,3,False),(8,32,1,True),(12,24,20,False),(12,12,6,True)]:
    exact=exact_pair_integral(D,T,h,log_weight)
    def f(t):
        s=sum(mu(d)*(mp.log(mp.mpf(d)/D) if log_weight else 1)*mp.exp(2j*mp.pi*h*t/d)
              for d in range(D+1,2*D+1) if d<=t)
        return abs(s)**2
    cuts=sorted(set([T,2*T]+[d for d in range(D+1,2*D+1) if T<d<2*T]))
    numeric=sum(mp.quad(f,[a,b]) for a,b in zip(cuts,cuts[1:]))
    difference=abs(exact-numeric)
    bound=T*D+3*D**3*(1+mp.log(D))/h
    assert difference<mp.mpf('1e-30')
    assert exact<=bound
    rows.append({'D':D,'T':T,'h':h,'log_weight':log_weight,
                 'integral':mp.nstr(exact,22),'analytic_minus_quad_abs':mp.nstr(difference,5),
                 'proved_bound':mp.nstr(bound,22)})
out={'status':'PASS_DIAGNOSTIC_NOT_INTERVAL','cases':len(rows),'precision_decimal':45,'rows':rows}
Path(__file__).with_name('reciprocal_diagnostics.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
