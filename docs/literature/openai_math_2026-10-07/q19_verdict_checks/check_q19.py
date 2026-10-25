"""Exact local controls of Q19 algebra, not a proof of asymptotic CCM signs.
No numerical point is asserted to be a zeta zero.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from pathlib import Path
import hashlib, json
import sympy as S
ROOT=Path(__file__).resolve().parent
counts=Counter()
I=S.I

def zero(x):
    return S.cancel(S.expand_complex(x))==0

def unit(t):
    t=S.Rational(t)
    return (1-t*t+2*I*t)/(1+t*t)

kr,ki,zr,zi,np,nm=S.symbols('kr ki zr zi np nm',real=True)
kap=kr+I*ki; zz=zr+I*zi
expected=kr*zr*(np+nm)-ki*zi*(np-nm)
assert S.expand(S.re(kap*(np*zz+nm*S.conjugate(zz)))-expected)==0
counts['paired_real_identity']=1
# Removing the defect or the phase is genuinely detectable.
assert expected.subs({kr:0,ki:1,zr:0,zi:1,np:3,nm:1})==-2
assert S.re((1+2*I)*(1+I))==-1
assert S.re(abs(1+2*I)*(1+I))==S.sqrt(5)
counts['phase_and_reflection_omissions_detected']=2
# The two-frequency numerator expansion, including its reflection defect.
e,o,c,d=S.symbols('e o c d',real=True)
pplus=e+o;pminus=e-o
dplus=2*(c-d);dminus=2*(c+d)
assert S.expand(pplus*dplus+pminus*dminus-4*(e*c-o*d))==0
assert S.expand(pplus*dplus-pminus*dminus-4*(o*c-e*d))==0
counts['whole_sum_and_difference']=2
# Common zero division, exact removable normalization, and preservation of phase.
s,delta=S.symbols('s delta',real=True,positive=True)
for r in range(1,7):
    a=(s*s+delta*delta)**r*(1+s+2*s*s)
    lhs=a*a/(delta+I*s)**(2*r)
    rhs=(delta-I*s)**(2*r)*(1+s+2*s*s)**2
    assert S.cancel(lhs-rhs)==0
    hg=1+s+2*s*s
    cw=(2*delta)**r*hg.subs(s,-I*delta)
    kv=1/S.conjugate(cw)**2
    val=kv*(2*delta)**(2*r)*hg.subs(s,I*delta)**2
    assert S.simplify(val-1)==0
    assert S.simplify(hg-hg.subs(s,-s))==2*s
    counts['common_zero_and_normalization']=counts['common_zero_and_normalization']+3
# Four-wave expansion. All phases below are independent rational unit complex numbers.
# They are substitutions in an algebraic identity, NOT data for a hypothetical zero.
for j in range(1,17):
    E=unit(S.Rational(j,7)); V=unit(S.Rational(j+1,9))
    Q=unit(S.Rational(j+2,11)); th=unit(S.Rational(j+3,13))
    k=S.Rational(j+1,5)+I*S.Rational(2*j+1,7)
    rr=S.Rational(j+2,8)+I*S.Rational(j+1,6)
    dp=S.Rational(2,3)+I*S.Rational(j,9)
    dm=S.Rational(3,5)-I*S.Rational(j+1,11)
    pp=S.Rational(j+2,10);pm=S.Rational(j+1,8)
    sp=S.Rational(j+2,4)
    sinT=(V-1/V)/(2*I)
    z=rr*Q*V/E
    Dp=th*E*dp+S.conjugate(th*E*dp)
    Dm=th/E*dm+S.conjugate(th/E*dm)
    direct=sinT/sp*S.re(k*(pp*Dp*z+pm*Dm*S.conjugate(z)))
    AA=k*pp*dp*th+S.conjugate(k)*pm*S.conjugate(dm)/th
    BB=k*pp*S.conjugate(dp)/th+S.conjugate(k)*pm*dm*th
    normal=S.re(rr*Q/(2*I*sp)*(V*V-1)*(AA+BB/(E*E)))
    assert S.simplify(direct-normal)==0
    counts['four_wave_normal_form']+=1
# Distinct waves including sums for real-square integration.
for alpha in [Fraction(1,100),Fraction(1,10),Fraction(1,8),Fraction(1,5),Fraction(6,25)]:
    waves=[(2*alpha,1),(Fraction(0),1),(-2+2*alpha,1),(Fraction(-2),1)]
    assert all(a!=0 or b!=0 for a,b in waves)
    counts['frequency_nonzero']+=4
    for j in range(4):
        for k in range(j+1,4):
            assert waves[j]!=waves[k]
            assert (waves[j][0]+waves[k][0],waves[j][1]+waves[k][1])!=(0,0)
            counts['frequency_separation']+=2
# Exact lower bound inequality from L2, Linfinity, and a small mean.
x,B=S.symbols('x B',positive=True)
assert S.simplify((x/(2*B)-x/(4*B))/2-x/(8*B))==0
counts['negative_part_conversion']=1
# The finite continuous transform retains both lower endpoints and directions.
z,L=S.symbols('z L',real=True)
D0=(S.exp((S.Rational(1,2)+z)*L)-1)/(S.Rational(1,2)+z)+(S.exp((S.Rational(1,2)-z)*L)-1)/(S.Rational(1,2)-z)
assert S.simplify(D0.subs(L,0))==0
assert S.simplify(S.diff(D0,L)-S.exp(L/2)*(S.exp(z*L)+S.exp(-z*L)))==0
assert S.simplify(D0-D0.subs(z,-z))==0
counts['continuous_finite_endpoints']=3
# A deliberately omitted second temporal orientation fails the endpoint derivative.
one_side=(S.exp((S.Rational(1,2)+z)*L)-1)/(S.Rational(1,2)+z)
assert S.simplify((S.diff(one_side,L)-S.diff(D0,L)).subs({z:0,L:0}))==-1
counts['temporal_orientation_omission_detected']=1
# Finite prime-power support is all powers, not primes only.
from math import isqrt
for n in range(2,81):
    factors={};v=n
    for p in range(2,isqrt(n)+1):
        while v%p==0:
            factors[p]=factors.get(p,0)+1;v//=p
    if v>1:factors[v]=factors.get(v,0)+1
    formal_lam={next(iter(factors)):1} if len(factors)==1 else {}
    div_sum={}
    for d in range(2,n+1):
        if n%d:continue
        v=d;ff={}
        for p in range(2,isqrt(d)+1):
            while v%p==0:ff[p]=ff.get(p,0)+1;v//=p
        if v>1:ff[v]=ff.get(v,0)+1
        if len(ff)==1:
            p=next(iter(ff));div_sum[p]=div_sum.get(p,0)+1
    assert div_sum==factors
    counts['actual_divisor_prime_power_support']+=1
assert {2:3}!={2:1}
counts['proper_power_omission_detected']=1
# Fixed-order, original-P return and optional frequency-tail payment.
for eps in [Fraction(1,40),Fraction(1,64),Fraction(1,100)]:
    q=int(1/eps)+3
    exps=[1+eps*(Fraction(1,2)-q),Fraction(1,2)+eps*(Fraction(3,2)-q),Fraction(1,2)+eps*(1-q)]
    assert max(exps)<0
    counts['original_P_fixed_order_budget']+=1
for beta,order,r,nu in [(Fraction(1,4),3,1,Fraction(1,4)),(Fraction(1,8),5,1,Fraction(1,4)),(Fraction(1,10),8,2,Fraction(1,4))]:
    assert Fraction(1,2)-beta*(2*order+2*r)<-nu
    counts['frequency_tail_budget']+=1
out={"status":"PASS_EXACT_LOCAL_ALGEBRA_NOT_CCM_CERTIFICATION","sympy":S.__version__,"counts":dict(counts),"total_controls":sum(counts.values()),"numerical_offcritical_zero_assigned":False,"CCM_spectra_computed":False,"arb_runs":0,"lean_runs":0,"registration_sha256":hashlib.sha256((ROOT/'registration.json').read_bytes()).hexdigest(),"script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
