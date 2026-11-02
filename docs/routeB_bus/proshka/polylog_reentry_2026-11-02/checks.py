from __future__ import annotations
import json, math
from pathlib import Path
import mpmath as mp
import sympy as sp

mp.mp.dps = 60
out = {}
x, eta, tt, nu = sp.symbols('x eta tt nu', real=True, positive=True)
# Phase locking makes cos(t*z0) real; the complete quartet coefficient is four.
a = 2*sp.I*sp.cosh(eta*tt)
assert sp.simplify(4*nu*sp.re(a*a)+16*nu*sp.cosh(eta*tt)**2) == 0
out['P1_exact_quartet'] = 'PASS'
# A concrete two-contact polynomial; no approximate zeros are used.
u0 = (1+sp.cos(x))**2
f0 = sp.diff(u0,x,2)-u0/4
assert sp.simplify(f0.subs(x,sp.pi)) == 0
for sign in (-1,1):
    F = sp.exp(sign*x/2)*(sp.diff(u0,x)-sign*u0/2)
    assert sp.simplify(sp.diff(F,x)-sp.exp(sign*x/2)*f0)==0
    assert sp.simplify(F.subs(x,sp.pi)-F.subs(x,-sp.pi))==0
out['P2_exact_endpoint_and_pole_contacts']='PASS'
ratios=[]
for L in (16,20,32,64):
    M=math.ceil(8*L*L)
    v=[mp.mpf(1)/4+(2*mp.pi*n/L)**2 for n in range(M+1)]
    S1=1/v[0]+2*mp.fsum(1/z for z in v[1:])
    S2=1/v[0]**2+2*mp.fsum(1/z**2 for z in v[1:])
    corr=S1/mp.sqrt((2*M+1)*S2)
    assert corr<mp.mpf('0.5')
    ratios.append(str(corr))
out['P2_gram_correlations_60dps']=ratios
# Diagnostics only; the uniform multiplier theorem is proved in the Markdown.
maxratio=mp.mpf(0); count=0
for N in (1,2,3,7,16,31,64,128,257):
    for t in (0,mp.mpf('0.01'),mp.mpf('0.5'),1,2,7,16,40,128,1000):
        z=mp.fsum(mp.power(k,-mp.mpf('0.5')+1j*t) for k in range(1,N+1))
        c=mp.power(N,mp.mpf('0.5')+1j*t)/(mp.mpf('0.5')+1j*t)
        ratio=abs(z-c)/(8*mp.sqrt(1+abs(t)))
        maxratio=max(maxratio,ratio); count+=1
        assert ratio<1
out['P3_multiplier']={'cases':count,'max_ratio_to_bound':str(maxratio),'status':'PASS_DIAGNOSTIC'}
# Complete output-space check for an even two-contact test.
L=mp.log(16); b=L/2; w=2*mp.pi/L
coef=[-mp.mpf(3)/8, -2*w*w-mp.mpf(1)/2, -2*w*w-mp.mpf(1)/8]
norm2=L*coef[0]**2+L/2*(coef[1]**2+coef[2]**2)
coef=[c/mp.sqrt(norm2) for c in coef]
def f(y):
    if y < -b or y>b: return mp.mpf(0)
    return mp.fsum(coef[k]*mp.cos(k*w*y) for k in range(3))
def antideriv(y):
    return mp.exp(y/2)*mp.fsum(coef[k]*(mp.cos(k*w*y)/2+k*w*mp.sin(k*w*y))/(mp.mpf(1)/4+(k*w)**2) for k in range(3))
assert abs(antideriv(b)-antideriv(-b))<mp.mpf('1e-50')
def C(s):
    s=abs(s)
    if s>=L: return mp.mpf(0)
    cs={0:coef[0],1:coef[1]/2,-1:coef[1]/2,2:coef[2]/2,-2:coef[2]/2}
    ans=mp.mpc(0)
    for j,cj in cs.items():
        for k,ck in cs.items():
            d=j+k
            integ=L-s if d==0 else (mp.exp(1j*d*w*(b-s))-mp.exp(-1j*d*w*b))/(1j*d*w)
            ans+=cj*ck*mp.exp(1j*k*w*s)*integ
    return ans.real
rows=[]
for N in (1,2,5):
    def zz(y): return mp.fsum(f(y+mp.log(k))/mp.sqrt(k) for k in range(1,N+1))
    def cc(y):
        top=y+mp.log(N)
        if top<=-b or top>=b: return mp.mpf(0) # exact zero total exp-moment
        return mp.exp(-y/2)*(antideriv(top)-antideriv(-b))
    breaks=sorted(set([-b-mp.log(k) for k in range(1,N+1)]+[b-mp.log(k) for k in range(1,N+1)]))
    direct=mp.fsum(mp.quad(lambda y: (zz(y)-cc(y))**2,[u,v]) for u,v in zip(breaks[:-1],breaks[1:]))
    raw=mp.fsum(C(mp.log(mp.mpf(a)/d))/mp.sqrt(a*d) for a in range(1,N+1) for d in range(1,N+1))
    cuts=sorted(set([mp.mpf(0),L]+[mp.log(mp.mpf(N)/k) for k in range(1,N+1) if 0<mp.log(mp.mpf(N)/k)<L]))
    compensation=mp.mpf(0)
    for lo,hi in zip(cuts[:-1],cuts[1:]):
        mult=mp.floor(N*mp.exp(-(lo+hi)/2))
        compensation+=mult*mp.quad(lambda s: mp.exp(s/2)*2*C(s),[lo,hi])
    err=abs(direct-(raw-compensation))
    assert err<mp.mpf('1e-45')
    assert direct>=0 and direct<=64*(1+2*w)
    rows.append({'N':N,'complete_output_norm_squared':str(direct),'identity_absolute_error':str(err)})
out['P5_complete_output_floor_identity']=rows
# A positive O(log^2) auxiliary term cannot certify the missing sign.
m=sp.symbols('m',positive=True)
A=sp.diag(-m,0); B=sp.zeros(2)
assert B==sp.zeros(2) and A[0,0]<0
out['P6_abstract_wrong_inference_control']='PASS_NOT_A_LITERAL_CCM_COUNTEREXAMPLE'
out['RH_PROVED']=False; out['INTERVAL_ARITHMETIC']=False; out['LEAN_EXECUTED']=False
Path(__file__).with_name('results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out,ensure_ascii=False,indent=2))
