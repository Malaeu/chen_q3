#!/usr/bin/env python3
"""Independent small-carrier spatial controls, no eigensolver or zero search."""
from pathlib import Path
import sys,json
import mpmath as mp
sys.argv=[sys.argv[0],str(Path(__file__).resolve().parent.parent/'inputs')]
import rellich as r
mp.mp.dps=80
m=4;L=mp.log(m);b=L/2
f=mp.matrix([mp.mpf(2)/3,-mp.mpf(1)/5,mp.mpf(1)/7,0,mp.mpf(1)/11]);f/=mp.norm(f)
D,Da,eb=r.generators(m)
def fn(x):
    return mp.fsum(f[n]*(1 if n==0 else mp.sqrt(2))*(-1)**n*mp.cos(2*mp.pi*n*x/L)/mp.sqrt(L) for n in range(m+1))
def fp(x):
    return mp.fsum(-f[n]*mp.sqrt(2)*(-1)**n*(2*mp.pi*n/L)*mp.sin(2*mp.pi*n*x/L)/mp.sqrt(L) for n in range(1,m+1))
def gg(x):return x*fp(x)+fn(x)/2
def ei(n,x):return (1 if n==0 else mp.sqrt(2))*(-1)**n*mp.cos(2*mp.pi*n*x/L)/mp.sqrt(L)
projection=max(abs(mp.quad(lambda x:ei(n,x)*gg(x),[-b,0,b])-(D*f)[n]) for n in range(m+1))
fourier=[]
for z in [mp.mpf('2.3'),mp.mpc('2.3','.27'),mp.j/2]:
    F,Fp=r.eval_fourier(list(f),z,L)
    H=L*mp.fdot(eb,f)*mp.cos(b*z)-F/2-z*Fp
    direct=mp.quad(lambda x:gg(x)*mp.exp(mp.j*z*x),[-b,0,b])
    fourier.append(abs(H-direct))
mixed=[]
for s in [L/7,L/2,6*L/7]:
    direct=mp.quad(lambda x:fn(x)*gg(x+s)+gg(x)*fn(x+s),[-b,( -s)/2,b-s])
    qp=2*mp.quad(lambda x:fn(x)*fp(x+s),[-b,-s/2,b-s])-2*fn(b-s)*fn(b)
    formula=L*fn(b)*fn(b-s)+s*qp/2
    mixed.append(abs(direct-formula))
def aprime(x):return 1-3*x*x/(b*b)
def av(x):return x*(1-x*x/(b*b))
alt=max(abs(mp.quad(lambda x:ei(n,x)*(av(x)*fp(x)+aprime(x)*fn(x)/2),[-b,0,b])-(Da*f)[n]) for n in range(m+1))
res={'status':'PASS','scope':'Independent finite spatial normalization controls only',
     'dps':mp.mp.dps,'D_projection_error':mp.nstr(projection,30),
     'Fourier_weak_identity_errors':[mp.nstr(x,30) for x in fourier],
     'mixed_correlation_errors':[mp.nstr(x,30) for x in mixed],
     'alternative_projection_error':mp.nstr(alt,30),
     'green_matrix_error':mp.nstr(mp.norm(D+D.T-L*eb*eb.T),30),
     'alternative_skew_error':mp.nstr(mp.norm(Da+Da.T),30),'new_eigenproblems':0}
assert max([projection,alt]+fourier+mixed)<mp.mpf('1e-70')
print(json.dumps(res,indent=2))
