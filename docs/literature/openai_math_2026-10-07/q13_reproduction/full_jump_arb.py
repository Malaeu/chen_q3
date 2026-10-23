from flint import arb, acb, ctx
import flint,json
from pathlib import Path
ctx.dps=80
L=arb(16).log(); T=L/2; w=2*arb.pi()/L; w2=w*w
cA=arb.const_euler()+(8*arb.pi()).log()+arb.pi()/2
B=arb(1)/2+8*w2; C=2+20*w2; psi0=-2-8*w2
psi_l2=4*w2-arb(1)/2
def psi(s):
 z=1-(w*s).cos(); return psi0+C*z-B*z*z
jpr=2*((arb(2).log()/arb(2).sqrt())*psi_l2+(arb(3).log()/arb(3).sqrt())*psi(arb(3).log()))
d=arb(1)/10000
assert C-B*w2*d*d/2>0
def h(x, analytic):
 z=1-(w*x).cos(); return (x/2).exp()*(C*z-B*z*z)/x.sinh()
Ihi=acb.integral(h,acb(d),acb(T),rel_tol=arb(2)**(-180),abs_tol=arb(2)**(-180),eval_limit=100000).real
Ilo=(d/2).exp()*w2*d*d/4*(C+B*w2*d*d/2)
AT=(arb(1)/2).atanh()+(arb(1)/2).atan()
j=cA*psi0+Ihi+arb(0,Ilo.upper())-2*psi0*AT+jpr
assert j>arb('0.23225') and j<arb('0.23226')
out={'flint':flint.__version__,'dps':ctx.dps,'m':16,'M':2,'normalized':False,'prime_jump':str(jpr),'full_jump':str(j),'lower':str(j.lower()),'upper':str(j.upper()),'small_integral_absolute_bound':str(Ilo.upper()),'status':'PASS_FINITE_INTERVAL_NOT_ASYMPTOTIC'}
Path(__file__).with_name('result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
