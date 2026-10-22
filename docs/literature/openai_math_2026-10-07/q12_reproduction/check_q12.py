from fractions import Fraction as F
from math import comb
from pathlib import Path
import json, hashlib
import sympy as s

checks=[]
def check(name, condition):
    if not bool(condition): raise AssertionError(name)
    checks.append(name)

# Rank-one identity and the full complex cross term: exact rational arithmetic.
def mul(z,w): return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def add(z,w): return (z[0]+w[0],z[1]+w[1])
def conj(z): return(z[0],-z[1])
def norm2(z): return z[0]*z[0]+z[1]*z[1]
I=(F(0),F(1)); mi=(F(0),F(-1))
for h in [F(-3),F(-2,3),F(0),F(1,3),F(1),F(4)]:
    w=1/(1+h*h); eta=h*w
    alpha=(eta,1-w); beta=(w,eta)
    check(f'unit_row/{h}',norm2(alpha)+norm2(beta)==1)
    check(f'determinant/{h}',w*(1-w)==eta*eta)
    for v in [(F(1),F(0)),(F(1,2),F(-2,3)),(F(0),F(1))]:
      for g in [(F(0),F(1)),(F(2,3),F(1,5)),(F(-1),F(0))]:
        z=add(mul(alpha,v),mul(mi,mul(beta,g)))
        zc=add(mul(conj(beta),v),mul(I,mul(conj(alpha),g)))
        # Direct expression for i eta(v bar(g)-g bar(v)).
        q=(1-w)*norm2(v)+w*norm2(g)-2*eta*mul(v,conj(g))[1]
        check(f'full_mixed/{h}/{v}/{g}',norm2(z)==q)
        check(f'complement/{h}/{v}/{g}',norm2(z)+norm2(zc)==norm2(v)+norm2(g))

alpha=beta=(F(1,2),F(1,2)); v=(F(1),F(0));g=(F(0),F(1))
z=add(mul(alpha,v),mul(mi,mul(beta,g)))
diagonal=F(1,2)*(norm2(v)+norm2(g))
wrong_sign=diagonal+mul(v,conj(g))[1]
check('planted_eta_omission',norm2(z)!=diagonal)
check('planted_eta_wrong_sign',norm2(z)!=wrong_sign)

# Both supplied transform defects, treated as algebra, not assumed zero.
a,b,Op,Oq,J,p,q=s.symbols('a b Op Oq J p q')
rp=Op-1/(1-a);rq=Oq-1/(1-b);hpq=J+Op-Oq
Npp=(2+(a*b-1)*(Op+Oq)+(b-a)*J)/(p*q*(p+q))
App=-(a+b)/(p*q*(p+q))
Dpp=((a-1)*(b+1)*rp+(b-1)*(a+1)*rq+(b-a)*hpq)/(p*q*(p+q))
Npm=((1+a*b)*(Op-Oq)+(a+b)*J)/(p*q*(q-p))
Apm=(a-b)/(p*q*(q-p))
Dpm=((1-a)*(1-b)*(rp-rq)+(a+b)*hpq)/(p*q*(q-p))
check('Lpp_full_subtraction',s.factor(Npp-App-Dpp)==0)
check('Lpm_full_subtraction',s.factor(Npm-Apm-Dpm)==0)
check('Lpp_diagonal',s.factor((Npp-App-Dpp).subs({b:a,Oq:Op,J:0,q:p}))==0)
ap,op,jp=s.symbols('aprime Oprime Jprime')
rprime=op-ap/(1-a)**2
limit_from_defect=(-(1-a)**2*rprime+2*a*(jp-op))/p**2
limit_from_subtraction=(ap-(1+a*a)*op+2*a*jp)/p**2
check('Lpm_diagonal_limit',s.factor(limit_from_defect-limit_from_subtraction)==0)
check('real_zero_multiplier_limit',norm2((F(0),F(1)))+norm2((F(0),F(0)))==1)


# A consistent even polynomial plant, zeros at +/- i sqrt(33)/16.
b0=F(1,16); c0=F(33,16); A=b0*c0
omega=lambda p: 1-4*p/((b0+c0)*(p+b0)*(p+c0))
kappa=lambda p: 2*p/(A-p*p)
jfun=lambda p,q: F(2)/(b0+c0)*(b0*(1/(b0+p)-1/(b0+q))+c0*(1/(c0+p)-1/(c0+q)))
plant=[]
for pv in [F(3,4),F(1),F(3,2),F(2),F(3)]:
    r=omega(pv)-1/(1-kappa(pv))
    check(f'nonpoisson_actual_plant/{pv}',r!=0)
    for qv in [F(5,4),F(5,2)]:
        hv=jfun(pv,qv)+omega(pv)-omega(qv)
        check(f'dispersion_actual_plant/{pv}/{qv}',hv!=0)
        av,bv=kappa(pv),kappa(qv)
        npp=(2+(av*bv-1)*(omega(pv)+omega(qv))+(bv-av)*jfun(pv,qv))/(pv*qv*(pv+qv))
        app=-(av+bv)/(pv*qv*(pv+qv))
        check(f'nonzero_defect_plant/{pv}/{qv}',npp!=app)
    plant.append({'p':str(pv),'r_p':str(r)})
# Exact factorizations used for rational integrals.
x=s.symbols('x',real=True)
check('plant_denominator_factor',s.expand((x*x+s.Rational(33,256))**2+4*x*x-(x*x+s.Rational(1,256))*(x*x+s.Rational(1089,256)))==0)
# Real-zero calibration X(z)=z, kappa=-1/p, Omega=p/(p+1).
for pv in [F(1),F(3,2),F(2),F(4)]:
    for qv in [F(5,4),F(3),F(5)]:
        av=-1/pv; bv=-1/qv; op=pv/(pv+1);oq=qv/(qv+1);jv=1/(pv+1)-1/(qv+1)
        check(f'real_zero_r/{pv}/{qv}',op-1/(1-av)==0)
        check(f'real_zero_h/{pv}/{qv}',jv+op-oq==0)
        check(f'real_zero_pp/{pv}/{qv}',(2+(av*bv-1)*(op+oq)+(bv-av)*jv)/(pv*qv*(pv+qv))==-(av+bv)/(pv*qv*(pv+qv)))
        check(f'real_zero_pm/{pv}/{qv}',((1+av*bv)*(op-oq)+(av+bv)*jv)/(pv*qv*(qv-pv))==(av-bv)/(pv*qv*(qv-pv)))

# Positive/negative pole quadrant algebra with exact moment constraints.
# A+/A- are split at an arbitrary r. Set total exponential moments to zero.
r,ap,bp,am,bm=s.symbols('r ap bp am bm', real=True)
# ap,bp: e^(u/2) integrals below/above r; am,bm: e^(-u/2).
C=s.exp(-r/2)*ap-s.exp(r/2)*bm
Cp=-s.exp(-r/2)*bp-s.exp(r/2)*bm
Cm=s.exp(r/2)*am+s.exp(-r/2)*ap
check('pole_positive_contact',s.simplify(Cp.subs(bp,-ap)-C)==0)
check('pole_negative_contact',s.simplify(Cm.subs(am,-bm)-C)==0)
y=s.symbols('y', real=True)
check('pole_fourier_norm_square',s.expand(4*(y*y+s.Rational(1,4))**2-4*y*y-4*(y*y-s.Rational(1,4))**2)==0)

# Arch logarithmic cancellation and exact derivative of Lerch partial terms.
t=s.symbols('t',positive=True)
for n in range(12):
    v=-s.exp(-(2*n+s.Rational(1,2))*t)/(2*n+s.Rational(1,2))
    check(f'arch_term_derivative/{n}',s.simplify(s.diff(v,t)-s.exp(-(2*n+s.Rational(1,2))*t))==0)

# Full arithmetic log coefficients: Lambda = mu * log, with formal prime logs.
def factor(n):
    ans={};d=2
    while d*d<=n:
        while n%d==0:ans[d]=ans.get(d,0)+1;n//=d
        d+=1
    if n>1:ans[n]=ans.get(n,0)+1
    return ans

def mu(n):
    f=factor(n)
    return 0 if any(a>1 for a in f.values()) else (-1)**len(f)
for n in range(1,181):
    out={}
    for d in range(1,n+1):
      if n%d==0:
        for prime,power in factor(n//d).items():out[prime]=out.get(prime,0)+mu(d)*power
    out={p:a for p,a in out.items() if a}
    f=factor(n);target={next(iter(f)):1} if len(f)==1 else {}
    check(f'actual_mobius_prime_power/{n}',out==target)
# Two halves of outward shifts do not create a factor sqrt(2) in their norm.
for N in range(2,10):
    for shift in range(0,N+1):
        vec=[F((i*7)%11-5,7) for i in range(2*N)]
        old=sum(v*v for v in vec)
        new=sum(v*v for v in vec[:N-shift])+sum(v*v for v in vec[N+shift:])
        check(f'outward_contractivity/{N}/{shift}',new<=old)

# Finite full budget arithmetic; no proof of the target is asserted here.
w,Cc,ca=s.symbols('w Cc ca',nonnegative=True)
E=2*(1+(6*w+Cc)**2)+12*w*w+ca
check('full_defect_fee_expand',s.expand(E-(84*w*w+24*w*Cc+2*Cc*Cc+ca+2))==0)

base=Path(__file__).resolve().parent
out={'status':'PASS_EXACT_LOCAL_ALGEBRA_NOT_CCM_CERTIFICATION','count':len(checks),
     'plant_values':plant,'checks':checks,
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'registration_sha256':hashlib.sha256((base/'registration.json').read_bytes()).hexdigest()}
(base/'exact_results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2))
print(json.dumps({k:v for k,v in out.items() if k!='checks'},indent=2))
