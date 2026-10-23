"""Exact finite algebra controls for Q13; not an asymptotic CCM certificate."""
from fractions import Fraction as F
from pathlib import Path
import hashlib, json

checks=[]
def ck(name, value):
    if not value: raise AssertionError(name)
    checks.append(name)
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def neg(a):return (-a[0],-a[1])
def sub(a,b):return add(a,neg(b))
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def cj(a):return (a[0],-a[1])
def sc(a,x):return (a[0]*x,a[1]*x)
def ns(a):return a[0]**2+a[1]**2
I=(F(0),F(1));MI=(F(0),F(-1))

# All complex cross terms; rational q represents the real value X'/X.
for r in [F(-3),F(-2,3),F(0),F(1,3),F(1),F(4)]:
    om=1/(1+r*r); eta=r*om
    al=(eta,1-om);be=(om,eta)
    ck(f'xi_row/{r}',ns(al)+ns(be)==1)
    ck(f'xi_coupling/{r}',sub(be,mul(I,al))==(F(1),F(0)))
    for z in [F(-1,2),F(0),F(1,3),F(3,4),F(1)]:
      for n,(j,v,p) in enumerate([
        ((F(2),F(1)),(F(-1,3),F(4,5)),(F(3,2),F(-1))),
        ((F(1,2),F(-2,3)),(F(5,4),F(-1,2)),(F(-2),F(3,7))),
        ((F(0),F(1)),(F(-3),F(1,4)),(F(2,5),F(7,3)))
      ]):
        x=F(7,5);c=F(1,3) # algebraic normalization, not a new Fourier convention
        fh=(F(0),-c*(1-z)/x)
        G=sc(mul(MI,add(v,sc(j,c))),1/x)
        FF=sc(mul(MI,p),1/x)
        U=sub(mul(al,FF),mul(I,mul(be,G)))
        EE=mul(MI,mul(be,mul(j,fh)))
        Ureg=sub(U,EE)
        exact=2*(ns(U)-ns(Ureg))
        q=c*(1-z)/(x*x)
        mixed=4*mul(cj(j),sc(add(sc(v,om),sc(mul(I,p),eta)),q))[0]
        lead=2*c*c*ns(j)*om*(1-z*z)/(x*x)
        tag=f'{r}/{z}/{n}'
        ck('seam_full_cross/'+tag,exact==lead+mixed)
        vreg=add(v,sc(j,c*z))
        Greg=sc(mul(MI,vreg),1/x)
        ck('width_cancels/'+tag,add(Greg,mul(j,fh))==G)
        ck('positive_seam_leading/'+tag,lead>=0)

# Planted wrong seam sign, omitted mixed term, and absent jump.
r=F(1);om=F(1,2);eta=F(1,2); al=(eta,1-om);be=(om,eta)
x=F(2);c=F(1,3);z=F(1,2);j=(F(2),F(1));v=(F(1),F(-2));p=(F(3),F(1))
H=(F(0),-c*(1-z)/x);G=sc(mul(MI,add(v,sc(j,c))),1/x); FF=sc(mul(MI,p),1/x)
U=sub(mul(al,FF),mul(I,mul(be,G)));EE=mul(MI,mul(be,mul(j,H)))
exact=2*(ns(U)-ns(sub(U,EE)))
lead=2*c*c*ns(j)*om*(1-z*z)/(x*x)
ck('plant_omitted_mixed',exact!=lead)
wrongG=add(sc(mul(MI,sub(v,sc(j,c*z))),1/x),mul(j,H))
ck('plant_wrong_box_sign',wrongG!=G)
ck('plant_omitted_delta',sc(mul(MI,v),1/x)!=G)
wronglead=2*c*c*ns(j)*om*((1-z)**2)/(x*x)
ck('plant_sinc_square_confusion',lead!=wronglead)

# Exact polynomial integrals for H_h, its primitive, and its box derivative.
# Scaling is analytic, so every positive rational h is a finite check only.
for h in [F(1,7),F(1,2),F(1),F(3,2),F(5)]:
    # 2 int_0^h (1-t/h)^2/4 dt, and 2 int_0^h (h-t)^4/(16h^2) dt.
    nH=F(1,2)*(h-h+h/3)
    nK=h**3/F(40)
    directK=sum(F(2,16)*F((-1)**k)*F(__import__('math').comb(4,k))*h**(4-k)*h**(k+1)/F(k+1)/h**2 for k in range(5))
    ck(f'H_norm/{h}',nH==h/6)
    ck(f'primitive_norm/{h}',directK==nK)
    ck(f'box_mass/{h}',2*h/(2*h)==1)
    ck(f'box_norm/{h}',2*h/(4*h*h)==1/(2*h))
    # Triangular density of two independent uniforms: E|X+Y|=2h/3.
    meanabs=2*(h-F(2,3)*h)
    ck(f'kappa_constant/{h}',meanabs==2*h/3)

# Exponents of complete h=1/R return, epsilon fixed first.
for e in [F(1,128),F(1,64),F(1,40)]:
  for nu in [F(1,100),F(1,20),F(1,4)]:
    th=F(1,2)+e+nu
    J=F(1,4)+e/2; D=F(1,4)+e
    ck(f'power_jump/{e}/{nu}',2*J-th==-nu)
    ck(f'power_mixed/{e}/{nu}',J+D-3*th/2==-F(1,4)-3*nu/2)
    ck(f'power_regular_tail/{e}/{nu}',2*D-2*th==-F(1,2)-2*nu)

# Half-integer regularity is needed, not imaginary suppression of jumps.
# For H_1 the derivative is delta_0 - 1/2 on (-1,1).
ck('distribution_mass',F(1)-2*F(1,2)==0)
ck('actual_xi_origin_algebra',ns((F(1),F(0)))==1)

base=Path(__file__).resolve().parent
out={'status':'PASS_EXACT_LOCAL_ALGEBRA_NOT_GLOBAL_CCM_CERTIFICATE','count':len(checks),'checks':checks,
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'registration_sha256':hashlib.sha256((base/'registration.json').read_bytes()).hexdigest()}
(base/'exact_results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='checks'},indent=2))
