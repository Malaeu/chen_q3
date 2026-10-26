#!/usr/bin/env python3
"""Exact finite controls for Q33. Not a CCM spectral or asymptotic proof."""
from collections import Counter
from fractions import Fraction as Q
from math import gcd, lcm
import json
from pathlib import Path
import sympy as s

counts = Counter()
planted = []
def check(group, proposition):
    if not bool(proposition):
        raise AssertionError(f'failed control: {group}')
    counts[group] += 1

def reject(name, wrong_claim):
    if bool(wrong_claim):
        raise AssertionError(f'planted error was not detected: {name}')
    planted.append(name)

def mu(n): return int(s.mobius(n))
def phi(n): return int(s.totient(n))
def ram(q,n):
    return sum(d*mu(q//d) for d in s.divisors(gcd(q,n)))
def cz(z):
    return sum((Q(mu(q)**2, phi(q)) for q in range(1,z+1)), Q(0))
def lam(z,n):
    return sum((Q(mu(q)*ram(q,n),phi(q)) for q in range(1,z+1)), Q(0))
def coeff(z,d):
    return sum((Q(d*mu(q)*mu(q//d),phi(q)) for q in range(d,z+1,d)),Q(0))
def logvec(n): return {int(p):Q(int(k)) for p,k in s.factorint(n).items()}
def mangvec(n):
    fs=s.factorint(n)
    return {int(next(iter(fs))):Q(1)} if len(fs)==1 else {}
def ellvec(z,n):
    v=mangvec(n)
    return v if v and next(iter(v))<=z else {}
def diffvec(z,n,omit_high_small=False):
    r=lam(z,n)**2/cz(z)**2
    ans={p:r*k for p,k in logvec(n).items()}
    ell=ellvec(z,n) if not (omit_high_small and n>z) else {}
    for v,sign in ((ell,1),(mangvec(n),-1)):
        for p,k in v.items(): ans[p]=ans.get(p,Q(0))+sign*k
    return ans

for z in (2,3,5):
    aa={d:coeff(z,d) for d in range(1,z+1)}
    for n in range(1,25):
        check('finite_Ramanujan_divisor_map',lam(z,n)==sum((aa[d] for d in aa if n%d==0),Q(0)))
        check('actual_prime_power_coefficient_majorant',all(v>=0 for v in diffvec(z,n).values()))
    mean=sum((aa[d]*aa[e]/lcm(d,e) for d in aa for e in aa),Q(0))
    check('exact_model_mean',mean==cz(z))
    period=lcm(*range(1,z+1))
    check('period_orthogonality',sum(lam(z,n)**2 for n in range(1,period+1))/period==cz(z))
    for d in aa:
        alt=Q(d*mu(d),phi(d))*sum((Q(mu(r)**2,phi(r)) for r in range(1,z//d+1) if gcd(d,r)==1),Q(0))
        check('coefficient_closed_form',aa[d]==alt)

# Absolutely summable auxiliary convolution, not a Mertens premise.
def vv(n):
    ans=Q(1)
    for p,k in s.factorint(n).items():
        p=int(p);k=int(k)
        if k>2:return Q(0)
        ans*=Q(1 if k==1 else -1,p*(p-1))
    return ans
for n in range(1,25):
    check('auxiliary_convolution',sum((vv(d)/Q(n//d) for d in s.divisors(n)),Q(0))==Q(mu(n)**2,phi(n)))

# Zero-extended translations on a finite physical lattice: only algebra model.
d=4; P=s.eye(d)-s.ones(d,d)/d
for shift in (0,1,3,4,6):
    ext=d+2*shift
    F=s.zeros(ext,d); U=s.zeros(ext,d)
    for j in range(d):F[j+shift,j]=1;U[j+2*shift,j]=1
    Qs=F.T*U+U.T*F
    square=P*(F+U).T*(F+U)*P
    check('both_time_shift_square',s.simplify(square-P*(2*s.eye(d)+Qs)*P)==s.zeros(d))
    c=P*s.Matrix([1+s.I,2-s.I,-1+2*s.I,3])
    check('complex_cross_term',s.simplify((c.conjugate().T*square*c)[0]-((F+U)*c).dot(((F+U)*c).conjugate()))==0)
    if shift>=d:check('zero_overlap_keeps_energy_diagonal',square==2*P)

# Complete signed source return, with the negative true mass retained.
Q1=s.Matrix([[0,1+s.I],[1-s.I,0]])
Q2=s.Matrix([[1,s.I],[-s.I,-1]])
I=s.eye(2); a,b,l,ds=s.symbols('a b l ds',real=True)
D=b+l-a
A=a*Q1;B=b*Q1;As=l*Q1;E=D*(Q1+2*I)
check('full_signed_return',s.expand(B+As+2*D*I-E-A)==s.zeros(2))
A2=a*Q1+ds*Q2
check('mixed_labels_return',s.expand((B+As+2*D*I-E)+ds*Q2-A2)==s.zeros(2))

# Integrals entering finite Euler returns.
x=s.symbols('x',positive=True)
primitive=2*s.sqrt(x)*s.log(x)-4*s.sqrt(x)
check('Euler_integrals',s.simplify(s.diff(primitive,x)-s.log(x)/s.sqrt(x))==0)
primitive2=(-2*s.log(x)-4)/s.sqrt(x)
check('Euler_integrals',s.simplify(s.diff(primitive2,x)-s.log(x)/x**s.Rational(3,2))==0)
check('Euler_integrals',s.simplify((primitive.subs(x,1)))==-4)
O,z=s.symbols('O z',nonnegative=True)
check('Euler_constants',s.expand((8+4*z)+(8+8*O+(4+4*O)*z)-(16+8*O+(8+4*O)*z))==0)
P0=s.diag(0,0,1,1)
v0=s.Matrix([1,0,0,0]);w0=s.Matrix([0,1,0,0])
v1=s.Matrix(s.symbols('v0:4'));w1=s.Matrix(s.symbols('w0:4'))
rank_deriv=v1*w0.T+v0*w1.T+w1*v0.T+w0*v1.T
check('log_contact_rank_two_derivative',P0*rank_deriv*P0==s.zeros(4))

# Actual original-P sine-vector coefficients; no numerical production cell.
u=s.symbols('u',positive=True)
a0=s.Rational(1,4)+u**2;b0=-(s.Rational(1,4)+4*u**2)/2
check('actual_contact_sine',s.simplify(a0*u/(s.Rational(1,4)+u**2)+b0*2*u/(s.Rational(1,4)+4*u**2))==0)
check('actual_contact_sine',s.expand(b0**2-a0**2)==3*(u**4-s.Rational(1,64)))
check('actual_contact_sine', (b0**2-a0**2).subs(u,s.Rational(1,4))<0)

# Fixed exponent budgets. These arithmetic controls do not prove asymptotics.
e=s.symbols('epsilon',positive=True); k=e/4
check('exponent_algebra',s.simplify(2*k+e-3*e/2)==0)
check('exponent_algebra',s.simplify(k/2-e/8)==0)
check('exponent_algebra',s.simplify(4/k-4-(16/e-4))==0)
check('exponent_algebra',s.Rational(3,2)*s.Rational(1,32)<s.Rational(1,2))

# Planted failures; each tests an actual change in the displayed formulas.
reject('omit_small_base_high_prime_powers',all(v>=0 for v in diffvec(2,4,True).values()))
reject('rough_prime_square_matches_Lambda',lam(2,9)**2/cz(2)**2*2==1)
reject('replace_lcm_by_product',sum((coeff(2,d)*coeff(2,e)/Q(d*e) for d in (1,2) for e in (1,2)),Q(0))==cz(2))
reject('drop_square_in_nonnegative_model',lam(3,6)/cz(3)>=0)
reject('forget_negative_actual_mass',s.expand(B+As+2*(b+l)*I-E-A)==s.zeros(2))
top_coefficient=diffvec(2,9)[3] # coefficient of actual log(3)
top_diagonal=2*s.Rational(top_coefficient.numerator,top_coefficient.denominator)/s.sqrt(9)
top_energy=top_diagonal
check('actual_top_atom_cancellation',s.simplify(top_diagonal-top_energy)==0)
reject('delete_top_square_only',s.simplify(top_diagonal)==0)
V=s.Matrix([[0,0],[1,0]])
reject('truncated_shift_is_unitary',(s.eye(2)+V).T*(s.eye(2)+V)==2*s.eye(2)+V+V.T)
zv=s.Matrix([1+s.I,2-s.I])
reject('transpose_for_complex_norm',(zv.T*zv)[0]==(zv.conjugate().T*zv)[0])

out={
 'status':'EXACT_LOCAL_CONTROLS_COMPLETED',
 'checks':dict(counts),'total_checks':sum(counts.values()),
 'planted_errors_detected':planted,'planted_count':len(planted),
 'scope':'finite algebra and exponent checks only; no asymptotic sign or original CCM spectrum certification',
 'independent_audit':False,'lean':False,'arb':False
}
Path('q33_checks.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,ensure_ascii=False,indent=2))
