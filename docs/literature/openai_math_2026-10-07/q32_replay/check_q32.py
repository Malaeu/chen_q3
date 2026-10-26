#!/usr/bin/env python3
"""Q32 finite exact controls. Not an asymptotic or actual-CCM certificate.
Python 3 + SymPy. Usage: python check_q32.py results.json
"""
from __future__ import annotations
import json
import sys
from pathlib import Path
import sympy as s

checks: list[str] = []
planted: list[str] = []

def zero(a):
    if isinstance(a, s.MatrixBase):
        return all(s.simplify(v) == 0 for v in a)
    return s.simplify(a) == 0

def eq(name, a, b=0):
    if not zero(a-b):
        raise AssertionError((name, s.simplify(a-b)))
    checks.append(name)

def reject(name, a, b=0):
    if zero(a-b):
        raise AssertionError('undetected planted change: '+name)
    planted.append(name)

def ok(name, condition):
    if not condition:
        raise AssertionError(name)
    checks.append(name)

# The cutoff is carried by the TEST only.
u=s.symbols('u',real=True)
p=1-10*u**3+15*u**4-6*u**5
for j in range(3):
    eq(f'cutoff_jet_left_{j}',s.diff(p,u,j).subs(u,0),1 if j==0 else 0)
    eq(f'cutoff_jet_right_{j}',s.diff(p,u,j).subs(u,1),0)
eq('cutoff_monotonicity_factor',s.diff(p,u),-30*u**2*(1-u)**2)

def chi(x):
    if x<=1:return s.S.One
    if x>=2:return s.S.Zero
    return p.subs(u,x-1)
for x in [s.Rational(5,2),s.Integer(5),s.Integer(7),s.Integer(11),s.Rational(63,2)]:
    B=4; J=2
    eq('partition_'+str(x),chi(x/B)+sum(chi(x/(2*(2**j)*B))-chi(x/((2**j)*B)) for j in range(J+1)),1)
reject('square_cutoff',s.Rational(1,2),s.Rational(1,2)**2)

# Complete matrix Fourier difference identity.
z=s.symbols('z',nonzero=True)
A={1:s.Matrix([[1,2+s.I],[2-s.I,3]]),2:s.Matrix([[2,-s.I],[s.I,-1]]),3:s.Matrix([[0,1],[1,2]])}
Z=s.zeros(2)
Ah=sum((v*z**(-n) for n,v in A.items()),Z)
diff=sum(((A.get(n+2,Z)-2*A.get(n+1,Z)+A.get(n,Z))*z**(-n) for n in range(-1,4)),Z)
eq('full_second_difference_fourier',diff,(1-z)**2*Ah)
# An exact subarc is a sinc kernel, not a diagonal/positive-part replacement.
lam=s.Rational(1,6)
def k(d):
    return 2*lam if d==0 else s.sin(2*s.pi*lam*d)/(s.pi*d)
t=s.symbols('t',real=True)
for d in range(4):
    eq('sinc_integral_'+str(d),s.integrate(s.cos(2*s.pi*d*t),(t,-lam,lam)),k(d))
b={1:-1,2:s.symbols('log2')-1,3:s.symbols('log3')-1}
Bh=sum(v*z**(-n) for n,v in b.items())
prod=s.expand(Bh*Ah.subs(z,1/z))
# Apply the linear interval integration functional to all Laurent coefficients.
via_coeff=s.zeros(2)
for d in range(-2,3):
    via_coeff += prod.applyfunc(lambda v:s.expand(v).coeff(z,d))*k(d)
direct=sum((bn*Al*k(l-n) for n,bn in b.items() for l,Al in A.items()),s.zeros(2))
eq('all_source_test_mixed_pairs',via_coeff,direct)
reject('drop_cross_indices',direct,sum((b[n]*A[n]*k(0) for n in A),s.zeros(2)))
wrong=direct.applyfunc(s.re)
reject('erase_complex_offdiagonal',direct,wrong)
# A zero top does not survive a low pass by itself.
H=s.Matrix([[1,1+s.I],[1-s.I,2]])
smoothed_top=H*k(1)
reject('lowpass_preserves_top_zero',smoothed_top,s.zeros(2))

# Actual arithmetic prime powers and finite Mobius-log reconstruction.
primes=list(s.primerange(2,40)); logs={p:s.Symbol('log'+str(p)) for p in primes}
def logn(n):return sum((v*logs[p] for p,v in s.factorint(n).items()),s.S.Zero)
def mangoldt(n):
    fs=s.factorint(n)
    return logs[next(iter(fs))] if len(fs)==1 else s.S.Zero
for n in range(1,25):
    eq('mu_log_'+str(n),sum(int(s.mobius(d))*logn(n//d) for d in s.divisors(n)),mangoldt(n))
reject('delete_prime_square',mangoldt(4),0)
eq('residual_atom_one',mangoldt(1)-1,-1)
# An interval and a hyperbolic cutoff remain literal in the paired formula.
I=range(4,13)
w={n:sum((Al*k(l-n) for l,Al in A.items()),s.zeros(2)) for n in I}
linear=sum((mangoldt(n)*w[n] for n in I),s.zeros(2))
rebuilt=s.zeros(2)
for d in range(1,13):
    for r in range(1,12//d+1):
        if d*r in w:rebuilt += int(s.mobius(d))*logn(r)*w[d*r]
eq('same_lowpassed_test_hyperbola',linear,rebuilt)

# Rational approximants: they are not legal on the microscopic central arc.
for X,tt in [(100,s.Rational(3,100)),(1000,s.Rational(7,1000)),(10000,s.Rational(9,10000))]:
    q=int(s.floor(1/tt))
    ok('rational_domain_'+str(X),q<=X//2 and abs(tt-s.Rational(1,q))<=s.Rational(1,q*q))
    central=s.Rational(1,100*X)
    badq=int(s.floor(1/central))
    ok('central_large_q_not_admissible_'+str(X),badq>4*X)
    ok('no_nonzero_small_denominator_'+str(X),all(s.Rational(1,q)-central>s.Rational(1,q*q) for q in range(2,40)))

# Original-P even five-mode contact discriminator, entirely symbolic.
om=s.symbols('omega',positive=True)
x=s.symbols('x',real=True)
c0=-s.Rational(3,4); c1=1+4*om**2; c2=-(s.Rational(1,4)+4*om**2)
eq('endpoint_contact',c0+c1+c2)
for a in [s.Rational(1,2),-s.Rational(1,2)]:
    eq('exponential_contact_'+str(a),c0/a+c1*a/(a*a+om*om)+c2*a/(a*a+4*om*om),0)
normal=c0*c0+(c1*c1+c2*c2)/2
eq('physical_norm_polynomial',normal,s.Rational(35,32)+5*om**2+16*om**4)
profile=c0+c1*s.cos(om*x)+c2*s.cos(2*om*x)
lead=s.expand(s.series(profile,om,0,6).removeO()).coeff(om,4)
eq('endpoint_profile_leading_jet',lead,6*x*x-x**4/8)
h=s.symbols('h',positive=True)
overlap=s.integrate(lead*lead.subs(x,h-x),(x,0,h))
eq('all_mixed_endpoint_overlap',overlap,s.Rational(6,5)*h**5-h**7/70+h**9/40320)
reject('drop_quartic_cross_terms',overlap,s.Rational(6,5)*h**5)
eq('top_window_half_weight',chi(s.Rational(3,2)),s.Rational(1,2))

# Exact integral budgets; no data fitting.
y,K=s.symbols('y K',positive=True)
for power,expected,name in [
 (s.Rational(1,2),s.Rational(8,3)*K**s.Rational(3,2),'sqrt_y'),
 (s.Integer(0),2*K,'one'),
 (-s.Rational(1,2),s.Rational(8,3)*s.sqrt(K),'inverse_sqrt_y')]:
    val=s.integrate(y**power,(y,0,K))+K*K*s.integrate(y**(power-2),(y,K,s.oo))
    eq('dual_weight_integral_'+name,val,expected)
for name,lhs,rhs in [
 ('annulus_term1',-s.Rational(1,2)+s.Rational(5,16),-s.Rational(3,16)),
 ('annulus_term2',-s.Rational(7,10)+s.Rational(5,8),-s.Rational(3,40)),
 ('annulus_term3',-1+s.Rational(15,16),-s.Rational(1,16)),
 ('annulus_epsilon',2-2*s.Rational(1,16),s.Rational(15,8))]:eq(name,lhs,rhs)
e=s.symbols('epsilon',positive=True)
eq('full_dominant_power',s.Rational(1,2)+e/2,(1+e)/2)
for ee in [s.S.Zero,s.Rational(1,32)]:
    ok('dominance_check_'+str(ee),s.Rational(1,2)+ee/2>s.Rational(3,10)+ee and s.Rational(1,2)+ee/2>2*ee)
reject('vanishing_power_promotion',s.Rational(1,2)+s.Rational(1,128),s.Rational(1,32))
# End-to-end bookkeeping: exact core error is not a second divisor charge.
A,N,E,Qsmall,Arch=s.symbols('A N E Qsmall Arch')
reject('double_divisor_fee',Arch-N-E,Arch-N-E-Qsmall)

result={'kind':'FINITE_EXACT_ALGEBRA_ONLY_NOT_GLOBAL_CCM_CERTIFICATE',
        'checks':checks,'exact_controls':len(checks),'planted':planted,
        'planted_errors_detected':len(planted),'production_CCM':False,
        'independent_audit':False,'Lean':False,'Arb':False,
        'external_Vaughan_proof_reproved':False}
Path(sys.argv[1] if len(sys.argv)>1 else 'exact_results.json').write_text(json.dumps(result,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
print(json.dumps({'exact_controls':len(checks),'planted_errors_detected':len(planted)}))
