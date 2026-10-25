#!/usr/bin/env python3
"""Exact finite algebra controls for Q20, not CCM or asymptotic certification."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import sympy as s

outdir = Path(__file__).resolve().parent
checks = []
planted = []

def check(name, proposition):
    if not bool(proposition):
        raise AssertionError(name)
    checks.append(name)

def zero(name, expression):
    check(name, s.simplify(s.expand(expression)) == 0)

def detect(name, discrepancy):
    if s.simplify(discrepancy) == 0:
        raise AssertionError('missed planted failure: ' + name)
    planted.append(name)

p, q = s.symbols('p q', positive=True)
a, b, c, d = s.symbols('a b c d', real=True)
x, y = a+s.I*b, c+s.I*d
nx, ny = a*a+b*b, c*c+d*d
xy = a*c+b*d
E = q/p*nx + p/q*ny - 2*xy
raw = nx+ny-2*xy
row = (p-q)/p*nx + (q-p)/q*ny
zero('jump_groundstate_identity_complex', raw-E-row)
zero('adjacency_is_diagonal_minus_energy', 2*xy-(q/p*nx+p/q*ny-E))
zero('energy_positive_square_representation', E-p*q*s.expand_complex((x/p-y/q)*s.conjugate(x/p-y/q)))

r1,r2 = s.symbols('r1 r2', nonnegative=True)
Eabs = q/p*nx+p/q*ny-2*r1*r2
zero('phase_defect_retains_both_complex_cross_terms', E-Eabs-2*(r1*r2-xy))
zero('phase_defect_is_gauge_independent_p', s.diff(E-Eabs,p))
zero('phase_defect_is_gauge_independent_q', s.diff(E-Eabs,q))
zero('outside_support_energy_equals_tail_diagonal', E.subs({c:0,d:0})-(q/p)*nx)
detect('deleting_tail_energy_without_return', (E.subs({p:1,q:2,a:1,b:0,c:0,d:0})))
detect('pole_energy_wrong_plus_sign', (2*xy-(q/p*nx+p/q*ny+E)).subs({p:1,q:2,a:1,b:1,c:-1,d:2}))
detect('dropping_imaginary_mixed_product', (2*xy-2*a*c).subs({a:0,b:1,c:0,d:1}))

# Finite four-node algebraic control. c_i is chosen to enforce Qh=0.
# These matrices are NOT the actual theta source or an arithmetic counterexample.
h = s.Matrix([1,2,3,4])
f = s.Matrix([1+s.I,-2+3*s.I,0,0])
arch = [(0,1,s.Rational(2,3)),(1,2,s.Rational(3,5)),(2,3,s.Rational(5,7))]
prime = [(0,1,s.Rational(7,11)),(0,2,s.Rational(11,13)),(1,3,s.Rational(13,17))]
pole = [(0,1,s.Rational(17,19)),(0,2,s.Rational(19,23)),(0,3,s.Rational(23,29)),(1,2,s.Rational(29,31)),(1,3,s.Rational(31,37)),(2,3,s.Rational(37,41))]
N=4
La=s.zeros(N); Ap=s.zeros(N); Rp=s.zeros(N)
for i,j,w in arch:
    La[i,i]+=w; La[j,j]+=w; La[i,j]-=w; La[j,i]-=w
for i,j,w in prime:
    Ap[i,j]+=w; Ap[j,i]+=w
for i,j,w in pole:
    Rp[i,j]+=w; Rp[j,i]+=w
pot=s.diag(*[((La-Ap+Rp)*h)[i]/h[i] for i in range(N)])
Q=La-Ap+Rp-pot
check('finite_radical_reference', Q*h==s.zeros(N,1))

def energy(edges):
    return s.expand(sum(w*h[i]*h[j]*(f[i]/h[i]-f[j]/h[j])*s.conjugate(f[i]/h[i]-f[j]/h[j]) for i,j,w in edges))
Ea,Ep,Er=energy(arch),energy(prime),energy(pole)
zero('finite_complete_groundstate_all_cross_terms', (s.conjugate(f).T*Q*f)[0]-(Ea+Ep-Er))
internal=[e for e in prime if e[0]<2 and e[1]<2]
external=[e for e in prime if e not in internal]
tail=sum(w*(h[j]/h[i]*f[i]*s.conjugate(f[i])+h[i]/h[j]*f[j]*s.conjugate(f[j])) for i,j,w in external)
zero('finite_tail_reconstruction', Ep-energy(internal)-tail)
Vpole=[(Rp*h)[i]/h[i] for i in range(N)]
Vtail=[0]*N
for i,j,w in external:
    Vtail[i]+=w*h[j]/h[i];Vtail[j]+=w*h[i]/h[j]
Ainternal=s.zeros(N)
for i,j,w in internal:
    Ainternal[i,j]+=w;Ainternal[j,i]+=w
Qcore=La-Ainternal-pot
zero('finite_core_identity_with_effective_potential', (s.conjugate(f).T*Qcore*f)[0]-(Ea+energy(internal)-sum((Vpole[i]-Vtail[i])*f[i]*s.conjugate(f[i]) for i in range(N))))

# Pole/contact scalar formula: x=e^(T/2)>1.
X,A = s.symbols('X A', positive=True)
zero('plateau_pole_row_ceiling', 8*A*(X-X**-1)/2*(X+X**-1)/2-2*A*(X**2-X**-2))
am,ap,Y=s.symbols('am ap Y',positive=True) # Y=e^(L/2)=sqrt(m)
Mp=(ap+Y*am)/s.sqrt(2)
Mm=(am+ap/Y)/s.sqrt(2)
zero('modulus_two_bump_pole_mass', 2*Mp*Mm-(am**2*Y+2*am*ap+ap**2/Y))

# Derivative-filtered compact polynomial controls (finite-order stand-ins only).
t=s.symbols('t',real=True)
for k in (4,5,6):
    eta=(t-1)**k*(2-t)**k
    v=s.diff(eta,t,2)-eta/4
    for sg in (-1,1):
        al=s.Rational(sg,2)
        # Exact antiderivative for e^(al*t)(D^2-1/4)eta.
        F=s.exp(al*t)*(s.diff(eta,t)-al*eta)
        zero(f'filtered_contact_primitive_k{k}_sg{sg}',s.diff(F,t)-s.exp(al*t)*v)
        zero(f'filtered_contact_boundary_k{k}_sg{sg}',F.subs(t,2)-F.subs(t,1))
    check(f'profile_nonzero_k{k}',v.subs(t,s.Rational(3,2))!=0)
    for j in range(k-2):
        zero(f'filtered_left_jet_k{k}_j{j}',s.diff(v,t,j).subs(t,1))
        zero(f'filtered_right_jet_k{k}_j{j}',s.diff(v,t,j).subs(t,2))

# Fixed derivative order, never q=q(m).
for eps in (Fraction(1,40),Fraction(1,64),Fraction(1,100)):
    order=eps.denominator//eps.numerator+3
    exponents=[1+eps*(Fraction(1,2)-order),
               Fraction(1,2)+eps*(Fraction(3,2)-order),
               Fraction(1,2)+eps*(1-order),
               Fraction(1,2)+eps*(Fraction(1,2)-order),
               eps*(Fraction(3,2)-order)]
    for j,v in enumerate(exponents):
        check(f'fixed_q_return_eps_{eps}_term_{j}',v<0)

# A signed pole kernel is not a positive-semidefinite form merely because
# its pointwise entries are positive.
R=s.Matrix([[2,s.Rational(5,2)],[s.Rational(5,2),2]])
check('pole_positive_entries',all(x>0 for x in R))
check('pole_negative_direction', (s.Matrix([[1,-1]])*R*s.Matrix([1,-1]))[0]==-1)

result={
 'status':'EXACT_LOCAL_ALGEBRA_ONLY_NOT_ASYMPTOTIC_CERTIFICATION',
 'sympy':s.__version__,
 'check_count':len(checks),
 'checks':checks,
 'planted_failures_detected':planted,
 'planted_failure_count':len(planted),
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'registration_sha256':hashlib.sha256((outdir/'registration.json').read_bytes()).hexdigest(),
 'actual_CCM_spectral_runs':0,'arb_runs':0,'lean_runs':0,
 'hypothetical_zero_values_assigned':False,
 'independent_review':'NOT_RUN'
}
(outdir/'exact_results.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(result,ensure_ascii=False,indent=2))
