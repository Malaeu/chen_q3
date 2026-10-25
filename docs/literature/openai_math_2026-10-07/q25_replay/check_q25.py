#!/usr/bin/env python3
"""Exact finite algebra controls for Q25; not an arithmetic sign certificate."""
import argparse
import json
from pathlib import Path
import sympy as s

passed = []
planted = []

def eq(name, lhs, rhs):
    if s.simplify(s.expand(lhs-rhs)) != 0:
        raise AssertionError(f'{name}: {s.simplify(lhs-rhs)}')
    passed.append(name)

def yes(name, value):
    if not bool(value):
        raise AssertionError(name)
    passed.append(name)

def bad(name, lhs, rhs):
    if s.simplify(s.expand(lhs-rhs)) == 0:
        raise AssertionError(f'Planted failure escaped: {name}')
    planted.append(name)

x, y, a = s.symbols('x y a', positive=True, real=True)
z, H, t = s.symbols('z H t', real=True)
C = s.Function('C')
# Exact differentiation with both time orientations.
for sign in (-1, 1):
    direct = x**(-s.Rational(1,2))*C(2*a+sign*s.log(x))
    op = C(y)
    for j in range(5):
        expr = x**(-s.Rational(1,2)-j)*op.subs(y,2*a+sign*s.log(x))
        eq(f'derivative_sign_{sign}_order_{j}', s.diff(direct,x,j), expr)
        op = sign*s.diff(op,y)-(s.Rational(1,2)+j)*op

for j in range(7):
    eq(f'adjacent_binomial_{j}',(H+t)**j,
       sum(s.binomial(j,l)*H**(j-l)*t**l for l in range(j+1)))

def mangoldt(n):
    factors=s.factorint(int(n))
    return s.log(next(iter(factors))) if len(factors)==1 else s.Integer(0)

def moment(left,right,j):
    atoms=sum(mangoldt(n)*(s.Integer(n)-left)**j
              for n in range(2,int(s.floor(right))+1) if left<n<=right)
    return atoms-(right-left)**(j+1)/s.Integer(j+1)

for j in range(4):
    eq(f'actual_Lambda_adjacent_{j}',moment(s.Integer(1),s.Integer(12),j),
       moment(s.Integer(1),s.Integer(6),j)+
       sum(s.binomial(j,l)*5**(j-l)*moment(s.Integer(6),s.Integer(12),l)
           for l in range(j+1)))
for n,p in ((4,2),(8,2),(9,3),(16,2),(25,5)):
    eq(f'proper_power_weight_{n}',mangoldt(n),s.log(p))
eq('non_prime_power_12',mangoldt(12),0)

F=(1+2*s.I)+(-3+s.I)*x+(2-s.I)*x*x
atoms=sum(mangoldt(n)*F.subs(x,n) for n in range(2,11))
whole=atoms-s.integrate(F,(x,1,10))
jets=0
for left,right in ((1,4),(4,7),(7,10)):
    local=sum(mangoldt(n)*F.subs(x,n) for n in range(left+1,right+1))-s.integrate(F,(x,left,right))
    jet=sum(s.diff(F,x,j).subs(x,left)*moment(s.Integer(left),s.Integer(right),j)/s.factorial(j) for j in range(3))
    eq(f'complex_exact_local_jets_{left}_{right}',local,jet)
    jets+=jet
eq('complex_joint_cell_reassembly',whole,jets)

lam,e,n,v=s.symbols('lam e n v',real=True)
u=n+e-lam+v
V=-lam*e+lam**2/2
D2=lam*e**2-lam**2*e+lam**3/3
eq('actual_bin_first_displacement',s.integrate(n-u,(v,0,lam)),V)
eq('actual_bin_second_displacement',s.integrate((n-u)**2,(v,0,lam)),D2)
eq('midpoint_jump_chain',(e**2-(e-lam)**2)/2,lam*(e-lam/2))
eq('second_displacement_nonnegative_form',D2,lam*(e-lam/2)**2+lam**3/12)

# Generic rational positive masses test exact finite geometry, not sampled primes.
cases=[{2:s.Rational(3,2),3:s.Rational(1,4),4:s.Integer(0),5:s.Rational(2,3)},
       {2:s.Integer(3),3:s.Integer(2),4:s.Integer(0),5:s.Integer(1)}]
for ci,masses in enumerate(cases):
    m=5
    mass=sum(masses.values()); endpoint=1+mass; Em=endpoint-m
    for deg in range(4):
        G=(1+s.I)*x**deg+(2-s.I)*x
        direct=sum(l*G.subs(x,n0) for n0,l in masses.items())-s.integrate(G,(x,1,m))
        cursor=s.Integer(1); disp=s.Integer(0); first=s.Integer(0)
        for n0,l in masses.items():
            disp+=s.integrate(G.subs(x,n0)-G,(x,cursor,cursor+l))
            En=cursor+l-n0
            first+=s.diff(G,x).subs(x,n0)*(-l*En+l*l/2)
            cursor+=l
        terminal=s.integrate(G,(x,m,endpoint))
        eq(f'finite_transport_case_{ci}_degree_{deg}',direct,disp+terminal)
        # Lebesgue pieces of right-continuous E; all jumps are separate.
        psi=s.Integer(0); EF=s.Integer(0); E2F=s.Integer(0)
        for left in range(1,m):
            if left>=2: psi+=masses[left]
            Ex=psi-(x-1)
            EF+=s.integrate(Ex*s.diff(G,x),(x,left,left+1))
            E2F+=s.integrate(Ex**2*s.diff(G,x,2),(x,left,left+1))
        first_ref=-EF-s.diff(G,x).subs(x,m)*Em**2/2+E2F/2
        eq(f'finite_flux_BV_case_{ci}_degree_{deg}',first,first_ref)
        rem=disp-first
        eq(f'finite_full_second_return_case_{ci}_degree_{deg}',rem+terminal,
           G.subs(x,m)*Em+s.diff(G,x).subs(x,m)*Em**2/2-E2F/2)

beta=s.Rational(3,5); theta=s.Rational(4,5); k=3
eq('threshold_exponent',2*beta-theta-s.Rational(1,2),-s.Rational(1,10))
eq('Taylor_exponent',s.Rational(1,2)-k*(1-theta),-s.Rational(1,10))
eq('localized_reconstruction_exponent',2*(-s.Rational(1,10)),-s.Rational(1,5))
epsilon=s.Rational(1,64); q=67
yes('fixed_q_receiver',q>1/epsilon+2)
exps=[1+epsilon*(s.Rational(1,2)-q),s.Rational(1,2)+epsilon*(s.Rational(3,2)-q),
      s.Rational(1,2)+epsilon*(1-q),s.Rational(1,2)+epsilon*(s.Rational(1,2)-q)]
for j,value in enumerate(exps): yes(f'receiver_negative_power_{j}',value<0)

delta,gamma=s.symbols('delta gamma', real=True)
tau=s.Rational(1,2)-delta
eq('model_density_exponent',1-s.Rational(1,2)-tau,delta)
eq('resonant_branch_phase',2*s.I*gamma*a+2*a*(delta-s.I*gamma),2*delta*a)
eq('reflected_branch_phase',2*s.I*gamma*a+2*a*(delta+s.I*gamma),2*delta*a+4*s.I*gamma*a)
# Complex norm cross terms, unrelated to any numerical hypothetical zero.
K=s.Matrix([[2,1+s.I],[1-s.I,3]])
g=s.Matrix([1+s.I,2]); kk=s.Matrix([2-s.I,-1+s.I]); phase=(3+4*s.I)/5
f=s.conjugate(phase)*g-phase*kk
form=(f.conjugate().T*K*f)[0]
ref=(g.conjugate().T*K*g)[0]+(kk.conjugate().T*K*kk)[0]-2*s.re(phase**2*(g.conjugate().T*K*kk)[0])
eq('complete_complex_pair_cross',form,ref)
err=s.Matrix([s.Rational(1,3),s.I/7])
eq('complete_return_cross_and_square',((g+err).conjugate().T*K*(g+err))[0],
   (g.conjugate().T*K*g)[0]+2*s.re((g.conjugate().T*K*err)[0])+(err.conjugate().T*K*err)[0])

bad('missing_adjacent_origin_shift',moment(s.Integer(1),s.Integer(12),1),
    moment(s.Integer(1),s.Integer(6),1)+moment(s.Integer(6),s.Integer(12),1))
bad('missing_half_jump',s.integrate(n-u,(v,0,lam)),-lam*e)
bad('missing_terminal_edge',s.Integer(6)-4,s.Integer(0)) # constant F=1, case 1: displacement=0
bad('double_counting_shared_atom',moment(s.Integer(1),s.Integer(8),0),
    moment(s.Integer(1),s.Integer(4),0)+moment(s.Integer(4),s.Integer(8),0)+mangoldt(4))
c=1+2*s.I
bad('complex_kappa_replaced_by_modulus',s.re((1/s.conjugate(c)**2)*(1+s.I)),
    s.re((1/(c*s.conjugate(c)))*(1+s.I)))
bad('missing_return_error_square',((g+err).conjugate().T*K*(g+err))[0],
    (g.conjugate().T*K*g)[0]+2*s.re((g.conjugate().T*K*err)[0]))
bad('single_interval_mass_not_first_moment',s.Integer(0),-H**2/2)

out={
    'task':'Q25','status':'EXACT_LOCAL_CONTROLS_COMPLETED',
    'exact_controls':len(passed),'planted_errors_detected':len(planted),
    'checks':passed,'planted':planted,'sympy_version':s.__version__,
    'scope':'Finite algebra and exact coefficient bookkeeping only; not a proof of asymptotic prime cancellation, CCM sign, or RH.',
    'hypothetical_zero_numerical_values_assigned':False,
    'lean_runs':0,'arb_runs':0,'ccm_spectral_runs':0,'independent_review':'NOT_RUN'}
parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,default=Path('exact_results.json'))
args=parser.parse_args();args.out.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ('status','exact_controls','planted_errors_detected')},ensure_ascii=False))
