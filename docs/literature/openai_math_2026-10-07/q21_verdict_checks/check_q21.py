#!/usr/bin/env python3
"""Exact finite checks for Q21. No CCM spectrum or asymptotic certification."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import sympy as s

ROOT=Path(__file__).resolve().parent
checks=[]
planted=[]

def check(name, truth):
    if not bool(truth):
        raise AssertionError(name)
    checks.append(name)

def zero(name, expr):
    check(name, s.simplify(s.expand(expr)) == 0)

def detect(name, expr):
    if s.simplify(s.expand(expr)) == 0:
        raise AssertionError('undetected planted defect: '+name)
    planted.append(name)

def abs2(z):
    return s.expand(z*s.conjugate(z))

ar,ai,br,bi=s.symbols('ar ai br bi',real=True)
tau=s.symbols('tau',positive=True)
A=ar+s.I*ai; B=br+s.I*bi
Y=(1+tau)*abs2(A)+(1+1/tau)*abs2(B)
Xi=abs2(tau*A+B)/tau
zero('complex_Young_exact_slack',Y-abs2(A-B)-Xi)
zero('cross_phase_not_deleted',Xi-(tau*abs2(A)+abs2(B)/tau+2*s.re(s.conjugate(A)*B)))
detect('planted_slack_zero',Xi.subs({ar:1,ai:0,br:1,bi:0,tau:1}))
detect('planted_imaginary_cross_deleted',(2*s.re(s.conjugate(A)*B)-2*ar*br).subs({ar:0,ai:1,br:0,bi:1}))

rx,ry,rz,K,C,cn=s.symbols('rx ry rz K C cn',positive=True)
fx,fy,fz=s.symbols('fx fy fz',real=True)
Ap=fz/rz-fx/rx; Bp=fz/rz-fy/ry
zero('two_edge_telescoping',Ap-Bp-(fy/ry-fx/rx))
weighted=K*rx*ry*(tau*Ap+Bp)**2/tau
ext=s.factor(weighted.subs(fz,0))
zero('exterior_gap_exact',ext/K-(tau*ry/rx*fx**2+rx/(tau*ry)*fy**2+2*fx*fy))
zero('exterior_AMGM_remainder',ext-4*K*fx*fy-K*(tau*ry*fx-rx*fy)**2/(tau*rx*ry))
zero('optimal_local_balance_exterior',ext.subs(tau,rx*fy/(ry*fx))-4*K*fx*fy)
# Both actual source ratios are needed to reproduce the original demand measure.
zero('prime_ratio_return',cn*rx*rz*((1+tau)*K/C*ry/rz)-K*rx*ry*cn/C*(1+tau))
a=s.symbols('a',positive=True)
zero('arch_ratio_return',a*ry*rz*((1+1/tau)/a*cn*K/C*rx/rz)-K*rx*ry*cn/C*(1+1/tau))
detect('planted_prime_ratio_equals_one',(cn*rx*rz*(1+tau)*K/C-K*rx*ry*cn/C*(1+tau)).subs({rx:2,ry:3,rz:5,cn:7,K:11,C:13,tau:2}))
detect('planted_arch_ratio_equals_one',(a*ry*rz*(1+1/tau)/a*cn*K/C-K*rx*ry*cn/C*(1+1/tau)).subs({rx:2,ry:3,rz:5,cn:7,K:11,C:13,tau:2}))
x,d,h=s.symbols('x d h',real=True)
J=s.Matrix([x+d,h-d]).jacobian([x,d])
check('arch_coordinate_Jacobian_absolute_one',abs(J.det())==1)

# Check the exact upper inequalities through their explicit nonnegative remainders.
xr,xi,yr,yi,zr,zi=s.symbols('xr xi yr yi zr zi',real=True)
X=xr+s.I*xi; Yv=yr+s.I*yi; Z=zr+s.I*zi
path=2*abs2(Z-X)+2*abs2(Z-Yv)
cap=4*abs2(X)+4*abs2(Yv)+8*abs2(Z)
zero('integrated_upper_two_edge_cap',cap-path-2*abs2(Z+X)-2*abs2(Z+Yv))
zero('short_edge_diagonal_cap',2*(abs2(X)+abs2(Yv))-abs2(Yv-X)-abs2(X+Yv))
zero('tail_energy_not_tail_adjacency',(ry/rx*abs2(X)+rx/ry*abs2(Yv)-2*s.re(s.conjugate(X)*Yv)).subs({yr:0,yi:0})-ry/rx*abs2(X))
detect('planted_future_energy_zero',(ry/rx*abs2(X)).subs({rx:2,ry:3,xr:1,xi:2}))

# A synthetic finite path graph checks aggregation, not the actual CCM.
rho=[s.Rational(2),s.Rational(3),s.Rational(5),s.Rational(7)]
f=[1+2*s.I,-2+s.I,3-s.I,0]
u=[f[j]/rho[j] for j in range(4)]
demands=[(0,1,s.Rational(3,7),[(2,s.Rational(2,5),s.Rational(3,2)),(3,s.Rational(3,5),s.Rational(5,3))]),
         (1,2,s.Rational(5,11),[(3,s.Rational(1),s.Rational(7,4))])]
P=0; H=0; SL=0; OUT=0; INS=0
for i,j,k,paths in demands:
    check('probability_sum_'+str(i)+str(j),sum(p for _,p,_ in paths)==1)
    P+=k*rho[i]*rho[j]*abs2(u[j]-u[i])
    for z,p,t in paths:
        aa=u[z]-u[i];bb=u[z]-u[j]
        H+=k*rho[i]*rho[j]*p*((1+t)*abs2(aa)+(1+1/t)*abs2(bb))
        sl=k*rho[i]*rho[j]*p*abs2(t*aa+bb)/t
        SL+=sl
        if z==3: OUT+=sl
        else: INS+=sl
zero('complete_graph_slack_all_cross_terms',H-P-SL)
zero('exterior_corrected_comparison',H-OUT-P-INS)
Eplus=s.Rational(17,13)*abs2(u[1]-u[0])+s.Rational(19,17)*abs2(u[2]-u[1])+s.Rational(23,19)*abs2(u[3]-u[2])
Q=Eplus-P
zero('joint_excess_equals_slack_minus_Q',H-Eplus-(SL-Q))

# Fixed-shell mass ratios from the derived PNT leading terms.
z=s.symbols('z',positive=True)  # z=exp(Delta/4)>1
zero('outer_half_shell_fraction',(z*z-z)/(z*z-1)-z/(z+1))
zero('outer_fraction_minus_half',z/(z+1)-s.Rational(1,2)-(z-1)/(2*(z+1)))
for v in [s.Rational(5,4),s.Rational(3,2),s.Rational(2),s.Rational(3),s.Rational(10)]:
    check('outer_half_fraction_'+str(v),v/(v+1)>s.Rational(1,2))

# Exterior geometry for b=Delta/8 and s in [Delta/2,Delta].
for de in [Fraction(1,2),Fraction(1),Fraction(2),Fraction(4)]:
    aa=de/16;bb=de/8
    for xx,vv in [(aa,aa),(aa,bb),(bb,aa),(bb,bb)]:
        ss=de/2
        check('outside_vertex_'+str((de,xx,vv)),ss-vv>0)
        check('future_prime_'+str((de,xx,vv)),ss-xx-vv>0)

# Compact polynomial stand-ins check contacts algebraically. The proof uses C-infinity bumps.
t=s.symbols('t',real=True)
a0=s.Rational(1,16);b0=s.Rational(1,8)
for order in (4,5,6):
    eta=(t-a0)**order*(b0-t)**order
    q=s.diff(eta,t,2)-eta/4
    for sign in (-1,1):
        al=s.Rational(sign,2)
        F=s.exp(al*t)*(s.diff(eta,t)-al*eta)
        zero('contact_primitive_'+str((order,sign)),s.diff(F,t)-s.exp(al*t)*q)
        zero('contact_endpoints_'+str((order,sign)),F.subs(t,b0)-F.subs(t,a0))
    check('test_nonzero_'+str(order),q.subs(t,(a0+b0)/2)!=0)

# Plateaux and the original fixed-q costs.
Xr,AA=s.symbols('Xr AA',positive=True) # Xr=sqrt(m)
zero('plateau_pole_left_endpoint',2*AA*((1-1/Xr)+(Xr-1))-2*AA*(Xr-1/Xr))
zero('plateau_pole_right_endpoint',2*AA*((1-1/Xr)*Xr+(Xr-1)/Xr)-2*AA*(Xr-1/Xr))
for ep in [Fraction(1,40),Fraction(1,64),Fraction(1,100)]:
    q=ep.denominator//ep.numerator+3
    powers=[Fraction(1,2)+ep*(Fraction(1,2)-q),ep*(1-q),ep*(Fraction(3,2)-q),1+ep*(Fraction(1,2)-q)]
    for j,v in enumerate(powers):
        check('original_P_fixed_q_'+str((ep,j)),v<0)

out={
    'status':'EXACT_LOCAL_ALGEBRA_ONLY_NOT_ASYMPTOTIC_OR_SPECTRAL_CERTIFICATION',
    'sympy_version':s.__version__,
    'check_count':len(checks),'checks':checks,
    'planted_failure_count':len(planted),'planted_failures_detected':planted,
    'source_spectra_computed':False,'hypothetical_zero_values_assigned':False,
    'lean_runs':0,'arb_runs':0,'independent_review':'NOT_RUN',
    'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'registration_sha256':hashlib.sha256((ROOT/'registration.json').read_bytes()).hexdigest()
}
(ROOT/'exact_results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out,ensure_ascii=False,indent=2))
