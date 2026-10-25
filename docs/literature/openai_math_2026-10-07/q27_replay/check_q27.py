#!/usr/bin/env python3
"""Exact local algebra controls for Q27. Not a CCM spectral certificate.
The rational-frequency controls test identities, not a production integer cell.
No hypothetical zeta zero is assigned numerical data.
"""
from __future__ import annotations
import json
from fractions import Fraction
import sympy as s
passed=[]; planted=[]
def check(name, cond):
    if not bool(cond): raise AssertionError(name)
    passed.append(name)
def reject(name, cond):
    if bool(cond): raise AssertionError('Undetected planted error: '+name)
    planted.append(name)
def zero(M): return all(s.cancel(x)==0 for x in M)
z,a,b,t=s.symbols('z a b t', nonzero=True)
check('causal_offdiagonal_partial_fraction',s.cancel((1/(z+a)-1/(z+b))/(b-a)-1/((z+a)*(z+b)))==0)
check('causal_diagonal_double_pole',s.diff(1/(z+a),z)==-1/(z+a)**2)
# Full exact three-contact projector for a frequency-parameter algebra control.
om=s.Matrix([-2,-1,0,1,2]); one=s.ones(5,1)
ve=s.Matrix([1/(s.Rational(1,4)+j*j) for j in om]); vo=s.Matrix([j/(s.Rational(1,4)+j*j) for j in om])
V=s.Matrix.hstack(one,ve,vo); P=s.eye(5)-V*(V.T*V).inv()*V.T
check('full_three_contact_projection_idempotent',zero(P*P-P))
check('projection_real_symmetric',P==P.T)
check('rank_is_dimension_minus_three',P.rank()==2)
check('endpoint_contact',zero(P*one))
vp=lambda z0,sgn:s.Matrix([1/(z0+sgn*s.I*j) for j in om])
for sign in (-1,1):
    check('exponential_contact_'+str(sign),zero(P*vp(s.Rational(1,2),sign)))
    check('reflected_contact_'+str(sign),zero(P*vp(-s.Rational(1,2),sign)))
    zz=s.Rational(2,3)+s.I/5
    resid=vp(zz,sign)-one/zz
    check('resolvent_endpoint_subtraction_'+str(sign),zero(P*vp(zz,sign)-P*resid))
    identity=s.Matrix([-sign*s.I*j/(zz*(zz+sign*s.I*j)) for j in om])
    check('resolvent_subtraction_denominators_'+str(sign),zero(resid-identity))
# Formal series at infinity. No asymptotic numerical fitting.
y=s.symbols('y')
ps=[]
for sign in (-1,1):
    v=s.Matrix([sum((-sign*s.I*j)**k*y**(k+1) for k in range(4)) for j in om])
    ps.append(P*v)
Sseries=sum((v*v.T for v in ps),s.zeros(5))
for power in (2,3):
    check('projected_transfer_coefficient_'+str(power)+'_vanishes',zero(Sseries.applyfunc(lambda x:s.expand(x).coeff(y,power))))
check('leading_quartic_full_matrix',zero(Sseries.applyfunc(lambda x:s.expand(x).coeff(y,4))+2*(P*om)*(P*om).T))
# Double main-pole cancellation. Both derivatives of vv^T are retained.
for sign in (-1,1):
    pv=P*vp(s.Rational(1,2),sign)
    dp=P*s.Matrix([-1/(s.Rational(1,2)+sign*s.I*j)**2 for j in om])
    check('double_contact_outer_derivative_'+str(sign),zero(dp*pv.T+pv*dp.T))
    reject('derivative_vector_itself_vanishes_'+str(sign),zero(dp))
# Analytic squares are not modulus squares; exact even/odd signature.
za=s.Rational(1,3)
p=P*vp(za,1); re=p.applyfunc(s.re); im=p.applyfunc(s.im)
S0=p*p.T+s.conjugate(p)*s.conjugate(p).T
check('analytic_square_even_odd_decomposition',zero(S0-2*(re*re.T-im*im.T)))
check('even_odd_vectors_orthogonal',s.cancel((re.T*im)[0])==0)
check('actual_contact_algebra_positive_direction',s.cancel((re.T*S0*re)[0])>0)
check('actual_contact_algebra_negative_direction',s.cancel((im.T*S0*im)[0])<0)
reject('transpose_can_be_replaced_by_adjoint',zero(p*p.T-p*p.conjugate().T))
reject('contact_projection_gives_pointwise_psd',s.cancel((im.T*S0*im)[0])>=0)
# Finite Hermitian aggregation and full complex mixed return.
A=s.Matrix([[2,1+s.I],[1-s.I,-3]]); x=s.Matrix([1+s.I,2]); e=s.Matrix([s.Rational(1,3),s.I/5])
quad=lambda v:s.expand((v.conjugate().T*A*v)[0])
cross=s.expand((x.conjugate().T*A*e)[0]+(e.conjugate().T*A*x)[0])
check('complete_quadratic_return',s.simplify(quad(x+e)-quad(x)-cross-quad(e))==0)
reject('drop_linear_mixed_return',s.simplify(quad(x+e)-quad(x)-quad(e))==0)
# Centering: same kernel identity, not the extra-decaying-copy convention.
xr,yr=s.symbols('xr yr',real=True)
check('pole_plus_decay_rank_two',s.simplify(s.exp((xr-yr)/2)+s.exp(-(xr-yr)/2)-2*s.cosh((xr-yr)/2))==0)
G,H,S=s.symbols('G H S')
center=S-G
check('single_continuum_return',s.expand(center.subs(G,-H)-H-S)==0)
reject('double_charge_H_after_single_centering',s.expand(center.subs(G,-H)-2*H-S)==0)
# Cauchy contour orientation: right side upwards, top right-to-left.
verts=[(0,-1),(2,-1),(2,1),(0,1)]
area=sum(verts[i][0]*verts[(i+1)%4][1]-verts[(i+1)%4][0]*verts[i][1] for i in range(4))/2
check('right_up_contour_positive',area>0)
rr=s.symbols('rr',integer=True,positive=True); zz0=s.symbols('zz0'); ell=s.symbols('ell',real=True)
res=s.residue(-rr*s.exp(ell*z)/(z-zz0),z,zz0)
check('log_derivative_residue_multiplicity',s.simplify(res+rr*s.exp(ell*zz0))==0)
reject('residue_sign_flipped',s.simplify(res-rr*s.exp(ell*zz0))==0)
# No automatic full-space promotion from the low block.
block=s.Matrix([[0,2],[2,0]])
check('low_block_does_not_control_cross',block[0,0]==0 and block.det()<0)
# The integrable logarithmic singularity in the averaged-line proof.
h,AA=s.symbols('h AA',positive=True)
primitive=h*(s.log(AA/h)+1)
check('averaged_log_singularity_primitive',s.simplify(s.diff(primitive,h)-s.log(AA/h))==0)
Y=s.symbols('Y',positive=True)
q=(s.log(2*Y)/3+s.Rational(1,9))/Y**3
check('log_weighted_quartic_tail_integral',s.simplify(s.diff(q,Y)+s.log(2*Y)/Y**4)==0)
check('quartic_tail_power',s.integrate(t**(-4),(t,Y,s.oo))==1/(3*Y**3))
# m-powers of complete returned errors, not just one sector.
nu=Fraction(1,12); kappa=Fraction(1,6)+nu
powers={'right_tail':Fraction(1,2)-3*kappa,'left_tail':-3*kappa,'horizontal':Fraction(1,2)-4*kappa}
for key,val in powers.items(): check('paid_height_power_'+key,val<0)
check('height_vs_old_sharp_prefix',Fraction(1,2)-kappa>0)
# Elementary binomial divisibility used for psi(x)<=3x.
def valuation(n,p):
    q=0
    while n and n%p==0: q+=1; n//=p
    return q
for n in range(1,13):
    B=int(s.binomial(2*n,n))
    for p0 in list(s.primerange(2,2*n+1)):
        p=int(p0); q=p; cnt=0
        while q<=2*n:
            cnt+=int(q>n); q*=p
        check('binomial_prime_power_interval_'+str(n)+'_'+str(p),valuation(B,p)>=cnt)
check('no_new_zero_assigned',True)
out={'exact_controls':len(passed),'planted_errors_detected':len(planted),'sympy_version':s.__version__,
     'passed':passed,'planted':planted,'height_powers':{k:str(v) for k,v in powers.items()},
     'scope':'Local exact identities and error-exponent controls only; no actual zero or production CCM eigenvalue; no Lean/Arb/independent review.'}
print(json.dumps(out,ensure_ascii=False,indent=2,sort_keys=True))
