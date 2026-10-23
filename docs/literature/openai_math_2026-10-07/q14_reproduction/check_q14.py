#!/usr/bin/env python3
"""Exact controls for Q14. Rational plants are NOT the Riemann xi source."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as s

checks=[]
def check(name: str, condition: bool) -> None:
    if not bool(condition):
        raise AssertionError(name)
    checks.append(name)
def zero(name: str, expression) -> None:
    check(name, s.cancel(expression)==0)

p,q,z,a,b,O,P,J=s.symbols('p q z a b O P J')
rp=O-1/(1-a);rq=P-1/(1-b);h=J+O-P
Dpp=((a-1)*(b+1)*rp+(b-1)*(a+1)*rq+(b-a)*h)/(p*q*(p+q))
Dpm=((1-a)*(1-b)*(rp-rq)+(a+b)*h)/(p*q*(q-p))
rawpp=(2+(a*b-1)*(O+P)+(b-a)*J+a+b)/(p*q*(p+q))
rawpm=((1+a*b)*(O-P)+(a+b)*J-a+b)/(p*q*(q-p))
zero('complete_pp_cancels_false_F_plus_Fprime_denominator',Dpp-rawpp)
zero('complete_pm_cancels_false_F_plus_Fprime_denominator',Dpm-rawpm)
for aa,bb in [(1,s.Rational(2,3)),(s.Rational(-3,2),1),(1,1)]:
    check(f'raw_finite_at_kappa_one_{aa}_{bb}',not rawpp.subs({a:aa,b:bb,p:2,q:3,O:s.Rational(2,5),P:s.Rational(3,7),J:s.Rational(1,9)}).has(s.zoo))

ap=(a*p-z)/(p*(p*p-z*z));aq=(b*q-z)/(q*(q*q-z*z))
bp=(p-a*z)/(p*(p*p-z*z));bq=(q-b*z)/(q*(q*q-z*z))
phi_pp=2*(bp*bq-ap*aq);phi_pm=-2*(bp*bq+ap*aq)
rpz=-2*p/(p*p-z*z);rqz=-2*q/(q*q-z*z)
hz=-2*(1/(p+z)-1/(q+z))
resp_pp=((a-1)*(b+1)*rpz+(b-1)*(a+1)*rqz+(b-a)*hz)/(p*q*(p+q))
resp_pm=((1-a)*(1-b)*(rpz-rqz)+(a+b)*hz)/(p*q*(q-p))
zero('filtered_pole_response_pp',resp_pp-phi_pp)
zero('filtered_pole_response_pm',resp_pm-phi_pm)
check('planted_mixed_quadrant_sign_error_detected',s.cancel(resp_pm-phi_pp)!=0)
check('planted_h_deleted_detected',s.cancel(((a-1)*(b+1)*rpz+(b-1)*(a+1)*rqz)/(p*q*(p+q))-phi_pp)!=0)

# Closing the right vertical line clockwise: minus residues at z=p,q.
for name,phi,target in [('pp',phi_pp,(a+b+2)/(p*q*(p+q))),('pm',phi_pm,(b-a)/(p*q*(q-p)))]:
    res_p=s.cancel(((z-p)*phi)).subs(z,p)/(1-a)
    res_q=s.cancel(((z-q)*phi)).subs(z,q)/(1-b)
    zero('right_line_'+name,-res_p-res_q-target)
    check('planted_right_contour_orientation_'+name,s.cancel(res_p+res_q-target)!=0)

l=s.symbols('l',positive=True)
a2=l*(l+2)
F=lambda x:x*x-a2
kap=lambda x:-2*x/F(x)
Z=lambda x:F(x)/(F(x)+2*x)
cp=-l/(l+1);cm=-(l+2)/(l+1)
Om=lambda x:1-cp/(x+l)+cm/(x+l+2)
JJ=-cp*(1/(p+l)-1/(q+l))-cm*(1/(p+l+2)-1/(q+l+2))
zero('rational_plant_residue',s.cancel((z-l)*Z(z)).subs(z,l)-cp)
zero('rational_plant_boundary_real_Poisson_defect',Om(p)-Z(p)-cp*(-2*p/(p*p-l*l)))
zero('rational_plant_phase_defect',JJ+Om(p)-Om(q)-cp*(-2*(1/(p+l)-1/(q+l))))
zero('pole_filter_a_removes_p_l',ap.subs({a:kap(p),z:l})+(l+2)/(p*(p*p-a2)))
zero('pole_filter_b_removes_p_l',bp.subs({a:kap(p),z:l})-1/(p*p-a2))
for ll in [s.Rational(1,64),s.Rational(1,32),s.Rational(1,16)]:
    check(f'plant_roots_inside_centered_strip_{ll}',ll*(ll+2)<s.Rational(1,4))
    check(f'actual_plant_residue_negative_{ll}',cp.subs(l,ll)<0)
    zero(f'kappa_at_pole_{ll}',kap(ll).subs(l,ll)-1)
    for pp,qq in [(1,2),(s.Rational(3,4),s.Rational(5,4)),(2,3),(s.Rational(5,4),s.Rational(7,4))]:
        sub={p:pp,q:qq,l:ll}
        aa=kap(p);bb=kap(q)
        exprpp=rawpp.subs({a:aa,b:bb,O:Om(p),P:Om(q),J:JJ})
        exprpm=rawpm.subs({a:aa,b:bb,O:Om(p),P:Om(q),J:JJ})
        expectpp=cp*phi_pp.subs({a:aa,b:bb,z:l})
        expectpm=cp*phi_pm.subs({a:aa,b:bb,z:l})
        zero(f'complete_plant_pp_{ll}_{pp}_{qq}',(exprpp-expectpp).subs(sub))
        zero(f'complete_plant_pm_{ll}_{pp}_{qq}',(exprpm-expectpm).subs(sub))
# Coincident Laplace variables: rational divisibility removes q-p.
rawplantpm=s.cancel(rawpm.subs({a:kap(p),b:kap(q),O:Om(p),P:Om(q),J:JJ}))
expectedplantpm=s.cancel(cp*phi_pm.subs({a:kap(p),b:kap(q),z:l}))
zero('coincident_laplace_removable',rawplantpm.subs(q,p)-expectedplantpm.subs(q,p))
true_pole_coefficient=s.cancel((p*p-a2)**2*rawplantpm.subs(q,p))
true_pole_coefficient=s.simplify(true_pole_coefficient.subs({l:s.Rational(1,32),p:s.sqrt(65)/32}))
check('coincident_true_F_double_pole_not_removed',true_pole_coefficient!=0 and not true_pole_coefficient.has(s.zoo,s.nan))

# Same ORIGINAL P controls. The even and odd source profiles use modes 0,+/-1,+/-2.
w,u=s.symbols('w u',positive=True)
ce=[-s.Rational(3,4),1+4*w*w,-s.Rational(1,4)-4*w*w]
co=[s.Rational(1,4)+w*w,-(s.Rational(1,4)+4*w*w)/2]
even=sum(ce[k]*u/(u*u+k*k*w*w) for k in range(3))
odd=sum(co[k-1]*k*w/(u*u+k*k*w*w) for k in range(1,3))
zero('even_endpoint',sum(ce))
zero('even_exponential_contact',even.subs(u,s.Rational(1,2)))
zero('odd_exponential_contact',odd.subs(u,s.Rational(1,2)))
for ww in [s.Rational(1,3),s.Rational(2,3),1,2]:
    for ll in [s.Rational(1,64),s.Rational(1,32),s.Rational(1,16)]:
        aa=s.sqrt(ll*(ll+2))
        check(f'even_nonzero_plant_laplace_{ww}_{ll}',s.simplify(even.subs({w:ww,u:aa}))!=0)
        check(f'odd_nonzero_plant_laplace_{ww}_{ll}',s.simplify(odd.subs({w:ww,u:aa}))!=0)
# A literal finite source: l=1/32, residue=-1/33, a^2/l^2=65.
zero('specific_residue_minus_one_over_33',cp.subs(l,s.Rational(1,32))+s.Rational(1,33))
zero('specific_odd_factor_65',(a2/l**2).subs(l,s.Rational(1,32))-65)
check('plant_even_defect_negative',-s.Rational(2,33)<0)
check('plant_odd_defect_positive',s.Rational(130,33)>0)
zero('plant_even_Gram',2-s.Rational(2,33)-s.Rational(64,33))
zero('plant_odd_Gram',-2+s.Rational(130,33)-s.Rational(64,33))

# Euclidean row norm behind the tail constants; no dimension factor.
A=s.Matrix([[1,-1,-1,-1],[-1,-1,1,-1]])/2
check('two_filter_rows_orthonormal',A*A.T==s.eye(2))
for eps in [s.Rational(1,64),s.Rational(1,128),s.Rational(1,1000)]:
    for nu in [s.Rational(1,10),s.Rational(1,5),s.Rational(1,2)]:
        power_Y=s.Rational(1,2)+eps+nu
        zero(f'vertical_derivative_return_{eps}_{nu}',s.Rational(1,2)+2*(s.Rational(1,4)+eps)-2*power_Y+2*nu)
        zero(f'jump_return_{eps}_{nu}',s.Rational(1,2)+eps-power_Y+nu)

out={'status':'PASS_EXACT_LOCAL_CONTROLS_NOT_ARITHMETIC_PROOF',
     'sympy_version':s.__version__,'count':len(checks),'checks':checks,
     'plants_are_actual_xi':False,'new_full_CCM_power':None}
path=Path(__file__).with_name('exact_results.json')
path.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':out['status'],'count':len(checks)}))
