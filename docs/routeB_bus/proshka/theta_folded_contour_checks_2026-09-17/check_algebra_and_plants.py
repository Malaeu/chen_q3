"""Exact rational constants; separate non-rigorous mpmath identity controls."""
from fractions import Fraction as Q
from pathlib import Path
import json
import sympy as sp
import mpmath as mp
from check_contour import ray, head, source_atom, reference_xi

out={}
# No floating-point comparisons in the rational constant checks.
D_bound=36*(1+Q(1,16)+Q(2,81))/Q(157,50)**2
assert D_bound<4
assert 64*Q(22,7)+30<256
assert 256*Q(7,4)==448
assert 16*4*448==28672
assert 8*28672==229376
assert 8*229376==1835008
assert 1835008<2**24
out['rational_constants']={'D_rational_upper':str(D_bound),'D_less_than_4':True,'tail_factor':448,'H_factor':28672,'scheduled_H_factor':229376,'schedule_aux_factor':1835008}
b=sp.symbols('b', positive=True)
u=sp.symbols('u', positive=True)
for k in (2,3):
    antideriv=sp.exp(-b*u)*sum(sp.factorial(k)/sp.factorial(k-j)*u**(k-j)/b**(j+1) for j in range(k+1))
    assert sp.simplify(sp.diff(antideriv,u)+u**k*sp.exp(-b*u))==0
out['incomplete_gamma_majorant_antiderivatives']='EXACT_SYMBOLIC_PASS'

mp.mp.dps=65
p=mp.mpf(1)/4+10j;theta=mp.mpf(1)/4;N=1
realhead=head(p,mp.mpf(0),N)
shifthead=head(p,theta,N)
def integrand(y):
    z=1j*y
    return 1j*(source_atom(z,1)-source_atom(-z,1))*mp.exp(p*z)
vertical=mp.quad(integrand,[0,theta])
assert abs((realhead-shifthead)-vertical)<mp.mpf('1e-58')
assert abs(realhead-shifthead)>mp.mpf('1e-8')
out['seam_identity_diagnostic']={'error':mp.nstr(abs(realhead-shifthead-vertical),24),'defect_absolute_value':mp.nstr(abs(vertical),24),'omitting_defect_rejected':True}
T=20;theta=mp.pi/4-1/mp.mpf(T+1);c=mp.cos(2*theta);M=int(mp.ceil(mp.sqrt(40/c)));N=M-1;p=mp.mpf(1)/4+T*1j
wrong=mp.fsum(ray(n,p,theta)+ray(n,-p,theta) for n in range(1,N+1))
B=448*M**3/c*mp.exp(-mp.pi*c*M*M)*mp.exp(-theta*T)
wrong_error=abs(wrong-reference_xi(p))
assert wrong_error>B
out['wrong_ray_plant']={'error':mp.nstr(wrong_error,24),'claimed_correct_formula_error_bound':mp.nstr(B,24),'rejected':True}
out['warning']='mpmath controls are diagnostics, not interval certificates; zero printed errors are not proofs of equality.'
path=Path(__file__).parent/'algebra_and_plants.json';path.write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
