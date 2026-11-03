"""Independent primitive interval bound calculator; imports no source generator."""
from pathlib import Path
import json,math
import mpmath as m
v=m.iv;v.dps=90;m.mp.dps=100
L=v.log(3);a=L/2;T=v.mpf(40);n=61;epsilon=v.mpf(2)**-90
D=math.factorial(2*n+1)//(2**n*math.factorial(n))
def envelope(x,prefactor):
 ratio=x*x/((2*n+1)*(2*n+3));assert ratio<1
 return prefactor*(2*n+1)*x**(2*n)/(D*D*(1-ratio))
tau=envelope(T*a,L);tau_p=envelope(a/2,2*L*v.exp(a))
assert tau<v.mpf(2)**-132 and tau_p<v.mpf(2)**-700
band=(8*T/v.pi)*(2*v.sqrt(L*tau)+tau)
poles=8*v.sqrt(tau_p)+2*tau_p
# Independent complex-ellipse estimate from absolute convergent digamma series.
digamma=1+8+22*v.pi**2/6
assert digamma<53
Y=v.mpf(3)/16
symbol=digamma+v.log(v.pi)+2*v.log(2)/v.sqrt(2)*(v.exp(v.log(2)*Y)+v.exp(-v.log(2)*Y))/2+v.mpf(4)/5
vector2=L*v.exp(2*a*Y)
operator_envelope=symbol*vector2
assert operator_envelope<512
# Conservative actual perturbation algebra, independent of final rounded budget.
eta=8*epsilon
per_node=4*(4*eta+eta*eta)+epsilon*(2+eta)**2
pole_round=4*eta+eta*eta
assert per_node<1000*epsilon and pole_round<1000*epsilon
fmt=lambda x:[m.mp.nstr(m.mp.mpf(x._mpi_[i]),60) for i in (0,1)]
rows=[]
for order in [40,48]:
 gauss=8*T*512/(v.pi*2**(2*order));rounding=1000*(80*order+1)*epsilon;matrix=v.mpf(61)/2**80
 total=band+poles+gauss+rounding+matrix
 assert total<v.mpf(2)**-40
 rows.append(dict(Q=order,band=fmt(band),poles=fmt(poles),gauss=fmt(gauss),scalar_round=fmt(rounding),matrix_round=fmt(matrix),total=fmt(total),total_lt_2pow_minus40=True))
out=dict(primitive_interval_dps=90,tail=fmt(tau),pole_tail=fmt(tau_p),digamma_ellipse_bound=fmt(digamma),matrix_integrand_bound=fmt(operator_envelope),per_node_rounding=fmt(per_node),SOS_scalar_identity='kappa I + (G-2kappa I)P +(beta-2kappa)Q +(kappa I+E) = PGP+beta Q+E',runs=rows)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
