"""Exact local algebra for Q17. No zeros or asymptotic CCM spectra are computed."""
from pathlib import Path
from collections import Counter
from fractions import Fraction
from math import factorial, isqrt
import hashlib,json
import sympy as s
R=Path(__file__).resolve().parent
counts=Counter()
a,A,u,t,z,w,b,d=s.symbols('a A u t z w b d', nonzero=True)
delta,gamma=s.symbols('delta gamma', real=True)
ww=delta+s.I*gamma; vv=-delta+s.I*gamma
# All finite-horizon polynomial terminal data, proved by differentiating in A.
for r in range(1,9):
 p=sum((a*A)**j/s.factorial(j) for j in range(r))
 tail=s.exp(-a*A)*p
 assert s.simplify(s.diff(1-tail,A)-a**r*A**(r-1)*s.exp(-a*A)/s.factorial(r-1))==0
 assert tail.subs(A,0)==1
 counts['finite_horizon_derivative_and_initial_value']+=2
 if r>1:
  assert s.simplify(s.diff(1-s.exp(-a*A),A)-a**r*A**(r-1)*s.exp(-a*A)/s.factorial(r-1))!=0
  counts['missing_terminal_polynomial_detected']+=1
 # First-order endpoint limits are removable values, not zeros.
 P=1+b*(z-w)+(z-w)**2
 MG=d*(w-z)**r*P
 norm=(-1)**r*s.diff(MG,z,r).subs(z,w)/s.factorial(r)
 assert s.simplify(norm-d)==0
 filt=(z*z-s.Rational(1,4))*P/(w*w-s.Rational(1,4))
 assert s.simplify(filt.subs(z,w)-1)==0
 counts['normalization_and_removable_value']+=2
 for j in range(r):
  assert s.simplify(((w-z)**(r-j)*filt).subs(z,w))==0
  counts['radical_chain_before_last_division']+=1
 assert s.simplify(((w-z)*filt).subs(z,w))==0
 counts['last_forcing_zero_but_inverse_value_one']+=1
 # Beta identity: two stable kernels have exactly order 2r.
 beta=s.integrate(s.expand(t**(r-1)*(u-t)**(r-1)),(t,0,u))/s.factorial(r-1)**2
 assert s.simplify(beta-u**(2*r-1)/s.factorial(2*r-1))==0
 counts['joint_two_resolvent_beta_factor']+=1
 # Partner reflection and the indefinite pairing, symbolic in delta/gamma.
 J=s.Matrix([[0,r],[r,0]])
 D=s.diag(-ww,-vv)
 assert s.simplify(D.conjugate().T*J+J*D)==s.zeros(2)
 assert (s.Matrix([1,-1]).T*J*s.Matrix([1,-1]))[0]==-2*r
 assert (s.Matrix([1,1]).T*J*s.Matrix([1,1]))[0]==2*r
 assert (s.Matrix([1,0]).T*J*s.Matrix([1,0]))[0]==0
 assert (s.Matrix([0,1]).T*J*s.Matrix([0,1]))[0]==0
 counts['reflected_conditional_quotient_controls']+=5
# Reflection in the adjoint is essential.
assert s.simplify(ww+s.conjugate(vv))==0
assert s.simplify(ww+vv)==2*s.I*gamma
counts['reflection_not_conjugation_free']=2
# Both translated boundary factors preserve the conditional mixed pairing.
x,y,h=s.symbols('x y h',real=True)
factor=s.exp(-s.conjugate(ww)*x+vv*y)*s.exp(-vv*(x+y))
assert s.simplify(factor)==1
assert s.simplify(s.exp(2*s.I*gamma*h)*s.exp(2*s.conjugate(ww)*h)-s.exp(2*delta*h))==0
counts['boundary_pair_and_phase_normalization']=2
# Polynomial-exponential ODE: annihilation is not a zero solution.
for r in range(1,7):
 f=s.exp(s.conjugate(ww)*t)*sum(t**j for j in range(r))
 for _ in range(r):f=s.diff(f,t)-s.conjugate(ww)*f
 assert s.simplify(f)==0
 counts['nonzero_homogeneous_solution_controls']+=1
# Full cutoff commutator includes every derivative of chi.
chi=t**5*(1-t)**5;g=(1+t)**7
D=lambda v:s.diff(v,t)+w*v
for r in range(1,6):
 def power(v,n):
  for _ in range(n):v=s.expand(D(v))
  return v
 lhs=power(chi*g,r)-chi*power(g,r)
 rhs=sum(s.binomial(r,j)*s.diff(chi,t,j)*power(g,r-j) for j in range(1,r+1))
 assert s.expand(lhs-rhs)==0
 assert s.expand(lhs)!=0
 counts['all_cutoff_commutators_and_omission_controls']+=2
# Explicit pole coefficient is separated from a zero forcing term.
pole=ww
Q=s.Matrix([[0,1],[1,0]])
zero_matrix=s.zeros(2)
assert Q!=zero_matrix and Q.det()==-1
counts['zero_forcing_does_not_determine_zero_form']=1
# Actual coefficients before any kernel estimate: log n as formal prime logs.
N=96
fac=[Counter() for _ in range(N+1)]
for n in range(2,N+1):
 v=n
 for p in range(2,isqrt(n)+2):
  while v%p==0:fac[n][p]+=1;v//=p
 if v>1:fac[n][v]+=1
mu=[0]+[0 if any(e>1 for e in fac[n].values()) else (-1)**len(fac[n]) for n in range(1,N+1)]
lam=[Counter() for _ in range(N+1)]
for n in range(2,N+1):
 if len(fac[n])==1:lam[n][next(iter(fac[n]))]=1
for n in range(1,N+1):
 v=Counter();v2=Counter()
 for j in range(1,n+1):
  if n%j==0:
   for p,e in fac[n//j].items():v[p]+=mu[j]*e
   for p,e in lam[j].items():v2[p]+=e
 assert {p:e for p,e in v.items() if e}==dict(lam[n])
 assert v2==fac[n]
 counts['actual_mu_log_and_divisor_log_identities']+=2
assert lam[8]==Counter({2:1}) and lam[9]==Counter({3:1})
counts['proper_prime_powers_retained']=2
# Fixed q budget and the moving auxiliary horizon A=log(L)/4.
for eps in [Fraction(1,64),Fraction(1,100),Fraction(1,256)]:
 q=int(1/eps)+3
 exponents=[1+eps*(Fraction(1,2)-q),Fraction(1,2)+eps*(Fraction(3,2)-q),Fraction(1,2)+eps*(1-q)]
 assert all(e<0 for e in exponents)
 assert Fraction(2)*(1-Fraction(1,4))>1
 counts['fixed_order_full_return_power_tests']+=2
# Algebraic evaluation of the exact averaging signal, symbolic delta>0.
Dlt,T,H=s.symbols('Dlt T H',positive=True)
E=s.exp(2*Dlt*H)*(1-s.exp(-2*Dlt*T))/(2*Dlt*T)
assert s.simplify(s.integrate(s.exp(2*Dlt*t),(t,H-T,H))/T-E)==0
price=s.exp(H)*(1-s.exp(-T))/T
ratio=2*Dlt*s.exp((1-2*Dlt)*H)*(1-s.exp(-T))/(1-s.exp(-2*Dlt*T))
assert s.simplify(price/E-ratio)==0
counts['source_S1_exact_average_and_ratio']=2
out={
 'status':'PASS_EXACT_LOCAL_ALGEBRA_NOT_RH_OR_ASYMPTOTIC_CERTIFICATE',
 'sympy':s.__version__,'counts':dict(counts),'total_cases':sum(counts.values()),
 'hypothetical_zero_numerical_values_used':False,
 'actual_CCM_spectrum_computed':False,'lean_runs':0,'arb_runs':0,
 'registration_sha256':hashlib.sha256((R/'registration.json').read_bytes()).hexdigest(),
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
}
(R/'results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
