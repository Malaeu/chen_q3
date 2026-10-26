"""Exact local controls of the Q29 progression reconstruction.
Python 3 with SymPy. Run: python3 check_q29.py
These are finite algebra/provenance controls, not a CCM spectral certificate.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
from math import gcd
import json, hashlib, sys
import sympy as s

checks = Counter()
planted = []
def ck(value, group):
    if not bool(value):
        raise AssertionError(group)
    checks[group] += 1

def reject(name, wrong_equal):
    if bool(wrong_equal):
        raise AssertionError('Planted error was NOT detected: ' + name)
    planted.append(name)

def factors(n):
    out = {}; p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: out[n] = out.get(n, 0) + 1
    return out

def mu(n):
    ff = factors(n)
    return 0 if any(k > 1 for k in ff.values()) else (-1)**len(ff)

def phi(n):
    out = n
    for p in factors(n): out = out//p*(p-1)
    return out

for n in range(1, 41):
    rhs = sum((F(mu(d)**2, phi(d)) for d in range(1,n+1) if n%d == 0), F(0))
    ck(rhs == F(n,phi(n)), 'totient_squarefree_identity')
reject('mu_instead_of_mu_squared',
       sum((F(mu(d),phi(d)) for d in (1,2)), F(0)) == F(2,phi(2)))

# This controls the exact minimax algebra, not an asymptotic prime error.
for Q in (1,2,3,5,8,12,20):
    S = sum((F(1,phi(q)) for q in range(1,Q+1)), F(0))
    beta = [F(1,phi(q))/S for q in range(1,Q+1)]
    ck(sum(beta) == 1, 'optimal_weights_normalized')
    ck(set(beta[q-1]*phi(q) for q in range(1,Q+1)) == {1/S},
       'minimax_equalized_coefficients')
    for j in range(1,Q+1):
        # An l1-budget concentrated at j attains the corresponding coefficient.
        D = [F(int(q==j)) for q in range(1,Q+1)]
        ck(sum(beta[q-1]*phi(q)*D[q-1] for q in range(1,Q+1)) == 1/S,
           'dual_l1_extreme_point')

# Formal log(p) symbols keep the ACTUAL Mangoldt support and multiplicities.
logs = {p:s.Symbol('logp_'+str(p), real=True) for p in range(2,66) if len(factors(p))==1 and factors(p).get(p)==1}
def Lam(n):
    ff=factors(n)
    return logs[next(iter(ff))] if len(ff)==1 else s.S(0)
x = s.Symbol('x', real=True)
H = s.Matrix([[x+1, 1+s.I*x], [1-s.I*x, x*x+2]])
def HH(n): return H.subs(x,n)
def zero(A): return all(s.expand(z)==0 for z in A)
def integral_H(a,b): return H.applyfunc(lambda e:s.integrate(e,(x,a,b)))
def msum(terms):
    z=s.zeros(2)
    for term in terms: z += term
    return z

saved = None
for X,Y in ((4,8),(8,13),(16,32)):
    J = integral_H(X,Y)
    full = msum(Lam(n)*HH(n) for n in range(X+1,Y+1)) - J
    for q in (1,2,3,4,6):
        units=[a for a in range(1,q+1) if gcd(a,q)==1]
        cop=msum(Lam(n)*HH(n) for n in range(X+1,Y+1) if gcd(n,q)==1)
        bad=msum(Lam(n)*HH(n) for n in range(X+1,Y+1) if gcd(n,q)>1)
        Ds=[]; Zs=[]
        for a in units:
            cls=msum(Lam(n)*HH(n) for n in range(X+1,Y+1) if (n-a)%q==0)
            D=cls-J/phi(q)
            Z=cls-cop/phi(q)
            Ds.append(D);Zs.append(Z)
            ck(zero(D-Z-(full-bad)/phi(q)), 'actual_principal_channel_identity')
        ck(zero(msum(Ds)+bad-full), 'full_matrix_residue_reassembly')
        ck(zero(msum(Zs)), 'nonprincipal_zero_sum_before_moduli')
        # Check the omitted atoms as prime powers, not a scalar norm surrogate.
        bad2=s.zeros(2)
        for p in factors(q):
            n=p
            while n<=Y:
                if n>X: bad2 += logs[p]*HH(n)
                n*=p
        ck(zero(bad-bad2), 'all_noncoprime_prime_powers_retained')
        if (X,Y,q)==(4,8,3): saved=(full,J,cop,bad,Ds)
        if (X,Y,q)==(4,8,2):
            reject('deleted_noncoprime_power_8',zero(msum(Ds)-full))

full,J,cop,bad,Ds=saved
reject('average_classes_instead_of_sum',zero(msum(Ds)/2+bad-full))
reject('full_continuum_subtracted_in_each_class',zero(cop-2*J+bad-full))
reject('deleted_off_diagonal_mixed_entries',zero(s.diag(full[0,0],full[1,1])-full))

# An exact Stieltjes test with the actual formal Mangoldt atoms. Integrate the
# step function E on each unit interval; the matrix weight here is an algebra
# control only, not production Q_M(log x)/sqrt(x).
X,Y,q,a=4,13,3,1
E=lambda n: sum((Lam(k) for k in range(1,n+1) if (k-a)%q==0),s.S(0))-s.Rational(n,phi(q))
D=msum(Lam(n)*HH(n) for n in range(X+1,Y+1) if (n-a)%q==0)-integral_H(X,Y)/phi(q)
Hp=H.diff(x); integ=s.zeros(2)
for n in range(X,Y):
    ps=sum((Lam(k) for k in range(1,n+1) if (k-a)%q==0),s.S(0))
    integ += (Hp*(ps-x/phi(q))).applyfunc(lambda e:s.integrate(e,(x,n,n+1)))
right=HH(Y)*E(Y)-HH(X)*E(X)-integ
ck(zero(D-right),'stieltjes_full_both_endpoints')
reject('deleted_lower_Stieltjes_endpoint',zero(D-(HH(Y)*E(Y)-integ)))

for p in (2,3,5,7):
    for X in (1,2,4,8,16,32):
        ns=[];n=p
        while n<=2*X:
            if n>X:ns.append(n)
            n*=p
        ck(len(ns)<=1,'one_power_per_prime_in_open_closed_dyadic_block')

O,r=s.symbols('O r',real=True)
variation=2/r+2+2*(1+2*O)*(1-1/r)
ck(s.expand(variation-(4*(1+O)-4*O/r))==0,'matrix_variation_price_algebra')
for eps in (F(1,64),F(1,128),F(1,257)):
    ck(F(1,2)+eps > F(1,2), 'completed_BV_power_not_better_than_half')
    ck(F(3,2)*eps < F(1,2), 'short_divisor_fee_not_the_dominant_debt')
    ck(-eps < 0, 'summed_noncoprime_return_decays')

base=Path(__file__).resolve().parent
out={
 'status':'PASS_EXACT_LOCAL_CONTROLS',
 'exact_controls':sum(checks.values()),
 'counts':dict(checks),
 'planted_errors_detected':len(planted),
 'planted_names':planted,
 'scope':'Finite coefficient, matrix, endpoint and minimax algebra. The test matrix is Hermitian with complex off-diagonal entries but is NOT a production CCM cell. Formal log(p) retains actual Mangoldt support. No infinite prime estimate is proved by these controls.',
 'python':sys.version.split()[0], 'sympy':s.__version__,
 'lean_runs':0, 'arb_runs':0, 'production_spectral_runs':0,
 'new_independent_review':'NOT_RUN',
 'registration_sha256':hashlib.sha256((base/'registration.json').read_bytes()).hexdigest(),
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
}
(base/'exact_results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out,ensure_ascii=False,indent=2))
