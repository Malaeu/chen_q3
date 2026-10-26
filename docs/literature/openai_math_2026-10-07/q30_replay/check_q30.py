"""Exact local controls for Q30. Not a CCM sign or asymptotic certificate.
Run: python3 check_q30.py
Requires the installed SymPy; no installation is performed.
"""
from pathlib import Path
from collections import Counter
import hashlib, json, sys
import sympy as s

counts = Counter()
planted = []

def check(value, name):
    if not bool(value):
        raise AssertionError(name)
    counts[name] += 1

def zero(A):
    return all(s.simplify(x) == 0 for x in A)

def reject(value, name):
    if bool(value):
        raise AssertionError('Planted error escaped: ' + name)
    planted.append(name)

# Basis-overlap integral: exp(2*pi*i*(j-k-1/2))=-1, no sign ambiguity.
for j,k in [(-2,-1),(0,0),(1,-2),(3,1)]:
    a = s.Rational(2*j-2*k-1, 2)
    integral = (-2)/(2*s.pi*s.I*a)
    formula = 2*s.I/(s.pi*(2*j-2*k-1))
    check(s.simplify(integral-formula)==0, 'half_grid_overlap_sign_and_scale')
reject(s.simplify(-2*s.I/s.pi - 2*s.I/s.pi)==0, 'reversed_H_sign')

# Synthetic finite support geometry. This tests the algebra of wrap and support,
# not a replacement of the continuous original CCM or of its projector.
N = 8
I = s.eye(N)
def T(d):
    A=s.zeros(N)
    for i in range(N-d):
        A[i,i+d]=1
    return A

def W(d):
    A=s.zeros(N)
    for i in range(max(0,N-d),N):
        j=i+d-N
        if 0<=j<N: A[i,j]=1
    return A

for d in [0,1,3,4,7,8]:
    Vp=T(d)+W(d); Vm=T(d)-W(d)
    check(zero((Vp+Vm)/2-T(d)), 'linked_wrap_cancellation')
    check(zero(Vm-Vp+2*W(d)), 'twisted_commutator')
    check(zero(Vp.T*Vp-I), 'periodic_shift_unitary')
    check(zero(Vm.T*Vm-I), 'antiperiodic_shift_unitary')
check(zero(T(N)), 'full_endpoint_zero')
reject(zero((I-I)-2*I), 'even_channel_alone_at_endpoint')
reject(zero((T(3)+W(3))+(T(3)-W(3))-T(3)), 'missing_half_in_link')

# An actual finite positive mixture is used in the proof. Rational weights here
# test its exact identities, not numerical prime data.
jumps=[3,5,7]
p=[s.Rational(1,2),s.Rational(1,3),s.Rational(1,6)]
Ts=[T(d) for d in jumps]
A=sum((w*t for w,t in zip(p,Ts)),s.zeros(N))
q=3
check(zero(A**q), 'collective_nilpotence')
check(not zero(A**(q-1)), 'nontrivial_nilpotent_order')
for a in jumps:
    for b in jumps:
        expected=T(a+b) if a+b<=N else s.zeros(N)
        check(zero(T(a)*T(b)-expected), 'all_ordered_shift_products')

boundary=sum((w*(I-t.T*t) for w,t in zip(p,Ts)),s.zeros(N))
variance=s.zeros(N)
for i in range(len(p)):
    for j in range(len(p)):
        diff=Ts[i]-Ts[j]
        variance+=p[i]*p[j]*diff.T*diff/2
Dgram=boundary+variance
check(zero(Dgram-(I-A.T*A)), 'explicit_boundary_variance_defect')
reject(zero(boundary-(I-A.T*A)), 'deleted_pair_variance')
diag_only=sum((p[i]**2*Ts[i].T*Ts[i] for i in range(len(p))),s.zeros(N))
reject(zero(diag_only-A.T*A), 'deleted_source_mixed_products')

Jgram=sum(((A.T)**j*Dgram*A**j for j in range(q)),s.zeros(N))
check(zero(Jgram-I), 'isometric_telescope')
check(zero(A.T*Jgram*A-(I-Dgram)), 'shifted_isometry_telescope')
# A nilpotent operator generally ceases to be nilpotent under compression.
B=s.Matrix([[0,1],[0,0]])
P=s.ones(2)/2
check(zero(B**2), 'nilpotent_before_projection')
reject(zero((P*B*P)**2), 'inserting_projection_in_products')

# Exact path eigenvector/energy identity; all off-diagonal terms included.
for order in [2,3,4,5]:
    theta=s.pi/(order+1)
    h=s.Matrix([s.sin((j+1)*theta) for j in range(order)])
    Sh=s.zeros(order)
    for j in range(order-1): Sh[j,j+1]=1
    Jpath=Sh+Sh.T
    check(zero(Jpath*h-2*s.cos(theta)*h), 'sine_path_eigenvector')
    G=s.zeros(order)
    for j in range(order-1):
        row=s.zeros(1,order)
        row[0,j]=1/h[j]
        row[0,j+1]=-1/h[j+1]
        G+=h[j]*h[j+1]*(row.T*row)
    check(zero(G-(2*s.cos(theta)*s.eye(order)-Jpath)), 'full_positive_path_defect')
reject(s.simplify(2*s.cos(s.pi/3)-2)==0, 'nilpotence_implies_zero_form')

# Complex mixed form is not an absolute-value or real-vector replacement.
x,y,u,v=s.symbols('x y u v', real=True)
f=s.Matrix([x+s.I*y,u+s.I*v])
form=s.expand((s.conjugate(f).T*(B+B.T)*f)[0])
check(s.simplify(form-2*(x*u+y*v))==0, 'complex_mixed_form')
reject(s.simplify(form-2*x*u)==0, 'deleted_imaginary_cross_sector')

# Exact g and h normalization on the two grids, with a common Green mass.
r0,ro,t=s.symbols('r0 ro t', positive=True)
qmass=s.symbols('qmass', real=True)
gpair=((t-1)*qmass-(t+1)*qmass)/2
hpair=((1-1/t)*qmass+(1+1/t)*qmass)/2
check(s.simplify(gpair+qmass)==0, 'whole_g_returns_negative_Green')
check(s.simplify(hpair-qmass)==0, 'whole_decay_returns_Green')
check(s.simplify(gpair+hpair)==0, 'continuum_rank_two_cancellation')
reject(s.simplify(((t-1)*qmass)-gpair)==0, 'discarded_odd_continuum')

# Actual mu*log arithmetic with formal prime logarithms, no float fitting.
def factor(n):
    ans={}; d=2
    while d*d<=n:
        while n%d==0:
            ans[d]=ans.get(d,0)+1; n//=d
        d+=1
    if n>1: ans[n]=ans.get(n,0)+1
    return ans

def mu(n):
    fs=factor(n)
    if any(k>1 for k in fs.values()): return 0
    return (-1)**len(fs)

for n in [2,3,4,6,8,9,12,16,25,27,30]:
    got={}
    for d in range(1,n+1):
        if n%d: continue
        for p0,e in factor(n//d).items(): got[p0]=got.get(p0,0)+mu(d)*e
    got={p0:e for p0,e in got.items() if e}
    fn=factor(n)
    expected={next(iter(fn)):1} if len(fn)==1 else {}
    check(got==expected,'actual_formal_Mangoldt_weights')

# Exact finite budgets. Wtot includes the upper atom, Wend is its known mass.
Wshort,Wtot,Wend,cost=s.symbols('Wshort Wtot Wend cost',real=True)
Wlong=Wtot-Wend-Wshort
sm=2*Wshort+2*cost*Wlong
check(s.simplify(sm-(2*cost*(Wtot-Wend)+2*(1-cost)*Wshort))==0,'full_budget_reassembly')
for eps in [s.Rational(1,64),s.Rational(1,128),s.Rational(3,200)]:
    order=s.ceiling(1/eps)
    check(order*eps>=1,'fixed_epsilon_nilpotence_order')
    check(s.Rational(3,2)*eps<s.Rational(1,2),'short_divisor_is_lower_power')
    kap=s.Rational(1,100)
    check(s.simplify(s.Rational(1,2)+3*eps-3*(s.Rational(1,6)+eps+kap))==-3*kap,'optional_odd_tail_exponent')

out={
 'status':'PASS_EXACT_LOCAL_CONTROLS',
 'mathematical_checks':sum(counts.values()),
 'counts':dict(counts),
 'planted_errors_detected':len(planted),
 'planted_errors':planted,
 'scope':'Exact finite algebra and support models. General PAPER proofs are in the verdict; no original CCM spectrum, no asymptotic sign inferred from tests.',
 'new_independent_audit':False,'lean_runs':0,'arb_runs':0,'production_spectral_runs':0,
 'python':sys.version.split()[0],'sympy':s.__version__,
 'registration_sha256':hashlib.sha256(Path(__file__).with_name('registration.json').read_bytes()).hexdigest(),
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(out,indent=2,ensure_ascii=False))
