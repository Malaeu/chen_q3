"""Exact consistency checks for Q02. These are not CCM spectral certificates."""
from fractions import Fraction as F
from collections import Counter
from pathlib import Path
import hashlib
import json


def trim(a):
    a=list(map(F,a))
    while len(a)>1 and a[-1]==0:a.pop()
    return a

def add(a,b):
    c=[F(0)]*max(len(a),len(b))
    for i,x in enumerate(a):c[i]+=x
    for i,x in enumerate(b):c[i]+=x
    return trim(c)

def scale(q,a): return trim([F(q)*x for x in a])

def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return trim(c)

def deriv(a):return trim([i*a[i] for i in range(1,len(a))] or [0])

def val(a,x):return sum(v*F(x)**i for i,v in enumerate(a))

def integ(a,lo,hi):return sum(x*(F(hi)**(i+1)-F(lo)**(i+1))/F(i+1) for i,x in enumerate(a))

def mu(n):
    s=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;s=-s
            if n%p==0:return 0
        p+=1
    return -s if n>1 else s

stats=Counter();samples=[];rejected=0
for m in (6,9,12,17,24):
    rows={}
    for d in range(1,m+1):
        # Lower value and upper value/derivative vanish exactly.
        f=scale(F(1,m**3),mul([-d,1],mul([m,-1],[m,-1])))
        fp=deriv(f);fpp=deriv(fp)
        assert val(f,d)==val(f,m)==val(fp,m)==0
        stats['endpoint_contracts']+=1
        discrete=sum(val(f,d*k) for k in range(1,m//d+1))
        cont=integ(f,d,m)/d
        err=discrete-cont
        beta_int=F(0);center_int=F(0);b2_int=F(0)
        for k in range(1,m//d+1):
            lo=max(d,k*d);hi=min(m,(k+1)*d)
            if lo>=hi:continue
            beta=[F(k),-F(1,d)]
            b1=[-F(k)-F(1,2),F(1,d)]
            b2=[F(k*k+k)+F(1,6),-F(2*k+1,d),F(1,d*d)]
            beta_int-=integ(mul(beta,fp),lo,hi)
            center_int+=integ(mul(b1,fp),lo,hi)
            b2_int+=integ(mul(b2,fpp),lo,hi)
        bernoulli=-F(d,12)*val(fp,d)-F(d,2)*b2_int
        assert err==beta_int==center_int==bernoulli
        stats['euler_centered_bernoulli_equalities']+=1
        if err:
            assert -center_int!=err
            rejected+=1
        rows[d]=(discrete,cont,err)
        if m%d==0:
            assert b2_int==0
            assert err==-F(d,12)*val(fp,d)
            stats['lower_boundary_nonoscillatory_controls']+=1
    for R in (1,2,3):
        if R>=m:continue
        B=sum(mu(d)*rows[d][0] for d in range(R+1,m+1))
        C=sum(mu(d)*rows[d][1] for d in range(R+1,m+1))
        E=sum(mu(d)*rows[d][2] for d in range(R+1,m+1))
        assert B==C+E
        stats['actual_mu_signed_euler_reassemblies']+=1
        if len(samples)<3:samples.append({'m':m,'R':R,'B':str(B),'C':str(C),'E':str(E)})

# Actual source combinatorial support: k=1 carries log(1)=0.
for m in range(6,65):
    for d in range(1,m+1):
        nonzero_k=list(range(2,m//d+1))
        if 2*d>m:
            assert not nonzero_k
            stats['empty_full_k_shell']+=1
        if 3*d>m and 2*d<=m:
            assert nonzero_k==[2]
            stats['exact_k2_shell']+=1

# Endpoint derivative is -2/L times the all-ones matrix; P b = 0 kills it.
for M in range(1,7):
    n=2*M+1
    P=[[F(i==j)-F(1,n) for j in range(n)] for i in range(n)]
    one=[F(1)]*n
    assert all(sum(P[i][j]*one[j] for j in range(n))==0 for i in range(n))
    for j in range(-M,M+1):
        for k in range(-M,M+1):
            coefficient=F(-2) if j==k else F(2*(k-j),j-k)
            assert coefficient==-2
    stats['projected_upper_derivative_controls']+=1

# Exact coefficients in the second-derivative truncation budget.
for D1,D2 in ((F(0),F(0)),(F(1),F(3)),(F(7,2),F(23,4))):
    K2=F(3,2)+2*D1+D2
    derived=2+F(2,3)*(4+2*D1)+F(4,9)*K2
    stated=F(16,3)+F(20,9)*D1+F(4,9)*D2
    assert derived==stated
    stats['fourier_tail_constant_algebra']+=1

# The centered k-free reciprocal kernel for a scalar Mellin monomial.
# Euler identity alone does not permit erasing the continuous term.
assert any(c!=0 and e!=0 for _,c,e in rows.values())
stats['delete_continuous_term_rejected']+=1

out={
 'status':'PASS', 'scope':'finite exact algebra; synthetic smooth kernels and actual integer mu; not CCM sign certificates',
 'counts':dict(stats),'total_checks':sum(stats.values()),
 'wrong_euler_sign_detected_cases':rejected,'signed_reassembly_samples':samples,
 'new_ccm_spectral_runs':0,'arb_runs':0,'lean_runs':0,
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
