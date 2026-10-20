"""Q04 exact algebra controls; NOT numerical certification of the CCM spectrum."""
from fractions import Fraction as F
from collections import Counter
from pathlib import Path
import json, hashlib

def mu(n):
    ans=1; p=2
    while p*p<=n:
        if n%p==0:
            n//=p;ans=-ans
            if n%p==0:return 0
        p+=1
    return -ans if n>1 else ans

def fact(n):
    out={};p=2
    while p*p<=n:
        while n%p==0:out[p]=out.get(p,0)+1;n//=p
        p+=1
    if n>1:out[n]=out.get(n,0)+1
    return out

def zero(n):return [[F(0) for j in range(n)] for i in range(n)]
def add(A,B):return [[x+y for x,y in zip(a,b)] for a,b in zip(A,B)]
def smul(t,A):return [[t*x for x in a] for a in A]
def tr(A):return list(map(list,zip(*A)))
def mm(A,B):return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def convolution_matrix(N,coef):
    A=zero(N)
    for n in range(1,N+1):
        for k in range(1,N//n+1):A[n*k-1][k-1]+=coef(n)
    return A

def z(a=0,b=0):return F(a),F(b)
def za(a,b):return a[0]+b[0],a[1]+b[1]
def zn(a):return -a[0],-a[1]
def zm(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def zc(a):return a[0],-a[1]
def zs(xs):
    ans=z()
    for x in xs:ans=za(ans,x)
    return ans

def inner(a,b):return zs(zm(zc(x),y) for x,y in zip(a,b))
def norm2(a):return inner(a,a)[0]
def det3(A):
    return zs([zm(zm(A[0][0],A[1][1]),A[2][2]),zm(zm(A[0][1],A[1][2]),A[2][0]),zm(zm(A[0][2],A[1][0]),A[2][1]),
               zn(zm(zm(A[0][2],A[1][1]),A[2][0])),zn(zm(zm(A[0][1],A[1][0]),A[2][2])),zn(zm(zm(A[0][0],A[1][2]),A[2][1]))])

stats=Counter()
for n in range(1,257):
    div=[d for d in range(1,n+1) if n%d==0]
    assert sum(mu(d) for d in div)==int(n==1)
    stats['mobius_inverse_atoms']+=1
    coef={}
    for d in div:
        for p,e in fact(d).items():coef[p]=coef.get(p,0)-mu(d)*e
    coef={p:e for p,e in coef.items() if e}
    fs=fact(n);expected={next(iter(fs)):1} if len(fs)==1 else {}
    assert coef==expected
    stats['differentiated_inverse_mangoldt_atoms']+=1

planted=False
for N in (3,4,6,8,12):
  for sig in (1,2):
    M=convolution_matrix(N,lambda n:F(mu(n),n**sig))
    Z=convolution_matrix(N,lambda n:F(1,n**sig))
    Id=[[F(i==j) for j in range(N)] for i in range(N)]
    assert mm(M,Z)==mm(Z,M)==Id
    stats['finite_full_inverse_matrices']+=1
    for p in [n for n in range(2,N+1) if fact(n)=={n:1}]:
      Mp=convolution_matrix(N,lambda n:F(-mu(n)*fact(n).get(p,0),n**sig))
      Lp=convolution_matrix(N,lambda n:F(int(len(fact(n))==1 and p in fact(n)),n**sig))
      assert mm(Mp,Z)==Lp
      Gp=add(mm(tr(Mp),M),mm(tr(M),Mp))
      assert mm(mm(tr(Z),Gp),Z)==add(Lp,tr(Lp))
      stats['formal_log_prime_gram_returns']+=1
      bad=[[Gp[i][j] if i==j else F(0) for j in range(N)] for i in range(N)]
      if mm(mm(tr(Z),bad),Z)!=add(Lp,tr(Lp)):planted=True
assert planted
stats['discarded_mixed_gram_terms_detected']+=1

for k in range(1,41):
    a=[z(F(k+j,j+2),F(j-k,j+3)) for j in range(3)]
    b=[z(F(2*j-k,j+3),F(k+1,j+2)) for j in range(3)]
    H=[[za(zm(a[i],zc(b[j])),zm(b[i],zc(a[j]))) for j in range(3)] for i in range(3)]
    c=inner(a,b); aa=norm2(a);bb=norm2(b)
    assert zs(H[i][i] for i in range(3))==z(2*c[0])
    minors=zs(za(zm(H[i][i],H[j][j]),zn(zm(H[i][j],H[j][i]))) for i in range(3) for j in range(i+1,3))
    assert minors==z(c[0]**2+c[1]**2-aa*bb)
    assert det3(H)==z()
    stats['rank_two_characteristic_polynomial']+=1

for delta in (F(1,16),F(1,8),F(1,4),F(3,8),F(7,16)):
  for gamma in (F(0),F(1,3),F(1),F(14)):
    kap=1/(2*delta)-1/((delta+F(1,2))**2+gamma**2)
    expected=((delta-F(1,2))**2+gamma**2)/(2*delta*((delta+F(1,2))**2+gamma**2))
    assert kap==expected and kap>0
    stats['projected_endpoint_limit_constants']+=1

# PRECHECKED before registration; counted only as exact arithmetic, not a new prediction.
tail=F(2,3**8)+F(2,7*3**7)+F(1,49*3**7)
assert tail==F(143,321489) and tail<F(1,2048)
stats['sigma8_tail_rational_control']+=1

for eps in (F(1,1000),F(1,100),F(1,64),F(1,33)):
    assert F(3,2)*eps<F(3,8)<F(1,2)
    assert (F(1,2)+eps)/2*2==F(1,2)+eps
    stats['returned_power_comparisons']+=1
out={'status':'PASS','counts':dict(stats),'total_checks':sum(stats.values()),
     'scope':'exact finite coefficient and matrix identities; not an actual CCM positivity certificate',
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'arb_runs':0,'lean_runs':0,'actual_ccm_spectral_runs':0}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
