"""Exact finite diagnostics, not an analytic or cofinal moment certificate.
Python 3 standard library only. Formal positive logarithmic weights are used
in matrix algebra; true logarithms in the signed witness are handled in PAPER.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
from math import gcd
import json

checks = Counter()
def check(name, condition):
    if not condition:
        raise AssertionError(name)
    checks[name] += 1

# Q(z), z^2=z-1, with conjugate(z)=1-z.
ZERO=(F(0),F(0)); ONE=(F(1),F(0))
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def mul(x,y): return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0]+x[1]*y[1])
def conj(x): return (x[0]+x[1],-x[1])
def scale(a,x): return (a*x[0],a*x[1])
def power(x,k):
    y=ONE
    for _ in range(k): y=mul(y,x)
    return y
ROOTS=[power((F(0),F(1)),k) for k in range(6)]

def clean(A): return {ij:z for ij,z in A.items() if z!=ZERO}
def plus(A,B):
    out=dict(A)
    for ij,z in B.items(): out[ij]=add(out.get(ij,ZERO),z)
    return clean(out)
def times(a,A): return clean({ij:scale(a,z) for ij,z in A.items()})
def star(A): return {(j,i):conj(z) for (i,j),z in A.items()}
def mm(A,B):
    right=defaultdict(list)
    for (k,j),z in B.items(): right[k].append((j,z))
    out={}
    for (i,k),x in A.items():
        for j,y in right[k]:
            ij=(i,j);out[ij]=add(out.get(ij,ZERO),mul(x,y))
    return clean(out)
def quad(A,v,w=None):
    w=v if w is None else w
    z=ZERO
    for (i,j),a in A.items():
        if v.get(i,ZERO)!=ZERO and w.get(j,ZERO)!=ZERO:
            z=add(z,mul(mul(conj(v[i]),a),w[j]))
    return z

def make_ops(labels, facts, prime_weights):
    ix={e:i for i,e in enumerate(labels)}; n=len(labels)
    ell=[sum(prime_weights[p]*k for p,k in facts[e].items()) for e in labels]
    C={}; Aps={p:{} for p in prime_weights}; D={}
    for e in labels:
        i=ix[e]
        if ell[i]:D[i,i]=(F(ell[i]),F(0))
        for p,v in facts[e].items():
            Aps[p][i,i]=(F(v),F(0))
            for k in range(1,v+1):
                # Model-specific exact divisor is installed by the caller.
                d=DIVIDE(e,p,k);j=ix[d]
                Aps[p][i,j]=ONE
                C[i,j]=(F(prime_weights[p]),F(0))
    A=plus(D,C)
    def K(H):
        return clean({(i,j):scale(F(1,ell[i]+ell[j]),v)
                      for (i,j),v in H.items() if ell[i]+ell[j]})
    def transfer(H):
        J=K(H);return plus(mm(star(C),J),mm(J,C))
    return ix,ell,C,A,Aps,K,transfer

# Part I: full exponent box in a two-labelled-prime ideal monoid.
labels=list(product(range(4),repeat=2)); labels.sort(key=lambda e:7**e[0]*13**e[1])
primes=(0,1); facts={e:{i:k for i,k in enumerate(e) if k} for e in labels}
def DIVIDE(e,p,k): return tuple(v-k if i==p else v for i,v in enumerate(e))
ix,ell,C,A,Aps,K,transfer=make_ops(labels,facts,{0:2,1:3})
mu={ix[e]:(F((-1)**sum(e) if max(e)<=1 else 0),F(0)) for e in labels}
unit=ix[(0,0)]
G={}; observed=[]
# Amplifiers p and p^2 are separate, with their identical zero masks retained.
amp_exponents=((0,0),(1,0),(2,0),(0,1),(1,1))
for row_no,vals in enumerate(product((-1,0,1),repeat=2)):
    wt=F(1+row_no%3,3)
    for mask in amp_exponents:
        t={}
        for e in labels:
            norm=7**e[0]*13**e[1]
            w=F(norm%17-8,17) if 40<=norm<=1500 else F(0)
            phase=vals[0]**e[0]*vals[1]**e[1]
            if any(a and b for a,b in zip(e,mask)):phase=0
            t[ix[e]]=(w*phase,F(0))
        observed.append((wt,t))
        for i,x in t.items():
            for j,y in t.items():
                if x!=ZERO and y!=ZERO:
                    key=(i,j);G[key]=add(G.get(key,ZERO),scale(wt/F(91),mul(conj(x),y)))
G=clean(G)
FG=transfer(G); R=transfer(FG);Y=plus(times(-1,K(G)),K(FG))
N=plus(mm(star(A),Y),mm(star(Y),A)); direct=plus(G,N)
for i in range(len(labels)):
    for j in range(len(labels)):
        check('two_sweep_matrix_identity',direct.get((i,j),ZERO)==R.get((i,j),ZERO))
check('null_correction',quad(N,mu)==ZERO)
check('source_energy_preserved',quad(G,mu)==quad(R,mu))
check('hermitian_residual',R==star(R))
physical=ZERO
for wt,t in observed:
    val=ZERO
    for i,z in t.items():val=add(val,mul(z,mu[i]))
    physical=add(physical,scale(wt/F(91),mul(conj(val),val)))
check('full_masked_source_gram',physical==quad(G,mu))

# Independent entrywise two-prime-power expansion, with same-prime paths.
up={i:[] for i in range(len(labels))}
for (i,j),v in C.items():
    delta=tuple(a-b for a,b in zip(labels[i],labels[j]))
    p=next(p for p,vv in enumerate(delta) if vv)
    up[j].append((i,v[0],p))
def expansion(drop_same=False):
    E={}
    for i in range(len(labels)):
        for j in range(len(labels)):
            z=ZERO
            for i1,l1,p1 in up[i]:
                for i2,l2,p2 in up[i1]:
                    if drop_same and p1==p2:continue
                    fac=l1*l2/F((ell[i1]+ell[j])*(ell[i2]+ell[j]))
                    z=add(z,scale(fac,G.get((i2,j),ZERO)))
            for j1,l1,p1 in up[j]:
                for j2,l2,p2 in up[j1]:
                    if drop_same and p1==p2:continue
                    fac=l1*l2/F((ell[i]+ell[j1])*(ell[i]+ell[j2]))
                    z=add(z,scale(fac,G.get((i,j2),ZERO)))
            for i1,l1,p1 in up[i]:
                for j1,l2,p2 in up[j]:
                    if drop_same and p1==p2:continue
                    fac=l1*l2/F(ell[i1]+ell[j1])*(F(1,ell[i1]+ell[j])+F(1,ell[i]+ell[j1]))
                    z=add(z,scale(fac,G.get((i1,j1),ZERO)))
            if z!=ZERO:E[i,j]=z
    return E
expanded=expansion()
for i in range(len(labels)):
    for j in range(len(labels)):
        check('expanded_same_and_distinct_prime_paths',expanded.get((i,j),ZERO)==R.get((i,j),ZERO))
bad=expansion(True)
bad_ij=next(ij for ij in R.keys()|bad.keys() if R.get(ij,ZERO)!=bad.get(ij,ZERO))
check('planted_same_prime_deletion_detected',bad!=R)

# Full roots of unity and zero extensions in the local source relation.
for vals in product([ZERO]+ROOTS,repeat=2):
    for mask in amp_exponents:
        psi={e:mul(power(vals[0],e[0]),power(vals[1],e[1])) for e in labels}
        for e in labels:
            if any(a and b for a,b in zip(e,mask)):psi[e]=ZERO
        for p in primes:
            pexp=(1,0) if p==0 else (0,1)
            for e in labels:
                value=scale(e[p],mul(mu[ix[e]],psi[e]))
                for k in range(1,e[p]+1):
                    d=DIVIDE(e,p,k)
                    value=add(value,mul(power(psi[pexp],k),mul(mu[ix[d]],psi[d])))
                check('twisted_all_power_masks',value==ZERO)
for x,a,b in product(range(1,7),repeat=3):
    lhs=(F(1,2*x+a)+F(1,2*x+b))/F(2*x+a+b)
    rhs=(1+F(2*x,2*x+a+b))/F((2*x+a)*(2*x+b))
    check('positive_diagonal_kernel_identity',lhs==rhs)
# Absolute pair-mass is conserved for the two sweeps on this window support.
Gabs={ij:(abs(v[0]),F(0)) for ij,v in G.items()}
check('absolute_pair_mass_conserved',sum(z[0] for z in transfer(transfer(Gabs)).values())==sum(z[0] for z in Gabs.values()))

# Part II: every good primary ideal of norm <=100, and ALL 18 elements of norm49.
def norm(z):a,b=z;return a*a-a*b+b*b
def em(z,w):a,b=z;c,d=w;return(a*c-b*d,a*d+b*c-b*d)
def ec(z):a,b=z;return(a-b,-b)
def div(z,w):
    a,b=em(z,ec(w));Q=norm(w)
    return (a//Q,b//Q) if a%Q==0 and b%Q==0 else None
ideals=sorted([(a,b) for a in range(-20,21) for b in range(-20,21)
               if a%3==1 and b%3==0 and 0<norm((a,b))<=100 and gcd(norm((a,b)),6)==1],key=lambda z:(norm(z),z))
actual_primes=[]; facts={}
for n in ideals:
    m=n;fs={}
    for p in actual_primes:
        while norm(m)>1:
            d=div(m,p)
            if d is None:break
            fs[p]=fs.get(p,0)+1;m=d
    if norm(m)>1:actual_primes.append(m);fs[m]=1
    facts[n]=fs
rows=[(a,b) for a in range(-15,16) for b in range(-15,16) if norm((a,b))==49]
cols=[n for n in ideals if norm(n)==91]
def chi(p,u):
    Q=norm(p);root=(-p[0]*pow(p[1],-1,Q))%Q
    val=(u[0]+u[1]*root)%Q
    if not val:return ZERO
    val=pow(val,(Q-1)//6,Q)
    j=next(j for j in range(6) if pow((1+root)%Q,j,Q)==val)
    return ROOTS[j]
def chin(n,u):
    z=ONE
    for p,k in facts[n].items():z=mul(z,power(chi(p,u),k))
    return z

def DIVIDE(e,p,k):
    for _ in range(k):e=div(e,p)
    if e is None:raise ValueError('nondivisor')
    return e
weights={p:(2 if norm(p)==7 else 3 if norm(p)==13 else norm(p)+1) for p in actual_primes}
ix,ell,C,A,Aps,K,transfer=make_ops(ideals,facts,weights)
G={}
for n,m in product(cols,repeat=2):
    z=ZERO
    for u in rows:z=add(z,mul(conj(chin(n,u)),chin(m,u)))
    G[ix[n],ix[m]]=scale(F(1,78),z)
G=clean(G)
check('actual_ideal_inventory',len(ideals)==31 and len(actual_primes)==23)
check('actual_row_inventory',len(rows)==18 and len(cols)==4)
check('actual_gram_hermitian',G==star(G))
parent=next(p for p in actual_primes if norm(p)==13)
ip=ix[parent];active=[ix[n] for n in cols if div(n,parent) is not None]
s={i:ONE for i in active};e={ip:ONE};Kphys=quad(G,s)
check('actual_complete_two_column_energy',Kphys==(F(2,13),F(0)))
FG=transfer(G);R=transfer(FG);Y=plus(times(-1,K(G)),K(FG))
corrected=plus(G,plus(mm(star(A),Y),mm(star(Y),A)))
for i,j in product(range(len(ideals)),repeat=2):check('actual_matrix_identity_formal_logs',corrected.get((i,j),ZERO)==R.get((i,j),ZERO))
x=F(3);l=F(2);h=x+l;c=l/(2*h);d=l*l/(h*(2*x+l))
for theta in (F(-3),F(-1),F(0),F(1,2),F(1),F(2),F(7)):
    Rtheta=plus(times(theta-1,FG),times(theta,R));S=times(-1,Rtheta)
    check('actual_compressed_pencil',quad(S,s)==ZERO)
    check('actual_compressed_pencil',quad(S,s,e)==scale((1-theta)*c,Kphys))
    check('actual_compressed_pencil',quad(S,e)==scale(-theta*d,Kphys))
    if theta>0:
        val=quad(S,e)
    else:
        aa=(1-theta)*c;t=-aa/(1+abs(theta)*d)
        z=dict(s);z[ip]=(t,F(0));val=quad(S,z)
    check('negative_compressed_witness',val[1]==0 and val[0]<0)
# The full real two-parameter scalar span, not just the canonical pencil.
for aa,bb in product((F(-4),F(-2),F(-1),F(-1,2),F(0),F(1,2),F(1),F(2)),repeat=2):
    Yab=plus(times(aa,K(G)),times(bb,K(FG)))
    Rab=plus(G,plus(mm(star(A),Yab),mm(star(Yab),A)))
    Sab=times(-1,Rab)
    check('two_parameter_compression',quad(Sab,s)==scale(-(1+aa),Kphys))
    check('two_parameter_compression',quad(Sab,s,e)==scale(-(aa+bb)*c,Kphys))
    check('two_parameter_compression',quad(Sab,e)==scale(-bb*d,Kphys))
    if aa>-1:
        z=s
    elif bb>0:
        z=e
    else:
        Av,Bv=-aa,-bb
        if Av>1:
            z={i:scale(-(Av+Bv)*c/(Av-1),v) for i,v in s.items()}
            z[ip]=ONE
        else:
            t=-(Av+Bv)*c/(1+Bv*d)
            z=dict(s);z[ip]=(t,F(0))
    value=quad(Sab,z)
    check('two_parameter_negative_witness',value[1]==0 and value[0]<0)

check('literal_U_L_upper_band',78**25<=49**28 and 78**100>=49**111)
check('literal_X_support',100**25*156**25>=183**25*49**28)
# r=28/25: p=(r*(1+1/10000)-1)/6=7507/375000.
p=F(28,25)*F(10001,10000)/6-F(1,6)
check('literal_amplifier_unit_only',49**p.numerator<2**p.denominator)

rlo,rhi,c0,eta=F(28,25),F(113,100),F(1,10000),F(1,200)
mins={}
for r in (rlo,rhi):
    h=r*(1+c0);p=(h-1)/6
    for le in (r-F(1,100),r):
        values={'PU_gain':5*p,'boundary_margin':h-eta-(p+F(1,6)+F(5,6)*le-F(1,120)),
                'absolute_budget_deficit':le-5*p+eta}
        for name,v in values.items():mins[name]=min(mins.get(name,v),v);check('budget_vertex_positive',v>0)
check('budget_equalities',eta-F(5,6)*rhi*c0==F(5887,1200000))
check('budget_equalities',eta-F(5,6)*rhi*c0-F(1,250)==F(1087,1200000))
out={
 'scope':'FINITE_CELL','verifier':'PAPER',
 'matrix_logs':'formal additive positive weights; true logarithms treated in the derivation',
 'checks':dict(checks),'total':sum(checks.values()),
 'actual_example':{'U':49,'L':78,'X':100,'good_ideals':31,'all_rows_norm49':18,
    'full_columns_norm91':4,'parent_ideal':parent,'local_full_energy':'2/13',
    'true_slack':'-(2/13)*(log 7)^2/((log 91)*(log 1183))'},
 'planted_same_prime_deletion_entry':bad_ij,
 'rational_budgets':{k:str(v) for k,v in mins.items()},
 'cofinal_moment_certified':False,'source_P_M_R_certified':False,
 'Lean_Arb_Comparator_runs':False
}
print(json.dumps(out,indent=2,ensure_ascii=False))
