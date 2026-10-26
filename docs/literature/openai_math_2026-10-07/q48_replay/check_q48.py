#!/usr/bin/env python3
"""Q48: exact framing and finite algebra checks, NOT production CCM spectra.
Uses only the standard library. Transcendental source signs are not sampled.
Log-prime rational specializations below test polynomial identities only.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import re
import sys

NAME = 'PROSHKA_CCM_CENTERED_TWO_COPY_SOURCE_Q48_2026-10-26.txt'
SIZE = 169553
LF = 2645
SHA = 'ffab4fd075bc2eb5be7c534d9fe6b81e2b86b30bcf4e5d64e354d0270996389c'
HEAD = re.compile(rb'^BEGIN_SOURCE (S\d+) (\S+) BYTES=(\d+) LF=(\d+) SHA256=([0-9a-f]{64})\n', re.M)

def verify_packet(raw: bytes) -> dict:
    if len(raw) != SIZE or raw.count(b'\n') != LF:
        raise ValueError('packet size/LF')
    if hashlib.sha256(raw).hexdigest() != SHA:
        raise ValueError('packet SHA256')
    raw.decode('utf-8')
    if b'\r' in raw or not raw.endswith(b'\n'):
        raise ValueError('newline convention')
    if not raw.startswith(b'OPERATIVE_CLASS: TRY_CCM_CENTERED_TWO_COPY_SOURCE_Q48\n'):
        raise ValueError('request binding')
    pos = 0
    rows = []
    for i in range(1, 12):
        h = HEAD.search(raw, pos)
        if h is None or h[1] != f'S{i}'.encode():
            raise ValueError('source order')
        start = h.end()
        end = start + int(h[3])
        body = raw[start:end]
        if len(body) != int(h[3]) or body.count(b'\n') != int(h[4]):
            raise ValueError('source size/LF')
        if hashlib.sha256(body).hexdigest() != h[5].decode():
            raise ValueError('source SHA256')
        body.decode('utf-8')
        tail = b'\nEND_SOURCE ' + h[1] + b'\n'
        if raw[end:end + len(tail)] != tail:
            raise ValueError('source framing')
        rows.append(dict(id=h[1].decode(), name=h[2].decode(), bytes=len(body),
                         lf=body.count(b'\n'), sha256=h[5].decode(),
                         start_byte=start, end_byte=end,
                         start_line=raw[:start].count(b'\n') + 1,
                         end_line=raw[:end].count(b'\n')))
        pos = end + len(tail)
    if raw[pos:].strip():
        raise ValueError('trailing material')
    return dict(name=NAME, bytes=SIZE, lf=LF, sha256=SHA,
                source_count=len(rows), manifest_verified=True, sources=rows)

@dataclass(frozen=True)
class G:
    """An exact Gaussian rational; no Python floating-point complex arithmetic."""
    r: F = F(0)
    i: F = F(0)
    @staticmethod
    def cast(z):
        return z if isinstance(z, G) else G(F(z))
    def __add__(self, z):
        z = G.cast(z)
        return G(self.r + z.r, self.i + z.i)
    __radd__ = __add__
    def __neg__(self):
        return G(-self.r, -self.i)
    def __sub__(self, z):
        return self + (-G.cast(z))
    def __rsub__(self, z):
        return G.cast(z) - self
    def __mul__(self, z):
        z = G.cast(z)
        return G(self.r*z.r - self.i*z.i, self.r*z.i + self.i*z.r)
    __rmul__ = __mul__
    def __truediv__(self, z):
        z = G.cast(z)
        den = z.r*z.r + z.i*z.i
        if not den:
            raise ZeroDivisionError
        return self*z.conj()*G(1/den)
    def conj(self):
        return G(self.r, -self.i)
    def real(self):
        if self.i:
            raise AssertionError('expected an exactly real trace')
        return self.r


def zero(n): return [[G() for _ in range(n)] for _ in range(n)]
def eye(n): return [[G(F(i == j)) for j in range(n)] for i in range(n)]
def add(a,b): return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def scale(a,z): return [[x*z for x in row] for row in a]
def mul(a,b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))),G())
             for j in range(len(b[0]))] for i in range(len(a))]
def star(a): return [[a[j][i].conj() for j in range(len(a))] for i in range(len(a[0]))]
def trace(a): return sum((a[i][i] for i in range(len(a))),G()).real()
def compress(p,a): return mul(mul(p,a),p)
def center(a,p,d): return add(a,scale(p,-trace(a)/d))
def var(a,p,d):
    z = center(a,p,d)
    return trace(mul(z,z))
def pairing(a,b): return trace(mul(a,b))

def inverse(a):
    n=len(a)
    z=[row[:] + erow[:] for row,erow in zip(a,eye(n))]
    for j in range(n):
        pivot=next((r for r in range(j,n) if z[r][j] != G()),None)
        if pivot is None: raise ValueError('singular exact matrix')
        z[j],z[pivot]=z[pivot],z[j]
        q=z[j][j]
        z[j]=[v/q for v in z[j]]
        for r in range(n):
            if r!=j:
                q=z[r][j]
                z[r]=[x-q*y for x,y in zip(z[r],z[j])]
    return [row[n:] for row in z]

def factor(n):
    if n<1: raise ValueError('positive integer expected')
    out={};p=2
    while p*p<=n:
        while n%p==0:
            out[p]=out.get(p,0)+1;n//=p
        p+=1
    if n>1: out[n]=out.get(n,0)+1
    return out

def mu(n):
    fs=factor(n)
    return 0 if any(k>1 for k in fs.values()) else (-1)**len(fs)
def ll_add(a,b):
    z=a.copy()
    for key,x in b.items(): z[key]=z.get(key,F())+x
    return {key:x for key,x in z.items() if x}
def ll_scale(a,t): return {key:t*x for key,x in a.items() if t*x}
def lam_form(n):
    fs=factor(n)
    return {next(iter(fs)):F(1)} if len(fs)==1 else {}
def conv_mu_log(n):
    z={}
    for d in range(1,n+1):
        if n%d==0: z=ll_add(z,ll_scale(factor(n//d),F(mu(d))))
    return z

def quadratic_logs(a,b):
    z={}
    for p,x in a.items():
        for q,y in b.items():
            key=tuple(sorted((p,q)))
            z[key]=z.get(key,F())+x*y
    return {key:x for key,x in z.items() if x}

def lambda_specialization(n):
    # Formal substitution log(p) -> p/(p+1), NOT an approximation to log(p).
    return sum((x*F(p,p+1) for p,x in lam_form(n).items()),F())

def fixture_raw(n):
    h=zero(4)
    for i in range(4):
        h[i][i]=G(F((n+2*i)%7-3,n+i+1))
        for j in range(i+1,4):
            v=G(F((n+i+j)%5-2,n+j+2),F((n+2*i+j)%3-1,n+i+3))
            h[i][j]=v;h[j][i]=v.conj()
    return h

def determinant(a):
    z=[row[:] for row in a];n=len(z);ans=G(1)
    for j in range(n):
        pivot=next((r for r in range(j,n) if z[r][j]!=G()),None)
        if pivot is None: return F(0)
        if pivot!=j: z[j],z[pivot]=z[pivot],z[j];ans=-ans
        q=z[j][j];ans=ans*q
        for r in range(j+1,n):
            f=z[r][j]/q
            for k in range(j+1,n): z[r][k]=z[r][k]-f*z[j][k]
            z[r][j]=G()
    return ans.real()

def psd_exact(a):
    # All principal minors: small rational fixtures only.
    from itertools import combinations
    n=len(a)
    if star(a)!=a: return False
    return all(determinant([[a[i][j] for j in ids] for i in ids])>=0
               for k in range(1,n+1) for ids in combinations(range(n),k))

def euler_interval_checks(P):
    rows=[]
    for r,ell in ((F(1,2),F(1)),(F(2,3),F(3,2)),(F(3,4),F(5,3))):
        # Finite compression of the bilateral Poisson multiplier. This exact
        # Toeplitz fixture is NOT the original logarithmic prime grid.
        raw=[[G(ell*r**abs(i-j) if i!=j else F()) for j in range(4)] for i in range(4)]
        ap=compress(P,raw)
        lower_abs=2*ell*r/(1+r);upper=2*ell*r/(1-r)
        alpha=4*ell*r*r/(1-r*r);gamma=4*ell*ell*r*r/(1-r*r)
        assert upper-lower_abs==alpha and upper*lower_abs==gamma
        defect=mul(add(scale(P,upper),scale(ap,-1)),add(ap,scale(P,lower_abs)))
        assert psd_exact(add(ap,scale(P,lower_abs)))
        assert psd_exact(add(scale(P,upper),scale(ap,-1)))
        assert psd_exact(defect)
        assert mul(ap,ap)==add(add(scale(ap,alpha),scale(P,gamma)),scale(defect,-1))
        d=trace(P);mean=trace(ap)/d
        assert var(ap,P,d)==alpha*trace(ap)+d*gamma-trace(defect)-d*mean*mean
        rows.append(dict(r=str(r),formal_log=str(ell),trace_deficit=str(trace(defect)),
                         lower_abs=str(lower_abs),upper=str(upper)))
    return rows

def checks():
    count={}; planted={}; details=[]
    for n in range(1,49):
        assert conv_mu_log(n)==lam_form(n)
    count['formal_one_copy_coefficients']=48
    pairs=[(2,3),(4,8),(9,25),(12,5),(16,27),(1,2),(6,10),(7,11)]
    for n,k in pairs:
        assert quadratic_logs(conv_mu_log(n),conv_mu_log(k))==quadratic_logs(lam_form(n),lam_form(k))
    count['formal_two_copy_coefficients']=len(pairs)
    assert quadratic_logs(lam_form(2),lam_form(3))=={(2,3):F(1)}
    planted['replace_tensor_coefficients_by_Lambda_product']=lam_form(6)=={} and quadratic_logs(lam_form(2),lam_form(3))!={}
    # Rational projected Hermitian fixtures. They are not original-P CCM cells.
    v=[[G(1)],[G(0,1)],[G(1)],[G()]]
    P=add(eye(4),scale(mul(v,star(v)),-F(1,3)))
    d=trace(P)
    assert d==3 and mul(P,P)==P
    R=fixture_raw(3)
    D=scale(compress(P,mul(star(R),R)),F(1,10))
    Gcontinuous=scale(D,-1)
    for m in (8,12,16):
        raw={n:(zero(4) if n==m else fixture_raw(n)) for n in range(2,m+1)}
        H={n:compress(P,h) for n,h in raw.items()}
        w={n:lambda_specialization(n)/n for n in H} # rational weight fixture, not n^-1/2
        A=zero(4); Araw=zero(4); groups={}
        for n,h in H.items():
            term=scale(h,w[n]);A=add(A,term);Araw=add(Araw,scale(raw[n],w[n]))
            fs=factor(n)
            if len(fs)==1:
                p=next(iter(fs))
                groups[p]=add(groups.get(p,zero(4)),term)
        C=add(A,D)
        ac=trace(A)/d;hc=trace(D)/d
        Ac=center(A,P,d);Dc=center(D,P,d)
        va=var(A,P,d);vh=var(D,P,d);vc=var(C,P,d)
        g=pairing(Ac,Dc)
        assert trace(C)/d==ac+hc
        assert vc==va+2*g+vh
        Hc={n:center(h,P,d) for n,h in H.items()}
        atomatom=sum((w[n]*w[k]*pairing(Hc[n],Hc[k]) for n in H for k in H),F())
        mixed=sum((w[n]*pairing(Hc[n],Dc) for n in H),F())
        assert atomatom==va and mixed==g
        fp={p:center(z,P,d) for p,z in groups.items()}
        same=sum((pairing(z,z) for z in fp.values()),F())
        cross=sum((pairing(z,t) for p,z in fp.items() for q,t in fp.items() if p!=q),F())
        assert same>=0 and same+cross==va
        # Entire continuous-source control changes A itself to the continuous source.
        Cz=add(Gcontinuous,D)
        assert Cz==zero(4) and trace(Cz)==0 and var(Cz,P,d)==0
        assert var(Gcontinuous,P,d)+2*pairing(center(Gcontinuous,P,d),Dc)+vh==0
        # Exact square-root triangle controls, squared without discarding signs.
        assert g*g<=va*vh
        assert (vc-va-vh)**2<=4*va*vh
        planted['omit_one_mixed_sector']=planted.get('omit_one_mixed_sector',False) or vc!=va+g+vh
        planted['reverse_continuous_return_sign']=planted.get('reverse_continuous_return_sign',False) or vc!=va-2*g+vh
        diag=sum((w[n]**2*pairing(Hc[n],Hc[n]) for n in H),F())
        planted['drop_distinct_powers_of_same_prime']=planted.get('drop_distinct_powers_of_same_prime',False) or same!=diag
        planted['drop_distinct_prime_sectors']=planted.get('drop_distinct_prime_sectors',False) or cross!=0
        product_cut=sum((w[n]*w[k]*pairing(Hc[n],Hc[k]) for n in H for k in H if n*k<=m),F())
        planted['impose_false_product_cutoff']=planted.get('impose_false_product_cutoff',False) or va!=product_cut
        planted['remove_intermediate_P_in_compressed_square']=planted.get('remove_intermediate_P_in_compressed_square',False) or trace(mul(A,A))!=trace(compress(P,mul(Araw,Araw)))
        wrong=add(C,scale(eye(4),-trace(C)/4))
        planted['center_using_ambient_dimension']=planted.get('center_using_ambient_dimension',False) or vc!=trace(mul(wrong,wrong))
        details.append(dict(m=m,dimension=int(d),mean_atomic=str(ac),mean_decay=str(hc),variance_atomic=str(va),variance_decay=str(vh),mixed_pairing=str(g),variance_full=str(vc),same_prime_sum=str(same),distinct_prime_sum=str(cross)))
    count['projected_four_sector_fixtures']=len(details)
    euler=euler_interval_checks(P)
    count['same_prime_interval_deficit_fixtures']=len(euler)
    # Rank argument at half period: test arbitrary rational codimension-3
    # projectors, not transcendental original contacts. The PAPER proof is general.
    half=[]
    for M in (4,5,6):
        js=list(range(-M,M+1));n=len(js)
        cols=[[G(1),G(F(j)),G(F(j*j))] for j in js]
        Pm=add(eye(n),scale(mul(mul(cols,inverse(mul(star(cols),cols))),star(cols)),-1))
        assert mul(Pm,Pm)==Pm
        dm=trace(Pm);assert dm==2*M-2
        parity=zero(n)
        for i,j in enumerate(js): parity[i][i]=G(F(1 if j%2==0 else -1))
        halfop=compress(Pm,parity)
        k2=var(halfop,Pm,dm)
        assert k2>=2*(M-3)
        half.append(dict(M=M,dimension=int(dm),K2=str(k2),paper_lower=2*(M-3)))
    count['half_period_rank_fixtures']=len(half)
    assert F(2)<F(9,4) # sqrt(2)<3/2 implies kappa=6+4sqrt(2)<12
    assert all(planted.values())
    return dict(passed=True,counts=count,planted_errors_detected=planted,
                rational_four_sector_results=details,half_period_rank_results=half,euler_interval_results=euler,
                scope='Exact formal arithmetic and Gaussian-rational nonproduction algebra only',
                actual_original_P_numerical_spectra=False,
                cofinal_source_sign_verified_by_finite_tests=False,
                independent_signed_supplier_derived=False)

def main():
    if len(sys.argv)!=2:
        raise SystemExit('usage: python3 check_q48.py CANONICAL_Q48.txt')
    raw=Path(sys.argv[1]).read_bytes(); provenance=verify_packet(raw)
    bad=bytearray(raw);bad[provenance['sources'][0]['start_byte']+120]^=1
    try: verify_packet(bytes(bad))
    except ValueError: provenance['single_byte_corruption_detected']=True
    else: raise AssertionError('corrupt packet accepted')
    result=dict(provenance=provenance,mathematics=checks(),
                historical_programs_executed=False,lean_run=False,arb_run=False,
                production_spectrum_run=False,independent_audit_run=False)
    text=json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
    Path('q48_checks.json').write_text(text,encoding='utf-8')
    print(text,end='')

if __name__=='__main__': main()
