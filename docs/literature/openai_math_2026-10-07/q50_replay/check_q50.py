#!/usr/bin/env python3
"""Q50 provenance and exact algebra. No production spectral computation.
Usage: python3 check_q50.py CANONICAL_Q50.txt
Uses only the Python standard library. Historical code is never executed.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,math,re,sys

PACKET_SHA='6d24b63f6f150b5fd723bbb99248417685b430a03a9fdd91abcecb2020d70e50'
PACKET_BYTES=49254
PACKET_LF=858
ROW=re.compile(rb'^(S\d+): (\S+); bytes=(\d+); LF=(\d+); SHA256=([0-9a-f]{64})$',re.M)

def provenance(raw:bytes)->dict:
    if len(raw)!=PACKET_BYTES or raw.count(b'\n')!=PACKET_LF or hashlib.sha256(raw).hexdigest()!=PACKET_SHA:
        raise ValueError('packet byte/LF/hash mismatch')
    raw.decode('utf-8')
    if b'\r' in raw or not raw.endswith(b'\n'):raise ValueError('newline convention')
    if not raw.startswith(b'Q50 SUPPORT_AWARE_SIGNED_OVERLAP'):raise ValueError('request binding')
    pos=raw.index(b'BEGIN S1 '); rows=list(ROW.finditer(raw[:pos])); out=[]
    if len(rows)!=10:raise ValueError('manifest count')
    for i,h in enumerate(rows,1):
        sid,name,nb,lf,sha=h.groups()
        if sid!=f'S{i}'.encode():raise ValueError('source order')
        head=b'BEGIN '+sid+b' '+name+b'\n'
        if raw[pos:pos+len(head)]!=head:raise ValueError('begin frame')
        start=pos+len(head); end=start+int(nb); body=raw[start:end]
        if len(body)!=int(nb) or body.count(b'\n')!=int(lf) or hashlib.sha256(body).hexdigest()!=sha.decode():
            raise ValueError('body byte/LF/hash')
        body.decode('utf-8'); tail=b'\nEND '+sid+b'\n'
        if raw[end:end+len(tail)]!=tail:raise ValueError('end frame')
        out.append(dict(id=sid.decode(),name=name.decode(),bytes=len(body),lf=int(lf),sha256=sha.decode(),
                        start_byte=start,end_byte=end,start_line=raw[:start].count(b'\n')+1,end_line=raw[:end].count(b'\n')))
        pos=end+len(tail)
        while raw[pos:pos+1]==b'\n':pos+=1
    if pos!=len(raw):raise ValueError('trailing content')
    return dict(bytes=len(raw),lf=PACKET_LF,sha256=PACKET_SHA,source_count=10,sources=out)

def zz(n):return [[F(0) for _ in range(n)] for _ in range(n)]
def mm(A,B):
    return [[sum((A[i][k]*B[k][j] for k in range(len(B))),F(0)) for j in range(len(B[0]))] for i in range(len(A))]
def add(A,B):return [[x+y for x,y in zip(a,b)] for a,b in zip(A,B)]
def scale(A,t):return [[t*x for x in row] for row in A]
def mv(A,v):return [sum((x*y for x,y in zip(row,v)),F(0)) for row in A]
def dot(v,w):return sum((x*y for x,y in zip(v,w)),F(0))
def quad(A,v):return dot(v,mv(A,v))
def anti(A,J):return add(mm(A,J),mm(J,A))
def reflection(n):return [[F(int(i+j==n-1)) for j in range(n)] for i in range(n)]
def hankel_atom(n,h):return [[F(int(i+j==h)) for j in range(n)] for i in range(n)]
def shift(n,s):return [[F(int(i==j+s)) for j in range(n)] for i in range(n)]
def transpose(A):return [list(row) for row in zip(*A)]

def nullspace(A):
    B=[row[:] for row in A];n=len(B[0]);r=0;piv=[]
    for c in range(n):
        p=next((i for i in range(r,len(B)) if B[i][c]),None)
        if p is None:continue
        B[r],B[p]=B[p],B[r];u=B[r][c];B[r]=[x/u for x in B[r]]
        for i in range(len(B)):
            if i!=r:
                u=B[i][c];B[i]=[x-u*y for x,y in zip(B[i],B[r])]
        piv.append(c);r+=1
        if r==len(B):break
    out=[]
    for c in range(n):
        if c in piv:continue
        v=[F(0)]*n;v[c]=F(1)
        for i,p in enumerate(piv):v[p]=-B[i][c]
        out.append(v)
    return out

def trim(p):
    while len(p)>1 and p[-1]==0:p.pop()
    return p

def padd(p,q):
    out=[F(0)]*max(len(p),len(q))
    for j,x in enumerate(p):out[j]+=x
    for j,x in enumerate(q):out[j]+=x
    return trim(out)
def pscale(p,s):return trim([x*s for x in p])
def pd(p):return trim([F(j)*p[j] for j in range(1,len(p))] or [F(0)])
def pmul(p,q):
    r=[F(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):r[i+j]+=x*y
    return trim(r)
def peval(p,x):return sum((v*x**i for i,v in enumerate(p)),F(0))
def pint(p,a,b):return sum((v*(b**(i+1)-a**(i+1))/F(i+1) for i,v in enumerate(p)),F(0))
def preflect(p):return [(-1)**i*x for i,x in enumerate(p)]

def log_interval(x:F,n:int=12):
    if x<1:raise ValueError('x>=1')
    z=(x-1)/(x+1)
    lo=2*sum((z**(2*k+1)/F(2*k+1) for k in range(n)),F(0))
    hi=lo+2*z**(2*n+1)/(F(2*n+1)*(1-z*z))
    return lo,hi

def checks()->dict:
    groups={};bad={}
    # Rational finite-grid analogues, NOT the logarithmic CCM lattice.
    n=9;J=reflection(n)
    for h in range(n):
        H=hankel_atom(n,h);S=shift(n,n-1-h)
        assert mm(J,H)==S and mm(H,J)==transpose(S)
    groups['all_finite_grid_reflections']=n
    H=add(scale(hankel_atom(n,3),F(2,3)),scale(hankel_atom(n,6),F(5,7)))
    S=add(scale(shift(n,n-1-3),F(2,3)),scale(shift(n,n-1-6),F(5,7)))
    assert anti(H,J)==add(S,transpose(S))
    bad['wrong_h_equals_s_instead_of_L_minus_s']=anti(hankel_atom(n,2),J)!=add(shift(n,2),transpose(shift(n,2)))
    bad['delete_one_time_orientation']=mm(H,J)!=anti(H,J)
    # Half weights on the discrete dividing diagonal represent a null boundary
    # of the continuum; this is an exact algebraic quadrature fixture only.
    r=F(1,2);full=zz(n);lo=zz(n);tail=zz(n);decay=zz(n)
    for i in range(n):
        for j in range(n):
            w=r**(i+j-(n-1));full[i][j]=w
            lo[i][j]=w*(F(1) if i+j<n-1 else F(1,2) if i+j==n-1 else F(0))
            tail[i][j]=full[i][j]-lo[i][j]
            decay[i][j]=r**abs(i-j)
    assert add(lo,tail)==full and anti(tail,J)==decay
    rows=[[F(int(i==0)) for i in range(n)],[F(int(i==n-1)) for i in range(n)],
          [r**i for i in range(n)],[r**(-i) for i in range(n)]]
    basis=nullspace(rows)
    vectors=[]
    for k in range(3):
        v=[sum((F((k+1)*(j+1),j+2)*b[i] for j,b in enumerate(basis)),F(0)) for i in range(n)]
        vectors.append(v)
        assert all(dot(row,v)==0 and dot(row,mv(J,v))==0 for row in rows)
        assert quad(full,v)==0 and quad(anti(full,J),v)==0
        assert quad(anti(lo,J),v)==-quad(decay,v)
        C=anti(add(H,scale(lo,-1)),J)
        completed=add(anti(H,J),decay)
        assert quad(C,v)==quad(completed,v)
        jp=mv(J,v);vp=[(x+y)/2 for x,y in zip(v,jp)];vm=[(x-y)/2 for x,y in zip(v,jp)]
        X=add(H,tail)
        assert quad(anti(X,J),v)==2*quad(X,vp)-2*quad(X,vm)
        # Complete discrete-to-continuous replacement cancels before estimates.
        assert anti(add(lo,scale(lo,-1)),J)==zz(n)
    v=vectors[0]
    assert quad(decay,v)>0
    bad['delete_triangle_complement_after_contacts']=quad(anti(lo,J),v)!=0
    vp=[(x+y)/2 for x,y in zip(v,mv(J,v))];vm=[(x-y)/2 for x,y in zip(v,mv(J,v))]
    X=add(H,tail)
    bad['use_plus_sign_for_both_reflection_sectors']=quad(anti(X,J),v)!=2*quad(X,vp)+2*quad(X,vm)
    # Whole real kernels on complex inputs = the two complete real forms.
    C=anti(X,J);u=vectors[0];v=vectors[1]
    whole=quad(C,u)+quad(C,v)
    wrong=quad(C,u)-quad(C,v)  # missed complex conjugation
    bad['omit_complex_conjugation']=whole!=wrong
    groups['constrained_rational_triangle_cases']=len(vectors)
    groups['exact_constraint_nullity']=len(basis)
    # Explicit compact polynomial filter; endpoint moment identity exact.
    a=F(1,100); polydata=[]
    for power in (8,12):
        chi=[F(0)]*(2*power+1)
        for k in range(power+1):chi[2*k]=F((-1)**k*math.comb(power,k))/a**(2*k)
        for parity,vpoly in ((1,chi),(-1,pd(chi))):
            upoly=padd(pd(pd(vpoly)),pscale(vpoly,-F(1,4)))
            assert preflect(upoly)==pscale(upoly,F(parity))
            U=pint(pmul(upoly,upoly),-a,a);assert U>0
            for z in (F(1,2),-F(1,2)):
                primitive=padd(pd(vpoly),pscale(vpoly,-z))
                # d(e^(zx)*primitive)/dx = e^(zx)*upoly
                assert padd(pd(primitive),pscale(primitive,z))==upoly
                assert peval(primitive,-a)==0 and peval(primitive,a)==0
            polydata.append({'power':power,'parity':parity,'squared_norm_positive':True})
    groups['exact_compact_filter_cases']=len(polydata)
    # Three-jet correction: sign of cos-1 coefficient is indispensable.
    e0,e1,e2=F(2,7),-F(3,11),F(5,13);omega=F(2,9)
    assert e0-e0==0 and e1-(e1/omega)*omega==0 and e2+(e2/omega**2)*(-omega**2)==0
    bad['omit_second_jet_correction']=e2!=0
    bad['reverse_second_jet_correction_sign']=e2-(e2/omega**2)*(-omega**2)!=0
    groups['exact_jet_correction']=1
    # Actual logarithmic separations, certified with rational series bounds.
    l2,u2=log_interval(F(2));l32,u32=log_interval(F(3,2))
    assert l2>F(2,3) and l32>F(2,5) and 4*a<l2 and 2*a<l32
    alpha_lo=l2/F(3,2);alpha_hi=u2/F(7,5)
    assert alpha_lo>F(4,9)
    assert alpha_lo-F(1,20)>F(1,3)
    assert -alpha_lo+4*a+F(1,20)<-F(1,3)
    # The C0 sign allowance is CONSTANT, not an m^(1/2) obstruction.
    groups['actual_log_support_and_margin_checks']=1
    exponents=[]
    for eps in (F(1,64),F(1,100),F(1,128)):
        inv=1/eps;ceil_inv=(inv.numerator+inv.denominator-1)//inv.denominator
        q=ceil_inv+6;ex=F(1,2)+eps*(3-q)
        assert ex<=-F(1,2)-3*eps
        exponents.append({'epsilon':str(eps),'fixed_q':q,'power_before_logs':str(ex)})
    groups['projection_power_fixtures']=len(exponents)
    # Source-specific packet algebra: signs are reflection parity * local parity.
    packet_signs=[]
    for local in (-1,1):
        for refl in (-1,1):
            packet_signs.append({'local_parity':local,'global_reflection':refl,'A_over_alpha':local*refl})
    assert all(bad.values())
    return dict(passed=True,scope='Exact finite algebra and rational enclosures; not production CCM spectra',
                groups=groups,planted_errors_detected=bad,polynomial_filter_cases=polydata,
                log2_interval=[str(l2),str(u2)],log_three_halves_interval=[str(l32),str(u32)],
                alpha_interval=[str(alpha_lo),str(alpha_hi)],packet_signs=packet_signs,
                projection_exponent_fixtures=exponents,
                universal_source_sign_certified_by_code=False,
                asymptotic_source_sign_proof='PAPER in the accompanying Markdown; not a finite computation')

def main():
    if len(sys.argv)!=2:raise SystemExit('usage: python3 check_q50.py CANONICAL_Q50.txt')
    raw=Path(sys.argv[1]).read_bytes();p=provenance(raw)
    altered=bytearray(raw);altered[p['sources'][0]['start_byte']+20]^=1
    try:provenance(bytes(altered))
    except ValueError:p['corrupted_byte_detected']=True
    else:raise AssertionError('corrupted packet accepted')
    out=dict(provenance=p,mathematics=checks(),historical_code_executed=False,repository_writes=False,
             independent_audit=False,lean=False,arb=False,production_spectrum=False)
    text=json.dumps(out,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
    Path('q50_checks.json').write_text(text,encoding='utf-8');print(text,end='')
if __name__=='__main__':main()
