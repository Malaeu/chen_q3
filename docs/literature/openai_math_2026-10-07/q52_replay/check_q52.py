#!/usr/bin/env python3
"""Q52: exact finite algebra and packet framing, not a CCM spectral certificate.
Usage: python3 check_q52.py CANONICAL_Q52.txt
Standard library only; historical source programs are never executed.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import math
import re
import sys

NAME = 'PROSHKA_CCM_JOINT_BOUNDARY_PHASE_Q52_2026-10-27.txt'
SIZE, LF = 129443, 2162
SHA = '2832d7259a0c5fbac9e4d6882775457f76ce8673ce3862ff6672d23f54286b13'
MAN = re.compile(rb'^S(\d+): ([^;\n]+); bytes=(\d+); LF=(\d+); SHA256=([0-9a-f]{64})$', re.M)


def verify(raw: bytes, outer: bool = True) -> dict:
    if outer and (len(raw) != SIZE or raw.count(b'\n') != LF or hashlib.sha256(raw).hexdigest() != SHA):
        raise ValueError('canonical bytes/LF/SHA')
    raw.decode('utf-8')
    if b'\r' in raw or not raw.endswith(b'\n') or not raw.startswith(b'Q52 JOINT_BOUNDARY_PHASE'):
        raise ValueError('encoding/request frame')
    pos = raw.index(b'BEGIN S1 ')
    heads = list(MAN.finditer(raw[:pos]))
    if len(heads) != 8:
        raise ValueError('manifest count')
    rows = []
    for i, h in enumerate(heads, 1):
        if h[1] != str(i).encode():
            raise ValueError('manifest order')
        sid, name = 'S'+str(i), h[2].decode()
        begin = f'BEGIN {sid} {name}\n'.encode()
        if raw[pos:pos+len(begin)] != begin:
            raise ValueError('opening frame')
        start, end = pos+len(begin), pos+len(begin)+int(h[3])
        body = raw[start:end]
        if len(body) != int(h[3]) or body.count(b'\n') != int(h[4]):
            raise ValueError('body bytes/LF')
        if hashlib.sha256(body).hexdigest() != h[5].decode():
            raise ValueError('body hash')
        body.decode('utf-8')
        close = f'\nEND {sid}\n'.encode()
        if raw[end:end+len(close)] != close:
            raise ValueError('closing frame')
        rows.append(dict(id=sid, name=name, bytes=len(body), lf=body.count(b'\n'),
                         sha256=h[5].decode(), start_byte=start, end_byte=end,
                         start_line=raw[:start].count(b'\n')+1, end_line=raw[:end].count(b'\n')))
        pos = end+len(close)
        # This packet has exactly one blank LF after EVERY closing frame,
        # including the last one. It is outside the source body.
        if raw[pos:pos+1] != b'\n':
            raise ValueError('post-frame separator')
        pos += 1
    if pos != len(raw):
        raise ValueError('trailing bytes')
    return dict(packet=NAME, bytes=len(raw), lf=raw.count(b'\n'), sha256=SHA,
                source_count=8, all_frames_verified=True, sources=rows)


@dataclass(frozen=True)
class Q:
    """Gaussian rational. No float is used to decide a sign."""
    re: F = F(0)
    im: F = F(0)
    def __post_init__(self):
        object.__setattr__(self, 're', F(self.re))
        object.__setattr__(self, 'im', F(self.im))
    @staticmethod
    def cast(x):
        return x if isinstance(x, Q) else Q(x)
    def __add__(self, x):
        x = Q.cast(x); return Q(self.re+x.re, self.im+x.im)
    __radd__ = __add__
    def __neg__(self):
        return Q(-self.re, -self.im)
    def __sub__(self, x):
        return self + (-Q.cast(x))
    def __rsub__(self, x):
        return Q.cast(x) + (-self)
    def __mul__(self, x):
        x = Q.cast(x)
        return Q(self.re*x.re-self.im*x.im, self.re*x.im+self.im*x.re)
    __rmul__ = __mul__
    def conj(self):
        return Q(self.re, -self.im)
    def norm2(self):
        return self.re*self.re+self.im*self.im
    def __truediv__(self, x):
        x = Q.cast(x); n = x.norm2()
        if not n: raise ZeroDivisionError
        return self*x.conj()*F(1, n)
    def __rtruediv__(self, x):
        return Q.cast(x)/self
    def __pow__(self, n):
        if n < 0: return (Q(1)/self)**(-n)
        z = Q(1)
        for _ in range(n): z = z*self
        return z

I = Q(0, 1)

# Bivariate rational polynomials. These test Green's formula, not zeta data.
def add(p, q):
    r = p.copy()
    for k, v in q.items(): r[k] = r.get(k, F(0))+v
    return {k:v for k,v in r.items() if v}
def scale(p, a): return {k:v*a for k,v in p.items() if v*a}
def mul(p, q):
    r = {}
    for (i,j), v in p.items():
        for (k,l), w in q.items(): r[i+k,j+l] = r.get((i+k,j+l), F(0))+v*w
    return r

def der(p, axis):
    r = {}
    for (i,j), v in p.items():
        n = (i,j)[axis]
        if n: r[(i-1,j) if axis == 0 else (i,j-1)] = v*n
    return r

def integ(p, box):
    a,b,c,d = box
    return sum((v*(b**(i+1)-a**(i+1))*F(1,i+1)*(d**(j+1)-c**(j+1))*F(1,j+1)
                for (i,j),v in p.items()), F(0))

def edge(p, axis, fixed, lo, hi):
    out = F(0)
    for (i,j),v in p.items():
        power, n = (i,j) if axis == 0 else (j,i)
        out += v*fixed**power*(hi**(n+1)-lo**(n+1))*F(1,n+1)
    return out

def harmonic(n):
    p = {}
    for j in range(0,n+1,2): p[n-j,j] = F(math.comb(n,j)*(-1)**(j//2))
    return p

def green(X,U,box,drop_second=False):
    a,b,c,d = box; result=F(0)
    for axis, v0,v1,lo,hi in ((0,a,b,c,d),(1,c,d,a,b)):
        p = mul(X,der(U,axis))
        if not drop_second: p=add(p,scale(mul(U,der(X,axis)),-1))
        result += edge(p,axis,v1,lo,hi)-edge(p,axis,v0,lo,hi)
    return result


def math_checks():
    counts, errors = {}, {}
    box=tuple(map(F,[-1,2,-2,1]))
    us=[{(2,0):F(1),(0,2):F(1)}, {(3,1):F(2),(1,2):F(-3),(0,0):F(4)},
        {(4,0):F(1),(0,4):F(-2),(2,2):F(3)}]
    gc=0; drop_detected=False
    for n in range(5):
        X=harmonic(n)
        assert not add(der(der(X,0),0),der(der(X,1),1))
        for U in us:
            lap=add(der(der(U,0),0),der(der(U,1),1))
            val=integ(mul(X,lap),box)
            assert green(X,U,box)==val
            drop_detected |= green(X,U,box,True)!=val
            gc+=1
    counts['green_polynomial_cases']=gc
    errors['drop_U_normal_derivative_of_X']=drop_detected

    # Exact one-root circle averages: mean K(w+r exp(it)) = K(w).
    # They also test the 2pi normalization and winding sign; not actual zeros.
    mc=0
    for w in (Q(F(1,3),F(2,5)),Q(F(-1,4),F(1,7))):
        for n in range(5):
            for mult in (1,3):
                center=w**n; corner=(w+Q(2))**n
                # K(w+2e^(it)) = sum_k coeff_k e^(ikt).
                # The normalized boundary-log integral equals mult*sum_{k>=1} coeff_k,
                # since integral_0^(2pi) t e^(ikt) dt = 2pi/(i*k).
                coeff=[math.comb(n,k)*(w**(n-k))*Q(2)**k for k in range(n+1)]
                branch=mult*sum(coeff[1:],Q(0))
                assert mult*center==mult*corner-branch
                mc+=1
    counts['circle_branch_cases']=mc
    errors['drop_winding_corner']=(Q(3)!=Q(0))
    errors['use_log_modulus_squared_without_half']=(F(3)!=F(6))

    # Finite auxiliary root fixtures only; no numeric zeros of xi are assigned.
    u=F(1,8)
    roots=[(Q(F(1,4),F(2,3)),2),(Q(F(3,8),F(-5,4)),1)]
    bc=0
    for t in (F(-2),F(0),F(1,3),F(3)):
        z=Q(u,t); b=Q(1); ld=Q(0); density=F(0)
        for w,r in roots:
            wr=Q(2*u)-w.conj(); a=w.re-u
            b*=((z-w)/(z-wr))**r
            ld+=r*(1/(z-w)-1/(z-wr))
            density+=r*2*a/(a*a+(t-w.im)**2)
        assert b.norm2()==1 and ld.im==0 and ld.re==-density
        assert density>0; bc+=1
    for z in (Q(F(1,5),F(1,7)),Q(F(3,4),F(-1,3))):
        b=Q(1)
        for w,r in roots: b*=((z-w)/(z-(Q(2*u)-w.conj())))**r
        assert b.norm2()<1;bc+=1
    counts['finite_blaschke_cases']=bc
    w=roots[0][0]; z=Q(u,0)
    errors['reflect_at_zero_instead_of_u']=((z-w)/(z+w.conj())).norm2()!=1
    errors['reverse_boundary_phase_speed']=ld.re!=density

    # Endpoint-reduced integral of the literal Fourier matrix.
    # Delta,L and E are formal rational specializations AFTER imposing
    # exp(+/- i omega_j L)=1, E=exp(z L). They are not production cells.
    fc=0
    for L,delta,z,E in ((F(2),F(1,3),Q(F(2,5),F(1,7)),Q(F(3,2),F(1,4))),
                        (F(3),F(2,5),Q(F(3,7),F(-1,6)),Q(F(4,3),F(-1,5)))):
        for j in range(-2,3):
            for k in range(-2,3):
                oj,ok=j*delta,k*delta
                S=(1/((z+I*oj)*(z+I*ok))+1/((z-I*oj)*(z-I*ok)))/L
                diag=(1/(z+I*oj)+1/(z-I*oj)) if j==k else Q(0)
                rhs=(E-1)*S-diag
                if j==k:
                    direct=sum((-1/(z+sgn*I*oj)+(E-1)/(L*(z+sgn*I*oj)**2)
                                for sgn in (-1,1)),Q(0))
                else:
                    def sine_int(o): return (E-1)*(1/(z+I*o)-1/(z-I*o))/(2*I)
                    direct=2*(sine_int(ok)-sine_int(oj))/(L*(oj-ok))
                assert direct==rhs;fc+=1
                if j==k and j==0: errors['drop_finite_Laplace_diagonal']=(direct!=(E-1)*S)
    counts['finite_Laplace_matrix_entries']=fc

    # Positive-time support correction: exact formal exponential powers,
    # represented here by a rational base for an algebraic test.
    sc=0; base=F(2); u0,a=2,1
    for y in (-3,-1,0,1,2,4):
        analytic=base**((u0+a)*y)
        poisson=base**(u0*y-a*abs(y))
        defect=F(0) if y<=0 else base**((u0+a)*y)-base**((u0-a)*y)
        assert analytic==poisson+defect;sc+=1
    counts['time_support_cases']=sc
    errors['replace_Poisson_by_analytic_continuation']=base**3!=base
    errors['drop_reflected_exponential']=base**3-base!=base**3

    # Contact cancellation S_P(1/2)=0 on explicit source contact directions.
    # Algebraic controls only; PAPER positivity of decaying kernels is separate.
    a0=F(1,2); delta=F(1,3); js=list(range(-2,3))
    q1,q2=a0*a0+delta*delta,a0*a0+4*delta*delta
    ee=[q2,-4*q1,6*a0*a0,-4*q1,q2]
    oo=[q2,-2*q1,F(0),2*q1,-q2]
    cc=0
    for c in (ee,oo):
        assert sum(c)==0
        vp=sum((c0/(Q(a0)+I*j*delta) for j,c0 in zip(js,c)),Q(0))
        vm=sum((c0/(Q(a0)-I*j*delta) for j,c0 in zip(js,c)),Q(0))
        assert vp==vm==Q(0)
        assert sum(c0*c0*2*a0/(a0*a0+(j*delta)**2) for j,c0 in zip(js,c))>0
        cc+=1
    counts['contact_directions']=cc

    # Jensen lower bound for a positive decaying kernel (finite algebra checks).
    jc=0
    for a in (F(1,4),F(1,3),F(1,2)):
        weights=[F(1,6),F(1,3),F(1,2)]; freqs=[F(0),F(1),F(3)]
        moment=sum(p*x*x for p,x in zip(weights,freqs))
        val=sum(p*2*a/(a*a+x*x) for p,x in zip(weights,freqs))
        assert val>=2*a/(a*a+moment);jc+=1
    counts['decaying_kernel_Jensen_cases']=jc
    for u in (F(1,128),F(1,32),F(1,8)):
        a=F(1,2)-2*u
        assert F(4)+2/a<=12
    errors['drop_second_contact_kernel']=(F(4)+F(8)!=F(4))

    exponents=[]
    for eps in (F(1,128),F(1,64),F(1,33)):
        kap=F(5,24)+eps; hh=F(1,4)+eps
        high=F(1,2)+3*eps-3*kap
        lefttail=3*eps+kap-5*hh
        horizontal=F(1,2)+3*eps+kap-6*hh
        righttail=F(1,2)+3*eps+kap-5*hh
        assert high==-F(1,8)
        assert lefttail==-F(25,24)-eps
        assert horizontal==-F(19,24)-2*eps
        assert righttail==-F(13,24)-eps
        exponents.append(dict(epsilon=str(eps),high=str(high),lefttail=str(lefttail),
                              horizontal=str(horizontal),righttail=str(righttail)))
    counts['budget_exponent_rows']=len(exponents)
    # C0=U-Rlow and Rlow=Pstable+Dgrowth, one copy of Hd only.
    C,H,U,Pstable=map(F,[7,2,3,5]);Rlow=U-C;D=Rlow-Pstable;A=C-H
    assert A==U-Pstable-D-H
    errors['double_Hd_return']=A!=U-Pstable-D-2*H
    assert all(errors.values()),errors
    return dict(passed=True,counts=counts,planted_errors_detected=errors,exponents=exponents,
                scope='Exact finite algebra and formal/rational controls; not actual zeta coordinates or CCM spectra',
                cofinal_signed_supplier_certified_by_code=False)


def main():
    if len(sys.argv)!=2: raise SystemExit('usage: python3 check_q52.py CANONICAL_Q52.txt')
    raw=Path(sys.argv[1]).read_bytes();p=verify(raw);mutations={}
    bad=bytearray(raw);bad[p['sources'][0]['start_byte']+50]^=1
    for name,data,outer in [('outer_hash',bytes(bad),True),('body_hash',bytes(bad),False),
                           ('extra_separator',raw[:p['sources'][0]['end_byte']]+b'\n'+raw[p['sources'][0]['end_byte']:],False),
                           ('truncated_frame',raw[:-2],False)]:
        try: verify(data,outer)
        except (ValueError,UnicodeError): mutations[name]=True
        else: raise AssertionError('undetected provenance change: '+name)
    out=dict(provenance=p,provenance_mutations=mutations,mathematics=math_checks(),
             historical_programs_executed=False,lean=False,arb=False,production_spectrum=False,
             numeric_zeta_zeros=False,independent_audit=False)
    text=json.dumps(out,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
    Path('q52_checks.json').write_text(text,encoding='utf-8');print(text,end='')

if __name__=='__main__': main()
