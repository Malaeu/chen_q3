"""Literal H, B, p, A decomposition for zeta and Davenport-Heilbronn EVEN.

A=H+outer(p,p)-B in the physical j=0,...,m basis. Signed arithmetic
coefficients are retained; DH has no pole. Diagnostic rounding, not an enclosure.
No source alteration, zero-side Gram, clipping, or RH assumption is used.
"""
from functools import lru_cache
import hashlib
from pathlib import Path
import platform
import time
import numpy as np
import scipy
from scipy.special import digamma
import source_float as original_float

PINNED_FLOAT_SHA256 = '627579485355b2907fbb34c3ab91ca09ac067b84cc65aa163f5d36207bbe313e'


def _world(world):
    world=world.lower()
    if world not in ('zeta','dh'):raise ValueError('world must be zeta or dh')
    return world


def verify_sources():
    original_float.verify_source()
    got=hashlib.sha256(Path(original_float.__file__).read_bytes()).hexdigest()
    if got != PINNED_FLOAT_SHA256:raise RuntimeError('SOURCE_FLOAT_CHANGED')


@lru_cache(maxsize=32)
def coefficients(m, world='zeta'):
    """Signed longdouble b(n), indices0..m-1, BEFORE division by sqrt(n).

    DH uses (a*b)(n)=a(n)log(n), with a(1)=1 and a(n) periodic mod5.
    The triangular divisor sieve implements the full Dirichlet recurrence;
    there is no multiplicativity or prime-support assumption.
    """
    world=_world(world)
    if m<2:raise ValueError('m>=2 required')
    ld=np.longdouble
    if np.finfo(ld).nmant<=np.finfo(np.float64).nmant:
        raise RuntimeError('EXTENDED_PRIME_PRECISION_REQUIRED')
    b=np.zeros(m,dtype=ld)
    if world=='zeta':
        sieve=np.ones(m,dtype=bool);sieve[:2]=False
        for p in range(2,m):
            if sieve[p]:
                sieve[p*p::p]=False
                k=p
                while k<m:
                    b[k]=np.log(ld(p));k*=p
    else:
        tau=(np.sqrt(ld(10)-2*np.sqrt(ld(5)))-2)/(np.sqrt(ld(5))-1)
        aa=np.array([0,1,tau,-tau,-1],dtype=ld)
        n=np.arange(2,m,dtype=np.int64)
        b[2:]=aa[n%5]*np.log(n.astype(ld))
        for d in range(2,m):
            if 2*d<m:
                k=np.arange(2,(m-1)//d+1,dtype=np.int64)
                b[2*d::d] -= b[d]*aa[k%5]
    b.flags.writeable=False
    return b


def _arch(m,world):
    L=np.log(float(m));pi=np.pi
    n=np.arange(m+1,dtype=np.float64);omega=2*pi*n/L;w2=omega**2
    alpha=.5 if world=='zeta' else 1.5
    zarg=alpha/2+.5j*omega
    psi=digamma(zarg)
    tri=original_float.trigamma(zarg).real
    diag=psi.real-digamma(alpha/2)+tri/(2*L)
    diag[1:] += psi.imag[1:]/(L*omega[1:])
    moment=psi.imag/2
    a,e=alpha,np.exp(-alpha*L);step=np.exp(-2*L);count=0
    while e>2.0**-304:
        den=a*a+w2
        moment -= omega*e/den
        diag -= e*(2*w2/(a*den)+4*a*a/(L*den**2)+2*a/den)
        diag[0] += 2*e/(L*a*a)
        a+=2;e*=step;count+=1
    is_dh=world=='dh'
    c=-np.euler_gamma-np.log(8*pi/(5 if is_dh else 1))+(pi/2 if is_dh else -pi/2)
    z=np.exp(-L/2)
    tail=np.arctanh(z)+(-np.arctan(z) if is_dh else np.arctan(z))
    return n,omega,moment,c+diag+2*tail,L,count


def _arithmetic(m,world,block):
    ld=np.longdouble;L=np.log(ld(m));pi=np.arccos(ld(-1))
    b=coefficients(m,world)
    atoms=np.flatnonzero(b[2:])+2
    weights=b[atoms]/np.sqrt(atoms.astype(ld))
    ratios=np.log(atoms.astype(ld))/L
    ps=np.empty(m+1);pd=np.empty(m+1)
    for lo in range(0,m+1,block):
        hi=min(m+1,lo+block);n=np.arange(lo,hi,dtype=ld)
        phase=(2*pi*n[:,None])*ratios[None,:]
        ss=np.sin(phase)@weights
        cc=np.cos(phase)@(2*(1-ratios)*weights)
        nz=n>0;cc[nz]-=ss[nz]/(pi*n[nz])
        ps[lo:hi]=ss;pd[lo:hi]=cc
    return ps,pd,b,len(atoms)


def _offdiagonal(moment,n,d,denominator):
    v=n*moment
    out=v[:,None]-v[None,:]
    out/=denominator
    out*=d[:,None]*d[None,:]/np.pi
    return out


def build(m,world='zeta',*,block=128):
    """Return (components,meta), all matrices float64, physical basis j=0..m.

    components has H,B,p,A,omega,W and coefficients. W is the vector
    1+omega**2; coefficients are signed b(n), indices0..m-1, longdouble.
    Exact decomposition: A=H+pp^T-B. DH p is identically zero. No projection,
    whitening, artificial pole, detector, or C* computation is performed.
    """
    if not isinstance(m,(int,np.integer)) or m<2:raise ValueError('integer m>=2 required')
    world=_world(world);wall=time.perf_counter();cpu=time.process_time();verify_sources()
    n,omega,moment,hdiag,L,tail_count=_arch(m,world)
    ps,pd,b,atom_count=_arithmetic(m,world,block)
    d=np.full(m+1,np.sqrt(2.));d[0]=1
    nn=n*n;den=nn[:,None]-nn[None,:];np.fill_diagonal(den,1.)
    H=_offdiagonal(moment,n,d,den);np.fill_diagonal(H,hdiag)
    B=-_offdiagonal(ps,n,d,den);np.fill_diagonal(B,pd)
    del den
    p=np.zeros(m+1)
    if world=='zeta':p=np.sqrt(2/L)*d*np.sinh(L/4)/(omega**2+.25)
    A=H-B
    A+=np.outer(p,p)
    parts=dict(H=H,B=B,p=p,A=A,omega=omega,W=1+omega**2,coefficients=b)
    meta=dict(m=int(m),world=world,dimension=m+1,dtype=str(A.dtype),
              source_sha256=original_float.SOURCE_SHA256,source_git_blob=original_float.SOURCE_GIT_BLOB,
              source_float_sha256=PINNED_FLOAT_SHA256,
              core_builder_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              python=platform.python_version(),numpy=np.__version__,scipy=scipy.__version__,
              signed_arithmetic_atoms=atom_count,tail_terms=tail_count,tail_cut='2^-304',
              coefficient_intermediate_dtype=str(b.dtype),mantissa_bits=int(np.finfo(b.dtype).nmant+1),
              decomposition='A=H+outer(p,p)-B',pole_present=world=='zeta',
              wall_seconds=time.perf_counter()-wall,cpu_seconds=time.process_time()-cpu,
              interval_certificate=False,honesty='DIAGNOSTIC_NEVER_A_PROOF; CHALLENGER_NOT_RH')
    return parts,meta


@lru_cache(maxsize=8192)
def corner(m,world='zeta'):
    """Return dict H00,B00,p0,A00 from the literal direct n=0 diagonal."""
    world=_world(world);verify_sources()
    if not isinstance(m,(int,np.integer)) or m<2:raise ValueError('integer m>=2 required')
    L=np.log(float(m));alpha=.5 if world=='zeta' else 1.5
    diag=float(original_float.trigamma(np.array([alpha/2+0j]))[0].real)/(2*L)
    a,e=alpha,np.exp(-alpha*L);step=np.exp(-2*L)
    while e>2.0**-304:
        diag-=2*e/(L*a*a)+2*e/a;a+=2;e*=step
    dh=world=='dh';z=np.exp(-L/2)
    c=-np.euler_gamma-np.log(8*np.pi/(5 if dh else 1))+(np.pi/2 if dh else -np.pi/2)
    H00=float(c+diag+2*(np.arctanh(z)+(-np.arctan(z) if dh else np.arctan(z))))
    b=coefficients(m,world);n=np.arange(2,m,dtype=np.longdouble);LL=np.log(np.longdouble(m))
    B00=float(np.sum(2*(1-np.log(n)/LL)*b[2:]/np.sqrt(n)))
    p0=0. if dh else np.sqrt(2/L)*np.sinh(L/4)/.25
    return dict(H00=H00,B00=B00,p0=float(p0),A00=float(H00+p0*p0-B00))
