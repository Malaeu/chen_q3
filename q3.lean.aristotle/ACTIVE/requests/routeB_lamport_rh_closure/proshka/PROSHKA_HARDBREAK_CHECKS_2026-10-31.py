#!/usr/bin/env python3
"""Exact checks and an optional literal-source FLOATING diagnostic.

Run:
  uv run --with sympy --with numpy --with scipy PROSHKA_HARDBREAK_CHECKS_2026-10-31.py
  uv run --with sympy --with numpy --with scipy PROSHKA_HARDBREAK_CHECKS_2026-10-31.py --diagnostic --output hardbreak_probe.json

The exact tests check algebra, not RH. The diagnostic has UNPAID quadrature,
truncation, and floating errors; its numbers are NOT interval certificates.
--output is the JSON path to create; e.g. hardbreak_probe.json in the current directory.
"""
from __future__ import annotations
import argparse
import json
import math
import time
from pathlib import Path


def exact_checks() -> None:
    import sympy as s
    x,a=s.symbols('x a',real=True)
    Q=s.Function('Q'); H=s.Function('H')(x); P=s.Function('P')(x)
    assert s.simplify(s.diff(Q(a*x),a).subs(a,1).doit()-x*s.diff(Q(x),x))==0
    print('PASS dilation: s Q-prime, not s Q')
    LH=s.diff(H,x)**2-H*s.diff(H,x,2)
    complete=2*(P*s.diff(H,x)+s.diff(P,x)*H/2)**2-(s.diff(P,x)*H)**2/2
    assert s.simplify(P**2*LH-complete+s.diff(P**2*H*s.diff(H,x),x))==0
    print('PASS square completion with full total derivative')
    R=P*H; LR=s.diff(R,x)**2-R*s.diff(R,x,2)
    assert s.simplify(LR-P**2*LH-(s.diff(P,x)**2-P*s.diff(P,x,2))*H**2)==0
    print('PASS polynomial-factor Laguerre identity')
    n=s.symbols('n',integer=True,nonnegative=True)
    assert s.expand(4*(n*n-n)-2*n*(2*n-1))==-2*n
    print('PASS physical Hankel coefficient')
    # Gaussian equality-null symbols: exact ALL cross moments, not just diagonals.
    for K in range(1,6):
        order=2*K-1
        for ell in range(2*K-1):
            total=s.Integer(0)
            for j in range(order+1):
                hv=s.expand(s.hermite(2*ell,s.sqrt(1+j)/2))
                total+=(-1)**(order+j)*s.binomial(order,j)*(-1)**ell*hv/s.Integer(2)**(2*ell)
            assert s.simplify(total)==0
        y=s.symbols('y',real=True)
        peak=sum((-1)**(order+j)*s.binomial(order,j)*y**j for j in range(order+1))
        assert s.expand(peak-(y-1)**order)==0
    print('PASS all finite-jet equalities K=1..5 and strictly positive peak')
    eps,N=s.symbols('eps N',positive=True)
    A=s.diag(eps*s.exp(N),-eps*s.exp(2*N))
    assert A.subs(eps,0)==s.zeros(2)
    assert s.diff(A,eps).subs(eps,0)==s.diag(s.exp(N),-s.exp(2*N))
    print('PASS zero at one parameter does not fix the signed derivative')
    u,b=s.symbols('u b',real=True,nonzero=True)
    pair=1/(u-s.I*b)**2+1/(u+s.I*b)**2
    assert s.simplify(pair-2*(u*u-b*b)/(u*u+b*b)**2)==0
    print('PASS off-real zero-pair curvature sign')
    print('ALL 7 EXACT GROUPS PASSED')


def diagnostic() -> dict:
    import numpy as np
    from numpy.polynomial import Polynomial
    from scipy.integrate import quad
    from scipy.linalg import eigvalsh
    import scipy, sympy

    K=3  # h, h'', h^(4); no growing-K or CCM-bottom inference.
    theta_terms=6
    prime_cutoff=40
    s_cutoff=3.5
    physical_halfwidth=3.0
    p=[Polynomial([0.,-24.,16.])]
    for _ in range(2*(K-1)):
        q=p[-1]
        p.append(.5*q+Polynomial([0.,2.])*q.deriv()-Polynomial([0.,2.])*q)
    ns=np.arange(1,theta_terms+1,dtype=float)
    def hd(x: float,k: int=0) -> float:
        v=abs(float(x)); y=math.pi*ns*ns*math.exp(2*v)
        out=math.exp(v/2)*float(np.sum(p[k](y)*np.exp(-y)))
        return -out if x<0 and k%2 else out
    def integral(fun,a,b):
        return quad(fun,a,b,epsabs=1e-9,epsrel=2e-11,limit=140)[0]
    def corr(s,i,j):
        mid=-s/2
        return 2*integral(lambda x:hd(x,2*i)*hd(x+s,2*j),
                          mid-physical_halfwidth,mid+physical_halfwidth)
    def vm(n: int) -> float:
        for q in range(2,n+1):
            if n%q==0:
                z=n
                while z%q==0: z//=q
                return math.log(q) if z==1 else 0.
        return 0.
    atoms=[(n,vm(n)) for n in range(2,prime_cutoff+1) if vm(n)]
    M=np.zeros((K,K)); J=np.zeros_like(M); G=np.zeros_like(M)
    near=np.zeros_like(M); D=np.zeros_like(M); entries=[]
    s0=math.log(2); total=K*(K+1)//2; done=0; start=time.monotonic()
    for i in range(K):
        for j in range(i,K):
            q=lambda s:corr(s,i,j)
            primes=sum(v*math.log(n)/math.sqrt(n)*q(math.log(n)) for n,v in atoms)
            continuum=integral(lambda s:s*math.exp(s/2)*q(s),0,s_cutoff)
            jterm=integral(lambda s:(.5 if s==0 else s*math.exp(-2.5*s)/(-math.expm1(-2*s)))*q(s),0,s_cutoff)
            n=i+j
            rhs=(-1.)**n*(4*integral(lambda x:x*x*hd(x,n)**2,-physical_halfwidth,physical_halfwidth)
                -(2*n*integral(lambda x:hd(x,n-1)**2,-physical_halfwidth,physical_halfwidth) if n else 0.))
            M[i,j]=M[j,i]=primes-continuum; J[i,j]=J[j,i]=jterm
            near[i,j]=near[j,i]=math.log(2)*s0/math.sqrt(2)*q(s0)-integral(lambda s:s*math.exp(s/2)*q(s),0,s0)
            ip=integral(lambda x:hd(x,2*i)*hd(x,2*j),-physical_halfwidth,physical_halfwidth)
            # The tiny s interval and all truncations are diagnostic approximations.
            energy=integral(lambda s:math.exp(-2.5*s)/(-math.expm1(-2*s))*(2*ip-q(s)) if s>1e-7 else 0.,0,s_cutoff)
            jt=sum(math.exp(-(2*k+2.5)*s_cutoff)/(2*k+2.5) for k in range(15))
            G[i,j]=G[j,i]=ip+energy+2*ip*jt
            if i and j:
                D[i,j]=D[j,i]=4*i*j*(-1.)**(i+j)*integral(lambda x:hd(x,i+j-1)**2,-physical_halfwidth,physical_halfwidth)
            relative=abs(M[i,j]+jterm-rhs)/max(1.,abs(rhs))
            entries.append(dict(i=i,j=j,M_full=float(M[i,j]),J=float(jterm),physical_rhs=float(rhs),relative_difference=float(relative)))
            done+=1; elapsed=time.monotonic()-start; eta=elapsed*(total-done)/done
            filled=20*done//total
            print('['+'#'*filled+'-'*(20-filled)+f'] {done}/{total} ETA {eta:.1f}s',flush=True)
    far=M-near
    return dict(status='FLOATING_DIAGNOSTIC_NOT_CERTIFICATE',K=K,
        theta_terms=theta_terms,prime_cutoff=prime_cutoff,continuum_cutoff=s_cutoff,
        physical_halfwidth=physical_halfwidth,s0=s0,entries=entries,
        M_full=M.tolist(),M_far=far.tolist(),G=G.tolist(),polynomial_derivative_Gram=D.tolist(),
        normalized_full_eigenvalues=eigvalsh(M,G).tolist(),
        normalized_far_eigenvalues=eigvalsh(far,G).tolist(),
        mu_K=float(eigvalsh(D,G)[-1]),
        versions=dict(numpy=np.__version__,scipy=scipy.__version__,sympy=sympy.__version__))


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--diagnostic',action='store_true',help='also run the non-certified K=3 literal-source probe')
    parser.add_argument('--output',type=Path,default=Path('hardbreak_probe.json'),help='diagnostic JSON destination')
    args=parser.parse_args()
    exact_checks()
    if args.diagnostic:
        data=diagnostic()
        args.output.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
        print(json.dumps(data,indent=2))
        print(f'WROTE {args.output}')


if __name__=='__main__':
    main()
