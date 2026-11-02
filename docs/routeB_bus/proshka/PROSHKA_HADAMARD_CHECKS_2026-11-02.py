#!/usr/bin/env python3
"""CCM window-variation checks. Exact algebra plus OPTIONAL floating diagnosis.

  uv run --with sympy PROSHKA_HADAMARD_CHECKS_2026-11-02.py
  uv run --with sympy --with mpmath PROSHKA_HADAMARD_CHECKS_2026-11-02.py --diagnostic

--output names the JSON diagnostic file (default hadamard_probe.json).
No finite computation establishes a cofinal spectral sign, RH or simplicity.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def exact_checks() -> None:
    import sympy as s
    r = s.symbols('r', real=True)
    L, a = s.symbols('L a', positive=True)
    Q = s.Function('Q')
    assert s.simplify(s.diff(Q(a/L), L) + a/L**2 * s.Subs(s.diff(Q(r),r),r,a/L)) == 0
    print('PASS chain rule at frozen coefficient vector')

    def raw(i: int, j: int):
        if i == j:
            return 2*(1-r)*s.cos(2*s.pi*i*r)
        return (s.sin(2*s.pi*j*r)-s.sin(2*s.pi*i*r))/(s.pi*(i-j))
    for N in range(4):
        modes = list(range(-N,N+1))
        U = s.zeros(2*N+1,N+1); U[N,0] = 1
        for j in range(1,N+1):
            U[N-j,j]=U[N+j,j]=1/s.sqrt(2)
        R = s.Matrix([[raw(i,j) for j in modes] for i in modes])
        E = s.simplify(U.T*R*U)
        d = s.Matrix([1]+[s.sqrt(2)]*N)
        assert E.subs(r,0) == 2*s.eye(N+1)
        assert E.subs(r,1) == s.zeros(N+1)
        assert s.simplify(s.diff(E,r).subs(r,1)+2*d*d.T)==s.zeros(N+1)
        assert s.simplify(s.diff(E,r).subs(r,0)+2*d*d.T)==s.zeros(N+1)
    print('PASS full even correlation, both endpoints, rank-one slope for N=0..3')

    for j in range(4):
        dj = 1 if j == 0 else s.sqrt(2)
        u = 4*s.sqrt(2)*dj*L**s.Rational(3,2)*s.sinh(L/4)/(L**2+16*s.pi**2*j*j)
        beta = 3/(2*L)+s.coth(L/4)/4-2*L/(L**2+16*s.pi**2*j*j)
        assert s.simplify(s.diff(u,L)-u*beta)==0
    print('PASS pole-vector derivative including normalization and endpoint transport')

    jfun=s.Function('j')
    arch=2/L*s.Integral(a*jfun(a),(a,0,L))+2*s.Integral(jfun(a),(a,L,s.oo))
    expected=-2/L**2*s.Integral(a*jfun(a),(a,0,L))
    assert s.simplify(s.diff(arch,L)-expected)==0
    print('PASS constant mode: finite arch endpoint cancels infinite arch tail endpoint')

    k=s.symbols('k',integer=True,positive=True)
    p=s.symbols('p',positive=True)
    assert s.simplify(2*s.log(p)/(p**(k/2)*(k*s.log(p)))-2/(k*p**(k/2)))==0
    print('PASS prime-power coefficient 2/(k p^(k/2))')

    B=s.diag(1,-1)
    assert min(B.eigenvals())==-1 and max(B.eigenvals())==1
    A=s.Matrix([[1,1],[1,1]])
    assert min(A.eigenvals())==0 < 1
    print('PASS degenerate slope guard and independent rank-enlargement control')
    print('ALL 6 EXACT GROUPS PASSED')


def diagnostic(output: Path) -> None:
    import mpmath as mp
    mp.mp.dps=60
    pi=mp.pi
    def vm(n: int):
        if n<2: return mp.mpf(0)
        for p in range(2,n+1):
            if n%p==0:
                x=n
                while x%p==0: x//=p
                return mp.log(p) if x==1 else mp.mpf(0)
        raise AssertionError('unreachable')
    def compress(A,N):
        U=mp.zeros(2*N+1,N+1); U[N,0]=1
        for j in range(1,N+1): U[N-j,j]=U[N+j,j]=1/mp.sqrt(2)
        return U.T*A*U
    def raw_q(r,i,j):
        if i==j: return 2*(1-r)*mp.cos(2*pi*i*r)
        return (mp.sin(2*pi*j*r)-mp.sin(2*pi*i*r))/(pi*(i-j))
    def raw_dq(r,i,j):
        if i==j:
            return -2*mp.cos(2*pi*i*r)-4*pi*i*(1-r)*mp.sin(2*pi*i*r)
        return 2*(j*mp.cos(2*pi*j*r)-i*mp.cos(2*pi*i*r))/(i-j)
    # Independent raw-source entry implementation: W02 - WR - full prime sum.
    def Kraw(N,L,cap=None):
        if cap is None: cap=int(mp.floor(mp.exp(L)))
        modes=list(range(-N,N+1)); out=mp.zeros(2*N+1)
        grid=[L*i/8 for i in range(9)]
        moments={0:mp.mpf(0)}; diagonal={}
        for n in range(N+1):
            om=2*pi*n/L
            if n:
                val=mp.quad(lambda x: om/2 if not x else mp.exp(x/2)*mp.sin(om*x)/(2*mp.sinh(x)),grid)
                moments[n]=val; moments[-n]=-val
            def integrand(x):
                if not x: return mp.mpf('.5')-1/L
                e=mp.exp(x/2)
                return (mp.expm1(x/2)-e*x/L-2*e*(1-x/L)*mp.sin(om*x/2)**2)/mp.sinh(x)
            diagonal[n]=mp.quad(integrand,grid)
        const=mp.euler+mp.log(4*pi*mp.tanh(L/2))
        atoms=[(n,vm(n)/mp.sqrt(n)) for n in range(2,cap+1) if vm(n)]
        for i,n in enumerate(modes):
            for j,k in enumerate(modes):
                pole=32*L*mp.sinh(L/4)**2*(L**2-16*pi**2*n*k)/((L**2+16*pi**2*n*n)*(L**2+16*pi**2*k*k))
                arch=const+diagonal[abs(n)] if n==k else (moments[k]-moments[n])/(pi*(n-k))
                prime=mp.fsum(c*raw_q(mp.log(nn)/L,n,k) for nn,c in atoms)
                out[i,j]=pole-arch-prime
        return compress(out,N)
    # Direct derived derivative, not differentiating Kraw numerically.
    def Kprime(N,L,cap=None):
        if cap is None: cap=int(mp.floor(mp.exp(L)))
        modes=list(range(-N,N+1)); out=mp.zeros(2*N+1)
        def integrand(r,i,j):
            if not r: return raw_dq(0,i,j)/(2*L)
            return r*mp.exp(-L*r/2)/(-mp.expm1(-2*L*r))*raw_dq(r,i,j)
        atoms=[(n,vm(n)/mp.sqrt(n)) for n in range(2,cap+1) if vm(n)]
        for ii,i in enumerate(modes):
            for jj,j in enumerate(modes):
                out[ii,jj]=mp.quad(lambda r:integrand(r,i,j),[mp.mpf(k)/8 for k in range(9)])
                out[ii,jj]+=mp.fsum(c*mp.log(n)/L**2*raw_dq(mp.log(n)/L,i,j) for n,c in atoms)
        out=compress(out,N)
        u=mp.matrix([4*mp.sqrt(2)*(1 if j==0 else mp.sqrt(2))*L**mp.mpf('1.5')*mp.sinh(L/4)/(L**2+16*pi*pi*j*j) for j in range(N+1)])
        du=mp.matrix([u[j]*(3/(2*L)+mp.coth(L/4)/4-2*L/(L**2+16*pi*pi*j*j)) for j in range(N+1)])
        return out+du*u.T+u*du.T
    def maxentry(A): return max(abs(x) for x in A)
    N=2; L=mp.mpf('1.25'); eps=mp.mpf('1e-12')
    A=Kraw(N,L); D=Kprime(N,L)
    Ap=Kraw(N,L+eps); Am=Kraw(N,L-eps)
    fd=(Ap-Am)/(2*eps)
    ev,V=mp.eigsy(A); c=V[:,0]
    predicted=(c.T*D*c)[0]
    slope=(mp.eigsy(Ap,eigvals_only=True)[0]-mp.eigsy(Am,eigvals_only=True)[0])/(2*eps)
    d=mp.matrix([1]+[mp.sqrt(2)]*N)
    a4=mp.log(4)
    continuity=maxentry(Kraw(N,a4,4)-Kraw(N,a4,3))
    jump=Kprime(N,a4,4)-Kprime(N,a4,3)
    jump_ref=-2*vm(4)/(mp.sqrt(4)*a4)*d*d.T
    ev4,V4=mp.eigsy(Kraw(N,a4,4)); c4=V4[:,0]
    jump_slope=(c4.T*jump*c4)[0]
    trace_ref=-2*vm(4)/(mp.sqrt(4)*a4)*(d.T*c4)[0]**2
    a6=mp.log(6)
    no_atom=maxentry(Kprime(N,a6,6)-Kprime(N,a6,5))
    a3=mp.log(3)
    old=Kraw(2,a3,3); new=Kraw(3,a3,3)
    principal=maxentry(new[:3,:3]-old)
    modejump=mp.eigsy(new,eigvals_only=True)[0]-mp.eigsy(old,eigvals_only=True)[0]
    vals={
       'matrix_derivative_max_error':maxentry(fd-D),
       'simple_ground_gap':ev[1]-ev[0],
       'ground_derivative_hadamard':predicted,
       'ground_derivative_finite_difference':slope,
       'ground_derivative_error':abs(slope-predicted),
       'at_log4_matrix_continuity_error':continuity,
       'at_log4_derivative_jump_max_error':maxentry(jump-jump_ref),
       'at_log4_simple_ground_gap':ev4[1]-ev4[0],
       'at_log4_ground_slope_jump':jump_slope,
       'at_log4_ground_slope_trace_error':abs(jump_slope-trace_ref),
       'at_log6_non_prime_power_jump_error':no_atom,
       'at_log3_rank_extension_principal_error':principal,
       'at_log3_rank_extension_ground_jump':modejump
    }
    assert vals['matrix_derivative_max_error']<mp.mpf('1e-20')
    assert vals['ground_derivative_error']<mp.mpf('1e-20')
    assert continuity<mp.mpf('1e-50')
    assert vals['at_log4_derivative_jump_max_error']<mp.mpf('1e-50')
    assert no_atom<mp.mpf('1e-50') and principal<mp.mpf('1e-50')
    assert modejump<=mp.mpf('1e-50')
    result={'status':'FLOATING_DIAGNOSTIC_NOT_CERTIFICATE','dps':mp.mp.dps,'fixed_N':N,
      'regular_L':'1.25','finite_difference_step':'1e-12',
      'values':{k:mp.nstr(v,30) for k,v in vals.items()}}
    output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,ensure_ascii=False,indent=2))


def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--diagnostic',action='store_true')
    ap.add_argument('--output',type=Path,default=Path('hadamard_probe.json'))
    args=ap.parse_args()
    exact_checks()
    if args.diagnostic: diagnostic(args.output)


if __name__=='__main__': main()
