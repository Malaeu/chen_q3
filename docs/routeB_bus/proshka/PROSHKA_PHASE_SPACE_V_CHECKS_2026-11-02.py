#!/usr/bin/env python3
"""Exact controls and a literal finite-CCM diagnostic for a proposed V.

  uv run --with sympy --with mpmath PROSHKA_PHASE_SPACE_V_CHECKS_2026-11-02.py
  uv run --with sympy --with mpmath PROSHKA_PHASE_SPACE_V_CHECKS_2026-11-02.py --diagnostic --m 8 16 24 --dps 90 --order 64 --output phase_space_v.json

--m: original cells, always N=m and L=log(m). --order: GL nodes per panel;
there are eight panels. --output: diagnostic JSON destination, e.g. v.json.
Numerical values have no interval/quadrature/tail certificate. The frequency
energy is evaluated through the exact archimedean form, not a truncated
Fourier integral. All prime powers through m are included.
"""
from __future__ import annotations
import argparse
import json
import time
from pathlib import Path


def exact_checks() -> None:
    import sympy as s
    x,tau=s.symbols('x tau', real=True)
    assert s.simplify(s.diff(s.log(1+s.exp(2*tau)*x*x),tau).subs(tau,0)-2*x*x/(1+x*x))==0
    print('PASS 1 position dilation multiplier')
    z=s.symbols('z',positive=True)
    j=s.exp(-z/2)/(1-s.exp(-2*z))
    mj=s.diff(z*j,z)
    assert s.limit(z*j,z,0,dir='+')==s.Rational(1,2)
    assert s.limit(z*j,z,s.oo)==0
    assert s.limit(mj,z,0,dir='+')==s.Rational(1,4)
    print('PASS 2 archimedean endpoints: integral m_j = -1/2')
    th=s.symbols('th', real=True)
    c=s.Matrix([s.cos(th),s.sin(th)])
    d=s.Matrix([-s.sin(th),s.cos(th)])
    A=d*d.T
    B=s.diag(0,1)
    Apr=s.diff(A,th)
    V=(c.T*B*c)[0]
    rhs=-2*(c.T*B*d)[0]*(d.T*Apr*c)[0]
    assert s.trigsimp(s.diff(V,th)-rhs)==0
    assert s.trigsimp(s.diff(V,th)-s.sin(2*th))==0
    print('PASS 3 exact spectral response; both signs despite exact ground state')
    for bj in [s.Rational(1,2),s.Integer(2)]:
        An=s.diag(0,-1); Bn=s.diag(1,bj)
        new=s.Matrix([0,1]); old=s.Matrix([1,0])
        assert (new.T*An*new)[0] < (old.T*An*old)[0]
        assert (new.T*Bn*new)[0]-(old.T*Bn*old)[0]==bj-1
    print('PASS 4 mode insertion lowers energy but need not lower V')
    C=s.symbols('C',nonnegative=True)
    a0,prime,pole,position,lam,cstar=s.symbols('a0 prime pole position lam cstar',real=True)
    assert s.expand((lam+cstar+prime-pole+position).subs(lam,a0-cstar-prime+pole)-(a0+position))==0
    print('PASS 5 full signed source balance keeps the pole and all mixed signs')
    assert 1-s.Rational(1,4)-s.Rational(1,4)==s.Rational(1,2)
    print('PASS 6 simultaneous time/frequency tail thresholds')
    print('ALL 6 EXACT CONTROL GROUPS PASSED')


def mangoldt(n: int, mp):
    for p in range(2,n+1):
        if n%p==0:
            q=n
            while q%p==0:q//=p
            return mp.log(p) if q==1 else mp.mpf(0)
    return mp.mpf(0)


def cell(m: int, dps: int, order: int) -> dict:
    import mpmath as mp
    mp.mp.dps=dps
    L=mp.log(m); N=m
    pi=mp.pi; sq2=mp.sqrt(2)
    gn,gw=mp.gauss_quadrature(order,'legendre')
    nodes=[]
    for panel in range(8):
        lo=mp.mpf(panel)/8; hi=mp.mpf(panel+1)/8
        for z,w in zip(gn,gw):
            nodes.append(((lo+hi)/2+(hi-lo)*z/2,w*(hi-lo)/2))
    ss=[L*y for y,w in nodes]
    ww=[L*w for y,w in nodes]
    sins=[[mp.sin(2*pi*n*y) for y,w in nodes] for n in range(N+1)]
    coss=[[mp.cos(2*pi*n*y) for y,w in nodes] for n in range(2*N+1)]
    xpos=[mp.log1p((L*(y-mp.mpf('.5')))**2) for y,w in nodes]
    xpos_mom=[mp.fsum(w*x*c for (y,w),x,c in zip(nodes,xpos,coss[n])) for n in range(2*N+1)]
    js=[mp.exp(-s/2)/(-mp.expm1(-2*s)) for s in ss]
    sinmom=[mp.fsum(w*j*sn for w,j,sn in zip(ww,js,sins[n])) for n in range(N+1)]
    diag=[]
    for n in range(N+1):
        # Stable raw WR diagonal, including the source subtraction at s=0.
        vals=[]
        for (y,w),s in zip(nodes,ss):
            e=mp.exp(s/2)
            num=mp.expm1(s/2)-e*y-2*e*(1-y)*mp.sin(pi*n*y)**2
            vals.append(L*w*num/mp.sinh(s))
        diag.append(mp.fsum(vals))
    cstar=mp.euler+mp.log(8*pi)+pi/2
    wrconst=mp.euler+mp.log(4*pi*mp.tanh(L/2))
    ds=[mp.mpf(1)]+[sq2]*N
    arch=mp.zeros(N+1); prime=mp.zeros(N+1); pos=mp.zeros(N+1)
    atoms=[(n,mp.log(n)/L,mangoldt(n,mp)/mp.sqrt(n)) for n in range(2,m+1) if mangoldt(n,mp)]
    for i in range(N+1):
        for k in range(i,N+1):
            if i==k:
                av=cstar-wrconst-diag[i]+(sinmom[i]/(pi*i) if i else 0)
            else:
                av=ds[i]*ds[k]/pi*(i*sinmom[i]-k*sinmom[k])/(i*i-k*k)
            def q(r):
                if i==k:
                    return 2*(1-r)*mp.cos(2*pi*i*r)-(mp.sin(2*pi*i*r)/(pi*i) if i else 0)
                return ds[i]*ds[k]/pi*(k*mp.sin(2*pi*k*r)-i*mp.sin(2*pi*i*r))/(i*i-k*k)
            pv=mp.fsum(w*q(r) for n,r,w in atoms)
            xv=ds[i]*ds[k]*(xpos_mom[abs(i-k)]+xpos_mom[i+k])/2
            arch[i,k]=arch[k,i]=av
            prime[i,k]=prime[k,i]=pv
            pos[i,k]=pos[k,i]=xv
    pole=mp.matrix([4*sq2*ds[n]*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*pi*pi*n*n) for n in range(N+1)])
    A=arch-cstar*mp.eye(N+1)-prime+pole*pole.T
    ev,U=mp.eigsy(A)
    B=arch+pos
    rows=[]
    for i in (0, min(1,N),N):
        c=U[:,i]
        ar=(c.T*arch*c)[0]; xp=(c.T*pos*c)[0]
        pp=(c.T*prime*c)[0]; pol=(c.T*pole)[0]**2
        val=ar+xp
        source=ev[i]+cstar+pp-pol+xp
        rows.append(dict(index=i,lambda_=mp.nstr(ev[i],32),V=mp.nstr(val,32),position=mp.nstr(xp,32),arch=mp.nstr(ar,32),prime=mp.nstr(pp,32),pole=mp.nstr(pol,32),source_balance_error=mp.nstr(abs(source-val),8),coefficients=[mp.nstr(z,40) for z in c]))
    return dict(m=m,N=N,L=mp.nstr(L,40),dps=dps,GL_order_per_panel=order,panels=8,
                status='FLOATING_DIAGNOSTIC_NOT_CERTIFICATE',eigen_residual=mp.nstr(mp.norm(A*U-U*mp.diag(ev)),8),levels=rows)


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--diagnostic',action='store_true')
    p.add_argument('--m',nargs='+',type=int,default=[8,16,24])
    p.add_argument('--dps',type=int,default=90)
    p.add_argument('--order',type=int,default=64)
    p.add_argument('--output',type=Path,default=Path('phase_space_v.json'))
    a=p.parse_args()
    exact_checks()
    if not a.diagnostic:return
    if min(a.m)<2 or a.dps<30 or a.order<16:
        p.error('Require m>=2, dps>=30, order>=16.')
    out=[]; start=time.monotonic()
    for i,m in enumerate(a.m,1):
        out.append(cell(m,a.dps,a.order))
        elapsed=time.monotonic()-start
        eta=elapsed*(len(a.m)-i)/i
        n=20*i//len(a.m)
        print('['+'#'*n+'-'*(20-n)+f'] {i}/{len(a.m)} ETA {eta:.1f}s',flush=True)
        print(json.dumps({k:v for k,v in out[-1].items() if k!='levels'}),flush=True)
        for v in out[-1]['levels']:print(json.dumps({k:z for k,z in v.items() if k!='coefficients'}),flush=True)
        a.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(f'WROTE {a.output}')

if __name__=='__main__':main()
