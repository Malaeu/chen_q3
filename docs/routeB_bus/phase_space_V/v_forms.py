"""Literal even CCM and fixed physical phase-space V matrices.

DIAGNOSTIC_NEVER_A_PROOF. Apositive uses the full jump kernel
j(s)=exp(-s/2)/(1-exp(-2s)); no frequency cutoff or x/L rescaling.
"""
from pathlib import Path
import mpmath as mp

def mangoldt(n):
    for p in range(2,n+1):
        if n%p==0:
            q=n
            while q%p==0:q//=p
            return mp.log(p) if q==1 else mp.mpf(0)
    return mp.mpf(0)

def theta(x):
    x=abs(x);u=mp.exp(2*x);v=mp.mpf(0);n=1
    while mp.pi*n*n*u<mp.mpf('2.5')*mp.mp.prec:
        y=mp.pi*n*n*u;v+=(16*y*y-24*y)*mp.exp(-y);n+=1
    return mp.exp(x/2)*v

def q_even(x,i,k,L,clip=False):
    if clip and x>=L:return mp.mpf(0)
    r=x/L
    if i==k:
        return 2*(1-r)*mp.cos(2*mp.pi*i*r)-(mp.sin(2*mp.pi*i*r)/(mp.pi*i) if i else 0)
    di=mp.sqrt(2) if i else 1;dk=mp.sqrt(2) if k else 1
    return di*dk/mp.pi*(k*mp.sin(2*mp.pi*k*r)-i*mp.sin(2*mp.pi*i*r))/(i*i-k*k)

def build_forms(window_m,N,dps=140,order=128):
    mp.mp.dps=dps;L=mp.log(window_m);sq2=mp.sqrt(2)
    gn,gw=mp.gauss_quadrature(order,'legendre');nodes=[]
    for panel in range(8):
        for z,w in zip(gn,gw):nodes.append(((mp.mpf(panel)+(z+1)/2)/8,w/16))
    coss=[[mp.cos(2*mp.pi*n*y) for y,w in nodes] for n in range(2*N+1)]
    sins=[[mp.sin(2*mp.pi*n*y) for y,w in nodes] for n in range(N+1)]
    ss=[L*y for y,w in nodes];ww=[L*w for y,w in nodes]
    js=[mp.exp(-s/2)/(-mp.expm1(-2*s)) for s in ss]
    sinmom=[mp.fsum(w*j*sn for w,j,sn in zip(ww,js,sins[n])) for n in range(N+1)]
    diag=[]
    for n in range(N+1):
        diag.append(mp.fsum(L*w*(mp.expm1(s/2)-mp.exp(s/2)*y-2*mp.exp(s/2)*(1-y)*mp.sin(mp.pi*n*y)**2)/mp.sinh(s)
            for (y,w),s in zip(nodes,ss)))
    xm=[mp.log1p((L*(y-mp.mpf('.5')))**2) for y,w in nodes]
    xpos_mom=[mp.fsum(w*x*c for (y,w),x,c in zip(nodes,xm,coss[n])) for n in range(2*N+1)]
    hvals=[theta(L*(y-mp.mpf('.5'))) for y,w in nodes]
    h=mp.matrix([mp.sqrt(L)*(1 if n==0 else sq2)*mp.fsum(w*hv*cs for (y,w),hv,cs in zip(nodes,hvals,coss[n])) for n in range(N+1)])
    cstar=mp.euler+mp.log(8*mp.pi)+mp.pi/2
    wrconst=mp.euler+mp.log(4*mp.pi*mp.tanh(L/2));ds=[mp.mpf(1)]+[sq2]*N
    arch=mp.zeros(N+1);prime=mp.zeros(N+1);spatial=mp.zeros(N+1)
    atoms=[(k,mp.log(k),mangoldt(k)/mp.sqrt(k)) for k in range(2,window_m+1) if mangoldt(k)]
    for i in range(N+1):
        for k in range(i,N+1):
            av=cstar-wrconst-diag[i]+(sinmom[i]/(mp.pi*i) if i else 0) if i==k else ds[i]*ds[k]/mp.pi*(i*sinmom[i]-k*sinmom[k])/(i*i-k*k)
            pv=mp.fsum(w*q_even(x,i,k,L,clip=True) for _,x,w in atoms)
            xv=ds[i]*ds[k]*(xpos_mom[abs(i-k)]+xpos_mom[i+k])/2
            arch[i,k]=arch[k,i]=av;prime[i,k]=prime[k,i]=pv;spatial[i,k]=spatial[k,i]=xv
    pole=mp.matrix([4*sq2*ds[n]*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*mp.pi**2*n*n) for n in range(N+1)])
    K=arch-cstar*mp.eye(N+1)-prime+pole*pole.T
    return dict(window_m=window_m,N=N,L=L,K=K,arch=arch,spatial=spatial,h=h,prime=prime,pole=pole,cstar=cstar,
                nodes=nodes,dps=dps,order=order,atoms=atoms)

def quantities(forms,f,K=None):
    f=f/mp.norm(f);n=f.rows;ar=forms['arch'][:n,:n];sp=forms['spatial'][:n,:n];h=forms['h'][:n,:]
    a=mp.fdot(f,ar*f);x=mp.fdot(f,sp*f)
    return dict(arch=a,spatial=x,V=a+x,w0=mp.fdot(f,h)**2/mp.fdot(h,h),
                Rayleigh=mp.fdot(f,(K if K is not None else forms['K'][:n,:n])*f))
