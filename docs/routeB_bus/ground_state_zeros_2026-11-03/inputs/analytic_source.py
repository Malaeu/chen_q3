"""Diagnostic analytic arch moments; compare with pinned quadrature before use.

All literal prime/Dirichlet atoms, arch tail and poles are retained. No zero-side
Gram, positivity assumption or eigenvalue clipping. Rounding is not an enclosure.
"""
import sys,time
sys.path.insert(0,'/workspace/conditioning_deps')
import gmpy2 as g
import numpy as np
from flint import arb,acb,ctx
from functools import lru_cache

@lru_cache(None)
def coefficients(M,bits):
    g.get_context().precision=bits+40
    f=g.mpfr;zero=f(0);tau=(g.sqrt(10-2*g.sqrt(5))-2)/(g.sqrt(5)-1)
    aa=[zero,f(1),tau,-tau,f(-1)];dh=[zero]*(M+1);ze=[zero]*(M+1)
    for n in range(2,M+1):
        dh[n]=aa[n%5]*g.log(n)-sum((dh[d]*aa[(n//d)%5] for d in range(2,n) if n%d==0),zero)
    sieve=[True]*(M+1)
    for p in range(2,M+1):
        if sieve[p]:
            for j in range(p*p,M+1,p):sieve[j]=False
            j=p
            while j<=M:ze[j]=g.log(p);j*=p
    return ze,dh

def build(m,bits=512):
    start=time.monotonic();g.get_context().precision=bits+40;ctx.prec=bits+72
    f=g.mpfr;zero=f(0);one=f(1);pi=g.const_pi();L=g.log(m);digits=int((bits+48)*.30103)+12
    def mid(x):return f(x.mid().str(digits,radius=False))
    ds=[one]+[g.sqrt(2)]*m;moment=[];diagonal=[];tail_lengths=[]
    for alpha in [f('.5'),f('1.5')]:
        step=g.exp(-2*L);E=g.exp(-alpha*L);a=alpha;terms=[];cut=g.exp2(-bits-48)
        while E>cut:
            terms.append((a,E));a+=2;E*=step
        tail_lengths.append(len(terms));z0=acb(arb(str(alpha/2)));p0=mid(z0.digamma().real)
        trig0=mid(z0.polygamma(1).real)
        sm=[zero];di=[trig0/(2*L)-2/L*sum((e/(a*a) for a,e in terms),zero)-2*sum((e/a for a,e in terms),zero)]
        for n in range(1,m+1):
            omega=2*pi*n/L;w2=omega*omega;z=acb(arb(str(alpha/2)),arb(str(omega/2)))
            psi=z.digamma();tri=z.polygamma(1)
            re,im=mid(psi.real),mid(psi.imag);rt=mid(tri.real)
            st=zero;dt=zero
            for a,e in terms:
                aa=a*a;den=aa+w2
                st+=omega*e/den
                dt+=e*(2*w2/(a*den)+4*aa/(L*den*den)+2*a/den)
            sm.append(im/2-st)
            di.append(re-p0+rt/(2*L)+im/(L*omega)-dt)
        moment.append(sm);diagonal.append(di)
    bs=coefficients(max(300,m),bits);ratios=[g.log(k)/L for k in range(2,m)]
    co=[g.cos(2*pi*r) for r in ratios];si=[g.sin(2*pi*r) for r in ratios]
    cs=[one]*len(ratios);sn=[zero]*len(ratios);ps=[[],[]];pd=[[],[]]
    weights=[[b[k]/g.sqrt(k) for k in range(2,m)] for b in bs]
    for n in range(m+1):
        term=[2*(1-r)*c-(s/(pi*n) if n else zero) for r,c,s in zip(ratios,cs,sn)]
        for k in range(2):
            ps[k].append(sum((w*s for w,s in zip(weights[k],sn)),zero))
            pd[k].append(sum((w*t for w,t in zip(weights[k],term)),zero))
        cs,sn=([c*u-s*v for c,s,u,v in zip(cs,sn,co,si)], [s*u+c*v for c,s,u,v in zip(cs,sn,co,si)])
    out={};z=g.exp(-L/2)
    for k,world in enumerate(['zeta','dh']):
        c=-g.const_euler()-g.log(8*pi/(5 if k else 1))+(pi/2 if k else -pi/2)
        tail=g.atanh(z)+(-g.atan(z) if k else g.atan(z));beta=[a+b for a,b in zip(moment[k],ps[k])]
        E=np.empty((m+1,m+1),object);O=np.empty((m,m),object)
        for i in range(m+1):
            E[i,i]=c+diagonal[k][i]+2*tail-pd[k][i]
            if i:O[i-1,i-1]=E[i,i]-2*beta[i]/(pi*i)
            for j in range(i+1,m+1):
                E[i,j]=E[j,i]=ds[i]*ds[j]/pi*(i*beta[i]-j*beta[j])/(i*i-j*j)
                if i:O[i-1,j-1]=O[j-1,i-1]=2/pi*(j*beta[i]-i*beta[j])/(i*i-j*j)
        if not k:
            pole=np.array([4*g.sqrt(2)*ds[n]*L**f('1.5')*g.sinh(L/4)/(L*L+16*pi*pi*n*n) for n in range(m+1)],object)
            odd=np.array([32*pi*n*g.sqrt(L)*g.sinh(L/4)/(L*L+16*pi*pi*n*n) for n in range(1,m+1)],object)
            E+=np.outer(pole,pole);O-=np.outer(odd,odd)
        out[world]=(E,O)
    w=g.mpc(2*pi/g.log(2),f('.25'));ss=g.sin(w*L/2)
    ev=np.array([2*ds[n]*w*ss/(g.sqrt(L)*(w*w-(2*pi*n/L)**2)) for n in range(m+1)],object)
    ov=np.array([g.sqrt(2/L)*2*(2*pi*n/L)*ss/(w*w-(2*pi*n/L)**2) for n in range(1,m+1)],object)
    out['plant']=(out['zeta'][0]+np.array([[4*(a*b).real for b in ev] for a in ev],object),out['zeta'][1]+np.array([[4*(a*b).real for b in ov] for a in ov],object))
    meta=dict(bits=bits,working_bits=bits+40,special_function_bits=bits+72,tail_lengths=tail_lengths,tail_cut=str(cut),seconds=time.monotonic()-start,source='literal analytic digamma arch+geometric endpoint correction+all signed atoms+tail+poles',interval_certificate=False)
    return out,meta
