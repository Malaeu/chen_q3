"""Scalar fixed-N source and analytic dilation, no source eigenproblem.

The source at a varied length retains all integer atoms with log(n)<L;
at the equality endpoint the atom value is zero and the two slopes differ.
"""
import mpmath as mp
from rellich_helpers import correlation_coefficients

def weights(world,limit):
    if world=='dh':
        tau=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
        a=[mp.mpf(0),mp.mpf(1),tau,-tau,mp.mpf(-1)];b=[mp.mpf(0)]*(limit+1)
        for n in range(2,limit+1):b[n]=a[n%5]*mp.log(n)-mp.fsum(b[d]*a[(n//d)%5] for d in range(2,n) if n%d==0)
    else:
        b=[mp.mpf(0)]*(limit+1)
        for n in range(2,limit+1):
            k=n;p=next((p for p in range(2,n+1) if n%p==0),n)
            while k%p==0:k//=p
            if k==1:b[n]=mp.log(p)
    return b

def panels(order,number=8):
    gn,gw=mp.gauss_quadrature(order,'legendre')
    return [((p+(x+1)/2)/number,w/(2*number)) for p in range(number) for x,w in zip(gn,gw)]

def source_scalar(c,N,L,world,order=128,quad=None,all_terms=True):
    Q,Qp,edge,e=correlation_coefficients(c,L);norm=mp.fsum(x*x for x in c)
    alpha=mp.mpf('1.5') if world=='dh' else mp.mpf('.5')
    j=lambda s:mp.exp(-alpha*s)/(-mp.expm1(-2*s))
    quad=quad or panels(order)
    H=mp.mpf(0);archdot=mp.mpf(0);Barch=mp.mpf(0);Varch=mp.mpf(0)
    for y,w in quad:
        s=y*L;wt=L*w*j(s)
        q,qp,ed=Q.all_values(s) if all_terms else (Q.only(s),mp.mpf(0),mp.mpf(0))
        H+=wt*(2*norm-q)
        if all_terms:
            archdot+=wt*s*qp;Barch+=wt*s*ed;Varch+=wt*s*(qp+2*e*ed)
    a=mp.exp(-L/2)
    tail=(mp.atanh(a)-mp.atan(a)) if world=='dh' else mp.atanh(a)+mp.atan(a)
    H+=2*norm*tail
    bn=weights(world,int(mp.floor(mp.exp(L)))+1)
    prime=mp.mpf(0);atomdot=mp.mpf(0);Batom=mp.mpf(0);Vatom=mp.mpf(0)
    for n in range(2,len(bn)):
        s=mp.log(n)
        if not bn[n] or s>=L:continue
        q,qp,ed=Q.all_values(s) if all_terms else (Q.only(s),mp.mpf(0),mp.mpf(0));w=bn[n]/mp.sqrt(n);prime+=w*q
        if all_terms:atomdot+=w*s*qp;Batom+=w*s*ed;Vatom+=w*s*(qp+2*e*ed)
    pole=mp.mpf(0);poledot=mp.mpf(0)
    if world=='dh':constant=mp.log(5/mp.pi)+mp.digamma(mp.mpf('.75'))
    else:
        constant=-mp.euler-mp.log(8*mp.pi)-mp.pi/2
        def pp(n,ell):
            d=mp.mpf(1) if n==0 else mp.sqrt(2);om=2*mp.pi*n/ell
            return mp.sqrt(2)*d/mp.sqrt(ell)*mp.sinh(ell/4)/(mp.mpf('.25')+om*om)
        p=mp.fsum(c[n]*pp(n,L) for n in range(N+1))
        pole=p*p
        if all_terms:
            t=mp.fsum(c[n]*(2*L*mp.diff(lambda ell:pp(n,ell),L)-pp(n,L)) for n in range(N+1));poledot=p*p+p*t
    energy=constant*norm+H-prime+pole
    if not all_terms:return dict(energy=energy,norm=norm,edge=e)
    B=Barch+Batom
    boundary=-2*e*B
    volume=Varch+Vatom+poledot
    return dict(energy=energy,virial=archdot+atomdot+poledot,archdot=archdot,atomdot=atomdot,poledot=poledot,boundary=boundary,volume=volume,edge=e,norm=norm)
