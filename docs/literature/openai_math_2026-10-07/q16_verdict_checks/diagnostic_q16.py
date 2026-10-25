"""Noninterval checks on the literal finite P; no spectral/asymptotic certificate."""
from pathlib import Path
import json, hashlib, sys
import numpy as np
import scipy
from scipy.integrate import quad, quad_vec
R=Path(__file__).resolve().parent

def mangoldt(n):
    v=n; factors=[];p=2
    while p*p<=v:
        if v%p==0:
            factors.append(p)
            while v%p==0:v//=p
        p+=1
    if v>1:factors.append(v)
    return float(np.log(factors[0])) if len(factors)==1 else 0.0

def one_case(m,M):
    L=float(np.log(m));ell=2/9;J=int(np.ceil(L/ell));cnt=J+1
    js=np.arange(-M,M+1);om=2*np.pi*js/L
    C=np.column_stack([np.ones(len(js)),1/(.5-1j*om),1/(.5+1j*om)])
    Q,_=np.linalg.qr(C);P=np.eye(len(js))-Q@Q.conj().T
    seed=(js+M+1)**2+1j*((-1.)**js)*(js+M+2)
    c=P@seed;c/=np.linalg.norm(c)
    dh=-c/(om**2+.25)
    def fields(t):
        v=np.exp(1j*om*t)/np.sqrt(L)
        return np.dot(c,v),np.dot(dh,v),np.dot(1j*om*dh,v)
    def packets(t):
        if t<0 or t>L:return np.zeros(cnt,dtype=complex)
        f,h,hp=fields(t);i=min(int(np.floor(t/ell)),J);x=t/ell-i
        r=10*x**3-15*x**4+6*x**5
        rp=30*x*x*(1-x)**2/ell
        rpp=60*x*(1-x)*(1-2*x)/ell**2
        out=np.zeros(cnt,dtype=complex)
        out[i]=(1-r)*f-2*rp*hp-rpp*h
        if i+1<cnt:out[i+1]=r*f+2*rp*hp+rpp*h
        return out
    knots=[j*ell for j in range(1,J) if j*ell<L]
    rec=max(abs(np.sum(packets(t))-fields(t)[0]) for t in np.linspace(0,L,51))
    contacts=[]
    for sign in (-1,1):
        mom,_=quad_vec(lambda t:np.exp(sign*t/2)*packets(t),0,L,
                       points=knots,epsabs=2e-10,epsrel=2e-10)
        contacts.append(float(np.max(np.abs(mom))))
    density,_=quad(lambda t:float(np.sum(np.abs(packets(t))))**2,0,L,
                   points=knots,epsabs=2e-8,epsrel=2e-8,limit=300)
    Cret=1+8/ell+48/ell**2
    total=np.zeros((cnt,cnt),dtype=complex);direct=0.0
    for n in range(2,m+1):
        lam=mangoldt(n)
        if lam==0:continue
        s=float(np.log(n));a=lam/np.sqrt(n)
        Qn=np.empty((len(js),len(js)))
        for i,j in enumerate(js):
            for k,v in enumerate(js):
                Qn[i,k]=2*(1-s/L)*np.cos(om[i]*s) if j==v else (np.sin(om[k]*s)-np.sin(om[i]*s))/(np.pi*(j-v))
        direct+=a*float(np.real(np.vdot(c,Qn@c)))
        if L-s<=1e-14:continue
        pts=sorted(set(t for t in knots+[x-s for x in knots] if 0<t<L-s))
        z,_=quad_vec(lambda t:np.outer(np.conj(packets(t)),packets(t+s)),0,L-s,
                     points=pts,epsabs=2e-9,epsrel=2e-9)
        total+=a*(z+z.conj().T)
    mixed=float(np.real(np.sum(total)))
    mask=np.abs(np.arange(cnt)[:,None]-np.arange(cnt)[None,:])<=1
    near=float(np.max(np.abs(total[mask])))
    def qform(s):
        mat=np.empty((len(js),len(js)))
        for i,j in enumerate(js):
            for k,v in enumerate(js):
                mat[i,k]=2*(1-s/L)*np.cos(om[i]*s) if j==v else (np.sin(om[k]*s)-np.sin(om[i]*s))/(np.pi*(j-v))
        return float(np.real(np.vdot(c,mat@c)))
    cont,_=quad(lambda s:np.exp(s/2)*qform(s),0,L,epsabs=1e-10,epsrel=1e-10)
    hf=float(np.sum(np.abs(c)**2/(om**2+.25)))
    assert rec<1e-10 and max(contacts)<1e-7
    assert abs(direct-mixed)<1e-7*(1+abs(direct))
    assert near<1e-10 and density<Cret*Cret
    assert abs(cont+hf)<1e-9 and abs(direct)>1e-7
    return dict(m=m,M=M,packet_width=ell,packets=cnt,
       scope='FINITE_GENERAL_P_IDENTITY_CHECK_NOT_PRODUCTION_SMALL_EPSILON',
       reconstruction_max=rec,packet_contact_max=max(contacts),
       sum_packet_absolute_amplitudes_L2_squared=density,paid_upper=Cret*Cret,
       original_prime_quadratic_form=direct,all_mixed_packet_form=mixed,
       original_vs_reconstructed_error=abs(direct-mixed),
       near_prime_entries_max=near,continuous_plus_H_error=abs(cont+hf),
       dropping_mixed_packets_detected=True)

rows=[one_case(16,2),one_case(64,3)]
out={'status':'PASS_NONINTERVAL_IDENTITIES_NOT_SOURCE_SIGN_CERTIFICATES',
     'numpy':np.__version__,'scipy':scipy.__version__,'cases':len(rows),'rows':rows,
     'full_CCM_spectra_computed':False,'large_prime_sums_computed':False,
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(R/'diagnostic_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
