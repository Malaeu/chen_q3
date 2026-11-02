#!/usr/bin/env python3
"""EDGE_LAW_RELLICH_v1 normalization checks.
Run: uv run --with mpmath --with sympy python checks.py
m=8 is the original carrier size; N is held at m during local L dilation.
No finite experiment certifies a cofinal inequality or RH.
"""
from pathlib import Path
import json, time, os
import sympy as sp
import mpmath as mp
BASE=Path(__file__).resolve().parent
out={"exact":{},"numerical":{},"scope":"DIAGNOSTIC_NOT_INTERVAL"}
def exact():
    t=sp.symbols('t',real=True)
    E=sp.Matrix([[1,t,0],[0,1,t]])
    P=E.T*(E*E.T).inv()*E
    M=(E*E.T).inv()
    rhs=(sp.eye(3)-P)*sp.diff(E,t).T*M*E+E.T*M*sp.diff(E,t)*(sp.eye(3)-P)
    assert sp.simplify(sp.diff(P,t)-rhs)==sp.zeros(3)
    out['exact']['projector_derivative']=True
    a,b,d=sp.symbols('a b d',real=True)
    v=sp.Matrix([sp.cos(t),sp.sin(t)])
    AA=sp.Matrix([[a,b],[b,d]])
    deriv=sp.diff((v.T*AA*v)[0],t).subs(t,0)
    assert deriv==2*b
    out['exact']['nonstationary_moving_subspace']=str(deriv)
    z,om=sp.symbols('z om',positive=True)
    assert sp.factor(z/(z*z-om*om)-1/z-om*om/(z*(z*z-om*om)))==0
    out['exact']['rational_edge_split']=True
    X,edge=sp.symbols('X edge',real=True)
    assert sp.expand(2*(edge+X)**2-(2*edge**2+4*edge*X+2*X**2))==0
    out['exact']['edge_cross_square']=True
    assert (4*edge*X).subs({edge:1,X:-sp.Rational(1,2)})==-2
    out['exact']['negative_cross_plant']=True
    T=sp.symbols('T',positive=True)
    primitive=(sp.log(T/(2*sp.pi))+1)/T
    assert sp.simplify(sp.diff(primitive,T)+sp.log(T/(2*sp.pi))/T**2)==0
    out['exact']['phase_averaged_coefficient']=2
    tau,w=sp.symbols('tau w',real=True)
    assert sp.diff(-2*w*(1-sp.exp(-tau)),tau).subs(tau,0)==-2*w
    out['exact']['endpoint_atom_right_kick']='-2*w (unit constant trial)'
    print('EXACT 7 groups passed',flush=True)
def numeric():
    mp.mp.dps=int(os.environ.get("MP_DPS", "40"))
    gl=int(os.environ.get("GL_ORDER", "32"))
    N=8; L0=mp.log(8)
    nodes,weights=mp.gauss_quadrature(gl,'legendre')
    us=[]; ws=[]
    for k in range(4):
        for i in range(gl):
            us.append((k+(nodes[i]+1)/2)/4)
            ws.append(weights[i]/8)
    d=[mp.mpf(1)]+[mp.sqrt(2)]*N
    cstar=mp.euler+mp.log(8*mp.pi)+mp.pi/2
    zeros=[mp.im(mp.zetazero(k)) for k in range(1,4)]
    def sinc(x): return mp.sin(x)/x if x else mp.mpf(1)
    def qij(L,s,i,j):
        if s>=L:return mp.mpf(0)
        ell=L-s; oi=2*mp.pi*i/L; oj=2*mp.pi*j/L
        return d[i]*d[j]*(-1)**(i+j)*ell/L*(sinc((oi-oj)*ell/2)*mp.cos((oi+oj)*s/2)+sinc((oi+oj)*ell/2)*mp.cos((oj-oi)*s/2))
    def jj(s):return mp.exp(-s/2)/(-mp.expm1(-2*s))
    def mj(s):
        v=jj(s)
        return v+s*v*(-mp.mpf('0.5')-2/mp.expm1(2*s))
    def ap(L,n):
        om=2*mp.pi*n/L
        return mp.sqrt(2)*d[n]/mp.sqrt(L)*mp.sinh(L/4)/(mp.mpf('0.25')+om*om)
    lambdas={n:mp.log(next(iter(sp.factorint(n)))) for n in range(2,10) if len(sp.factorint(n))==1}
    def Eof(L):
        return mp.matrix([[2*d[n]*z*mp.sin(L*z/2)/(mp.sqrt(L)*(z*z-(2*mp.pi*n/L)**2)) for n in range(N+1)] for z in zeros])
    def Aof(L):
        H=mp.matrix(N+1)
        poles=[ap(L,n) for n in range(N+1)]
        tail=mp.fsum(mp.exp(-(mp.mpf('.5')+2*k)*L)/(mp.mpf('.5')+2*k) for k in range(35))
        for i in range(N+1):
            for j in range(i,N+1):
                ij=int(i==j)
                ar=L*mp.fsum(w*jj(u*L)*(2*ij-qij(L,u*L,i,j)) for u,w in zip(us,ws))+2*ij*tail
                primes=mp.fsum(v/mp.sqrt(n)*qij(L,mp.log(n),i,j) for n,v in lambdas.items() if mp.log(n)<L)
                H[i,j]=H[j,i]=-cstar*ij+ar-primes+poles[i]*poles[j]
        return H
    def select(L):
        E=Eof(L); U,R=mp.qr(E.T)
        U=U[:,:len(zeros)]
        A=Aof(L); eig,V=mp.eigsy(U.T*A*U)
        if L==L0:out['numerical']['saved_base_gap']=mp.nstr(eig[1]-eig[0],24)
        c=U*V[:,0]
        return eig[0],c,A,E
    lam,c,A,E=select(L0)
    print('NUM base source built',flush=True)
    P=E.T*(E*E.T)**-1*E
    Ed=mp.matrix([[mp.diff(lambda tau:Eof(L0*mp.exp(tau))[i,j],0) for j in range(N+1)] for i in range(len(zeros))])
    Pd=(mp.eye(N+1)-P)*Ed.T*(E*E.T)**-1*E+E.T*(E*E.T)**-1*Ed*(mp.eye(N+1)-P)
    r=(mp.eye(N+1)-P)*A*c
    corr=2*(r.T*Pd*c)[0]
    e=mp.fsum(d[i]*c[i] for i in range(N+1))/mp.sqrt(L0)
    def Q(s):return mp.fsum(c[i]*c[j]*qij(L0,s,i,j) for i in range(N+1) for j in range(N+1))
    p=mp.fsum(c[i]*ap(L0,i) for i in range(N+1))
    xpq=mp.fsum(c[i]*(2*L0*mp.diff(lambda x:ap(x,i),L0)-ap(L0,i)) for i in range(N+1))
    ar=-1-L0*mp.fsum(w*mj(u*L0)*Q(u*L0) for u,w in zip(us,ws))
    prime=mp.fsum(v/mp.sqrt(n)*mp.log(n)*mp.diff(Q,mp.log(n)) for n,v in lambdas.items() if n<8)
    virial=ar+p*p+p*xpq+prime
    kick=-2*mp.log(2)/mp.sqrt(8)*L0*e*e
    h=mp.mpf(os.environ.get('FD_H','1e-8'))
    lp,cp,Ap,Ep=select(L0*mp.exp(h))
    lm,cm,Am,Em=select(L0*mp.exp(-h))
    plus=(lp-lam)/h
    minus=(lam-lm)/h
    expected_plus=virial+corr+kick
    expected_minus=virial+corr
    errplus=abs(plus-expected_plus);errminus=abs(minus-expected_minus)
    # Independent direct interior integral checks the boundary in Q'.
    def ff(x):
        return mp.fsum(c[n]*d[n]*(-1)**n*mp.cos(2*mp.pi*n*x/L0) for n in range(N+1))/mp.sqrt(L0)
    def fp(x):
        return mp.fsum(-c[n]*d[n]*(-1)**n*(2*mp.pi*n/L0)*mp.sin(2*mp.pi*n*x/L0) for n in range(1,N+1))/mp.sqrt(L0)
    leibniz_errors=[]
    for ss in [L0/7,mp.log(2),mp.log(5),L0*mp.mpf('.95')]:
        ell=L0-ss
        integ=ell*mp.fsum(w*ff(-L0/2+u*ell)*fp(-L0/2+u*ell+ss) for u,w in zip(us,ws))
        leibniz_errors.append(abs(mp.diff(Q,ss)-(2*integ-2*e*ff(L0/2-ss))))
    out['numerical']['leibniz_max_error']=mp.nstr(max(leibniz_errors),24)
    leibniz_error=max(leibniz_errors)
    assert leibniz_error<mp.mpf('1e-24')
    vals={'m':8,'N_fixed':8,'dps':mp.mp.dps,'GL_per_panel':gl,'panels':4,'lambda':lam,'edge':e,'source_left_virial':virial,'projector_correction':corr,'prime8_kick':kick,'fd_left':minus,'pred_left':expected_minus,'fd_right':plus,'pred_right':expected_plus,'abs_error_left':errminus,'abs_error_right':errplus,'projector_rank':3,'orthogonality_error':mp.norm(P*c-c),'FD_h':h,'leibniz_max_error':leibniz_error}
    out['numerical'].update({k:mp.nstr(v,24) if isinstance(v,mp.mpf) else v for k,v in vals.items()})
    assert errplus<mp.mpf('1e-5') and errminus<mp.mpf('1e-5')
    assert abs(corr)>mp.mpf('1e-12')
    out['numerical']['passed']=True
exact()
started=time.monotonic()
numeric()
out['elapsed_seconds']=time.monotonic()-started
(BASE/os.environ.get('RESULT_NAME','results.json')).write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps(out,indent=2),flush=True)
