"""Fixed-N physical dilation formulas; DIAGNOSTIC_NEVER_A_PROOF.

No eigenproblem is solved by this module. Active zero coordinates are fixed.
"""
import mpmath as mp

def Erow_and_dot(z,N,L):
    b=L/2;out=[];dot=[]
    oms=[2*mp.pi*n/L for n in range(N+1)]
    if z and min(abs(z-w) for w in oms)>mp.mpf('1e-50'):
        sn=mp.sin(z*b);co=mp.cos(z*b);root=mp.sqrt(L)
        for n,w in enumerate(oms):
            d=mp.mpf(1) if n==0 else mp.sqrt(2);den=z*z-w*w
            val=2*d*z*sn/(root*den)
            deriv=2*d/root*((sn+z*b*co)/den-2*z*z*sn/(den*den))
            out.append(val);dot.append(val/2+z*deriv)
        return out,dot
    def sincprime(x):return (x*mp.cos(x)-mp.sin(x))/(x*x) if x else mp.mpf(0)
    for n in range(N+1):
        d=mp.mpf(1) if n==0 else mp.sqrt(2)
        w=2*mp.pi*n/L
        pref=d*(-1)**n*b/mp.sqrt(L)
        zm=(z-w)*b;zp=(z+w)*b
        val=pref*(mp.sinc(zm)+mp.sinc(zp))
        deriv=pref*b*(sincprime(zm)+sincprime(zp))
        out.append(val);dot.append(val/2+z*deriv)
    return out,dot

def correlation_coefficients(c,L):
    N=len(c)-1;ds=[mp.mpf(1)]+[mp.sqrt(2)]*N
    C=[2*x*x for x in c];S=[mp.mpf(0)]*(N+1)
    for n in range(1,N+1):S[n]-=c[n]*c[n]/(mp.pi*n)
    for i in range(N+1):
        for j in range(i+1,N+1):
            t=2*c[i]*c[j]*ds[i]*ds[j]/mp.pi/(i*i-j*j)
            S[j]+=t*j;S[i]-=t*i
    e=mp.fsum(c[n]*ds[n] for n in range(N+1))/mp.sqrt(L)
    oms=[2*mp.pi*n/L for n in range(N+1)];cc=[c[n]*ds[n]/mp.sqrt(L) for n in range(N+1)]
    ap=[-C[n]/L+S[n]*oms[n] for n in range(N+1)];bp=[-C[n]*oms[n] for n in range(N+1)]
    def values(s):
        co=mp.cos(2*mp.pi*s/L);si=mp.sin(2*mp.pi*s/L);cn=mp.mpf(1);sn=mp.mpf(0)
        q=mp.mpf(0);qp=mp.mpf(0);ed=mp.mpf(0)
        r=1-s/L
        for n in range(N+1):
            q+=C[n]*r*cn+S[n]*sn
            qp+=ap[n]*cn+bp[n]*r*sn
            ed+=cc[n]*cn
            cn,sn=cn*co-sn*si,sn*co+cn*si
        return q,qp,ed
    def Q(s):return values(s)[0]
    def Qprime(s):return values(s)[1]
    def edge_shift(s):return values(s)[2]
    Q.all_values=values
    def only(s):
        co=mp.cos(2*mp.pi*s/L);si=mp.sin(2*mp.pi*s/L);cn=mp.mpf(1);sn=mp.mpf(0);q=mp.mpf(0);r=1-s/L
        for n in range(N+1):
            q+=C[n]*r*cn+S[n]*sn;cn,sn=cn*co-sn*si,sn*co+cn*si
        return q
    Q.only=only
    return Q,Qprime,edge_shift,e

def direct_I(c,L,s):
    N=len(c)-1;ell=L-s;ds=[mp.mpf(1)]+[mp.sqrt(2)]*N
    def sins(theta):
        co=mp.cos(theta);si=mp.sin(theta);cn=mp.mpf(1);sn=mp.mpf(0);out=[]
        for k in range(2*N+1):out.append(sn);cn,sn=cn*co-sn*si,sn*co+cn*si
        return out
    sa=sins(mp.pi*s/L);bb=mp.pi*ell/L;sb=sins(bb);sc=[mp.mpf(1)]+[sb[k]/(k*bb) for k in range(1,2*N+1)]
    sin_a=lambda k:sa[k] if k>=0 else -sa[-k]
    cc=[c[i]*ds[i]*(-1)**i for i in range(N+1)]
    return -mp.fsum(cc[i]*cc[j]*(2*mp.pi*j/L)*ell/(2*L)*(
        sin_a(j-i)*sc[j+i]+sa[j+i]*sc[abs(j-i)])
        for i in range(N+1) for j in range(1,N+1))

def projector_velocity(E,Ed,c,A,U=None,Q=None):
    if U is not None:
        project=lambda x:U*(U.T*x)
        F=E*U
        y=mp.lu_solve(F.T,U.T*c)
        z=Ed.T*y;pc=z-project(z);ac=A*c;r=ac-project(ac)
        return dict(Pi=None,project=project,dPi_c=pc,r=r,correction=2*(r.T*pc)[0])
    d=E.cols;Pi=E.T*(E*E.T)**-1*E
    y=mp.lu_solve(E*E.T,E*c)
    pc=(mp.eye(d)-Pi)*Ed.T*y
    r=(mp.eye(d)-Pi)*A*c
    corr=2*(r.T*pc)[0]
    return dict(Pi=Pi,project=lambda x:Pi*x,dPi_c=pc,r=r,correction=corr)
