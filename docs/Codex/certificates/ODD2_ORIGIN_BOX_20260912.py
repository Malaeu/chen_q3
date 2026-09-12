"""Bounded whole-box proof attempt; no acceptance is implied by execution.

Raw source F=Phi. Fixed target 0<x,y<=1/4, total Taylor degree32.
Uses a byte-pinned reviewed interval class, not a new arithmetic dependency.
All signs are whole polynomial Bernstein enclosures plus full remainders.
"""
import os, sys, json, math, hashlib, importlib.util, time
from pathlib import Path
from fractions import Fraction as Q

BASE=Path(__file__).resolve().parent
SOURCE=BASE/'ODD2COMPACT_BOUNDARY_CERT_20260912.py'
assert hashlib.sha256(SOURCE.read_bytes()).hexdigest()=='27c072e2ae3ee548f52c9b01008c3161a968060dd133420fcaeb83892e33eebe'
os.environ['ODD2COMPACT_PREC']='100'
spec=importlib.util.spec_from_file_location('reviewed_interval_source',SOURCE)
iv=importlib.util.module_from_spec(spec);spec.loader.exec_module(iv)
B,rat,PI,DN,UP=iv.B,iv.rat,iv.PI,iv.DN,iv.UP

DEGREE=32; MOMENTS=DEGREE+1; ORDER=8; MODES=20; VMAX=3
CELLS=int(sys.argv[1]) if len(sys.argv)>1 else 512
assert CELLS in (128,512)
DELTA=Q(1,4); UMAX=DELTA**2; CAUCHY_R=Q(1,2)
MAXJ=2*DEGREE
P=[[Q(0),Q(-6),Q(4)]]
for j in range(MAXJ):
    old=P[-1];new=[Q(0)]*(len(old)+1)
    for k,q in enumerate(old):new[k]+=(Q(1,2)+2*k)*q;new[k+1]-=2*q
    P.append(new)
D=[]
for j,p in enumerate(P):
    nu=Q(4*j+9,4)
    D.append(rat(Q(16,15)*sum(abs(q) for q in p)*nu**math.ceil(nu)))
PB=[[rat(q) for q in poly] for poly in P]
TH=[(d*(-PI*rat(Q((MODES+1)**2,2))).exp()).hi for d in D]

def fvals(x,last):
    assert x.lo>=0
    ex=(2*x).exp();eh=(x/2).exp();s=[B(0) for _ in range(last+1)]
    for n in range(1,MODES+1):
        z=PI*(n*n)*ex;ez=(-z).exp()
        for j in range(last+1):
            p=B(0)
            for q in reversed(PB[j]):p=p*z+q
            s[j]=s[j]+p*ez
    return [eh*s[j]+iv.symmetric(TH[j]) for j in range(last+1)]

def moment_derivative(v,fs,j,k):
    a=sum((math.comb(k,h)*fs[j+h]*fs[j+k-h] for h in range(k+1)),B(0))
    if not k:return v*a
    b=sum((math.comb(k-1,h)*fs[j+h]*fs[j+k-1-h] for h in range(k)),B(0))
    return v*a+k*b

def integrate_moments():
    h=Q(VMAX,CELLS)
    weights=[rat(h**(k+1)/(2**k*(k+1)*math.factorial(k))) for k in range(0,ORDER,2)]
    rw=rat(h**9/(2**8*9*math.factorial(8)))
    vals=[B(0) for _ in range(MOMENTS+1)];errs=[B(0) for _ in vals]
    for i in range(CELLS):
        v=rat((Q(i)+Q(1,2))*h);fs=fvals(v,MOMENTS+ORDER-2)
        for j in range(1,MOMENTS+1):
            for k,w in zip(range(0,ORDER,2),weights):
                vals[j]=vals[j]+w*moment_derivative(v,fs,j,k)
        cell=B(rat(i*h).lo,rat((i+1)*h).hi);fs=fvals(cell,MOMENTS+ORDER)
        for j in range(1,MOMENTS+1):
            errs[j]=errs[j]+rw*B(moment_derivative(cell,fs,j,ORDER).absup())
        if (i+1)%32==0:print(json.dumps({'stage':'moment_cells','done':i+1,'total':CELLS}),file=sys.stderr,flush=True)
    tails=[B(0)]+[D[j].square()*(-PI*B(2*VMAX).exp()).exp()/(2*PI) for j in range(1,MOMENTS+1)]
    return [vals[j]+iv.symmetric((errs[j]+tails[j]).hi) for j in range(MOMENTS+1)],errs,tails

def origin_jets(mom,f0):
    """Source PDE gives all odd jets from one central jet per antidiagonal."""
    out={}
    for n in range(1,MOMENTS+1):
        if n%2:
            r=q=n;val=4*mom[n]-2*n*f0[n-1].square()
        else:
            r=n-1;q=n+1;val=-4*mom[n]-2*(n-1)*f0[n-2]*f0[n]
        out[r,q]=out[q,r]=val
        while r>1:
            r-=2;q+=2
            val=val-2*r*f0[r-1]*f0[q-1]+2*(q-2)*f0[r+1]*f0[q-3]
            out[r,q]=out[q,r]=val
    return out

def polynomial(jets):
    return {(p,q):jets[2*p+1,2*q+1]*rat(UMAX**(p+q)/
                (math.factorial(2*p+1)*math.factorial(2*q+1)))
            for p in range(DEGREE+1) for q in range(DEGREE+1-p)}

def curvature_numerator(poly):
    """Exact cancellation: unordered pair coefficient (p-r)(q-s)."""
    out={};items=list(poly.items())
    for i,((p,q),a) in enumerate(items):
        for (r,s),b in items[i+1:]:
            c=(p-r)*(q-s)
            if not c:continue
            key=(p+r-1,q+s-1);assert min(key)>=0
            out[key]=out.get(key,B(0))+c*a*b
    return out

def bernstein(poly):
    """Power coefficients on [0,1]^2 to a tensor Bernstein enclosure."""
    m=max(p for p,q in poly);n=max(q for p,q in poly)
    wx=[[rat(Q(math.comb(i,p),math.comb(m,p))) for p in range(i+1)] for i in range(m+1)]
    wy=[[rat(Q(math.comb(j,q),math.comb(n,q))) for q in range(j+1)] for j in range(n+1)]
    first={}
    for i in range(m+1):
        for q in range(n+1):
            first[i,q]=sum((wx[i][p]*poly[p,q] for p in range(i+1) if (p,q) in poly),B(0))
    co=[]
    for i in range(m+1):
        for j in range(n+1):
            co.append(sum((wy[j][q]*first[i,q] for q in range(j+1)),B(0)))
    return B(min(v.lo for v in co),max(v.hi for v in co)),[m,n]

def abs_poly_derivative(poly,a,b):
    s=B(0)
    for (p,q),v in poly.items():
        if p<a or q<b:continue
        c=math.factorial(p)//math.factorial(p-a)*math.factorial(q)//math.factorial(q-b)
        s=s+c*B(v.absup())
    return s.hi

def cauchy_tails():
    # On |s|,|t|<=1/2, |F(v+s)|<=1050 exp(-exp(2v)/8).
    # Each V integral <=2*1050^2; |Kraw|<=4*1050^2=4410000.
    # Odd-power Cauchy gives |T_pq|<=4M*4^(p+q).
    k=DEGREE+1;r=UMAX/CAUCHY_R**2;M=Q(4*1050**2);C=4*M
    t00=C*(k+1)*r**k/(1-r*Q(k+2,k+1))
    t10=C*Q(k*(k+1),2)*r**k/(1-r*Q(k+2,k))
    t11=C*Q(k*(k+1)*(k-1),6)*r**k/(1-r*Q(k+2,k-1))
    return tuple(rat(x) for x in (t00,t10,t11))

def exact_tests():
    iv.self_tests()
    a={(0,0):B(2),(1,0):B(3),(0,1):B(3),(1,1):B(5)}
    n=curvature_numerator(a);assert set(n)=={(0,0)} and n[0,0].out()==['1','1']
    z,_=bernstein({(0,0):B(1),(1,0):B(-1),(2,0):B(1)})
    assert z.lo<=Q(1,2)<=z.hi and z.hi==1

def main():
    started=time.monotonic();exact_tests()
    print(json.dumps({'stage':'start','degree':DEGREE,'box':'[0,1/4]^2','cells':CELLS,'precision':100}),file=sys.stderr,flush=True)
    mom,errs,vtails=integrate_moments();f0=fvals(B(0),MAXJ)
    jets=origin_jets(mom,f0)
    assert jets[1,1].lo>0
    # Cross-check the first off-diagonal central identity without the recurrence.
    assert jets[1,3].out()==(-4*mom[2]-2*f0[0]*f0[2]).out()
    poly=polynomial(jets);np=curvature_numerator(poly)
    print(json.dumps({'stage':'bernstein','terms':len(poly),'numerator_terms':len(np)}),file=sys.stderr,flush=True)
    pb,pd=bernstein(poly);nb,nd=bernstein(np)
    e0,e1,e2=cauchy_tails()
    a0=abs_poly_derivative(poly,0,0);a1=abs_poly_derivative(poly,1,0)
    a2=abs_poly_derivative(poly,0,1);a12=abs_poly_derivative(poly,1,1)
    error=(B(a0)*e2+B(a12)*e0+e0*e2+B(a1)*e1+B(a2)*e1+e1.square()).hi
    actual_p=pb+iv.symmetric(e0.hi);actual_n=nb+iv.symmetric(error)
    good=actual_p.lo>0 and actual_n.lo>0
    result={'status':'POSITIVE_WHOLE_BOX_CANDIDATE' if good else 'INCONCLUSIVE_WHOLE_BOX_ENCLOSURE',
      'accepted':False,'box_x_y':'[0,1/4]^2','precision':100,'degree':DEGREE,'cells':CELLS,'modes':MODES,'vmax':VMAX,
      'pi':PI.out(),'interval_dependency_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'P_Bernstein':pb.out(),'N_Bernstein':nb.out(),'P_degree':pd,'N_degree':nd,
      'cauchy_tails':[x.out() for x in (e0,e1,e2)],'polynomial_derivative_abs':[str(x) for x in (a0,a1,a2,a12)],
      'N_error':str(error),'P_full':actual_p.out(),'N_full':actual_n.out(),
      'moments':{str(j):mom[j].out() for j in range(1,MOMENTS+1)},
      'moment_Taylor_errors':{str(j):errs[j].out() for j in range(1,MOMENTS+1)},
      'moment_v_tails':{str(j):vtails[j].out() for j in range(1,MOMENTS+1)},
      'theta_tails':[str(v) for v in TH],
      'origin_K11':jets[1,1].out(),'origin_K13':jets[1,3].out(),'origin_K33':jets[3,3].out(),
      'seconds':time.monotonic()-started,'global_ODD2':False,'RH_claim':False}
    if good:
        constant=(B(actual_n.lo)*(B(actual_p.lo)/B(actual_p.hi)).square()/rat(UMAX**2)).lo
        result['Delta_raw_over_x2_y2_squared_gap_lower']=str(constant)
    return result

if __name__=='__main__':print(json.dumps(main(),indent=2),flush=True)
