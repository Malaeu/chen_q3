#!/usr/bin/env python3
"""Source-exact all-vector certificate. Requires mpmath, sympy.
Elementary iv intervals + proved Binet/Bessel remainders + integer Bareiss.
No interval eigenvalues, Arb, Lean, or RH premise is used.
"""
from __future__ import annotations
import hashlib,json,math,time
from fractions import Fraction
from pathlib import Path
import mpmath as mpm
import sympy as sp
OUT=Path(__file__).resolve().parent
mp=mpm.mp;iv=mpm.iv;mp.dps=90;iv.dps=70
N=60;Q=40;PANELS=80;T=40;BITS=100;MBITS=80
SCALE=1<<BITS;MSCALE=1<<MBITS;EPS=iv.mpf(2)**-90
beta=iv.mpf(4)/5;length=iv.log(3);b=length/2;log2=iv.log(2);c2=log2/iv.sqrt(2)
START=time.monotonic()
def end(x,hi=False):return mp.mpf(x._mpi_[int(hi)])
def itext(x):return [mp.nstr(end(x),25),mp.nstr(end(x,True),25)]
def quant(x):
 n=int(mp.nint((end(x)+end(x,True))*SCALE/2))
 assert abs(x-iv.mpf(n)/SCALE)<EPS,('quant',itext(x))
 return n
def lp(n,x):
 p0=iv.mpf(1);p1=x
 if n==0:return p0,iv.mpf(0)
 for k in range(1,n):p0,p1=p1,((2*k+1)*x*p1-k*p0)/(k+1)
 return p1,p0
def gauss(n):
 approx,_=mp.gauss_quadrature(n,'legendre');den=1<<200;out=[];last=None
 for v in approx:
  cen=int(mp.nint(v*den));lo=iv.mpf(cen-2)/den;hi=iv.mpf(cen+2)/den
  
  def exact_p(y):
   p0=Fraction(1);p1=y
   for k in range(1,n):p0,p1=p1,((2*k+1)*y*p1-k*p0)/(k+1)
   return p1
  assert exact_p(Fraction(cen-2,den))*exact_p(Fraction(cen+2,den))<0
  x=iv.mpf([end(lo),end(hi,True)])
  if last is not None:assert last<x
  assert x>-1 and x<1
  pn,pm=lp(n,x);der=n*(pm-x*pn)/(1-x*x);assert abs(der)>0
  w=2/((1-x*x)*der*der);assert w>0 and w<2
  out.append((x,w));last=x
 return out
P=14;BERN=[Fraction(sp.bernoulli(2*k)) for k in range(1,P+1)]
REM=iv.mpf(2*abs(BERN[-1].numerator))/(BERN[-1].denominator*(2*P)*64**(2*P))
def psi(z):
 w=z+64;assert w.real>=64 and abs(w.imag)<=32
 v=iv.log(w)-1/(2*w)
 for k,B in enumerate(BERN[:-1],1):v-=iv.mpf(B.numerator)/B.denominator/(2*k*w**(2*k))
 for k in range(64):v-=1/(z+k)
 rr=iv.mpf([-end(REM,True),end(REM,True)])
 return v+iv.mpc(rr,rr)
def symbol(t):return psi(iv.mpc(iv.mpf(1)/4,t/2)).real-iv.log(iv.pi)-2*c2*iv.cos(log2*t)
def df(n):return math.prod(range(1,2*n+2,2))
def seed(n,x,modified=False):
 term=iv.mpf(1);total=term
 for k in range(120):
  term*=x*x/(2*(k+1)*(2*n+2*k+3))
  if not modified:term=-term
  total+=term
 nxt=abs(term*x*x/(2*121*(2*n+243)))
 rat=x*x/(2*122*(2*n+245));assert rat<iv.mpf(1)/2
 rr=nxt/(1-rat);total+=iv.mpf([-end(rr,True),end(rr,True)])
 return x**n/df(n)*total
def jvals(x):
 assert x>0 and x<22
 vals=[None]*(N+3);vals[N+1]=seed(N+1,x);vals[N+2]=seed(N+2,x)
 for k in range(N+1,0,-1):vals[k-1]=(2*k+1)*vals[k]/x-vals[k+1]
 return vals[:N+1]
def bareiss(M):
 A=[r[:] for r in M];n=len(A);prev=1;ds=[]
 for k in range(n):
  p=A[k][k];assert p>0,('pivot',k,p);ds.append(p)
  if k<n-1:
   for i in range(k+1,n):
    for j in range(i,n):
     v,r=divmod(p*A[i][j]-A[i][k]*A[k][j],prev);assert r==0
     A[i][j]=A[j][i]=v
   for i in range(k+1,n):A[i][k]=A[k][i]=0
  prev=p
 return ds
def progress(done,total):
 e=time.monotonic()-START;eta=e*(total-done)/max(done,1);n=30*done//total
 print('['+'#'*n+'-'*(30-n)+f'] {done}/{total} elapsed={e:.1f}s ETA={eta:.1f}s',flush=True)
def main():
 roots=gauss(Q);print('PASS certified algebraic Gauss nodes/weights',flush=True)
 lo=psi(iv.mpc(iv.mpf(1)/4,20)).real-iv.log(iv.pi)-2*c2
 assert lo>beta;assert c2<iv.mpf(1)/2
 a0=psi(iv.mpc(iv.mpf(1)/4,0)).real-iv.log(iv.pi)
 aT=lo+2*c2
 assert a0>-iv.mpf(27)/5 and aT<2 # proves |symbol-beta|<8 on [0,40]
 print('PASS tail symbol lower',itext(lo),flush=True)
 fac=[iv.sqrt(length*(2*n+1)) for n in range(N+1)]
 inds=[list(range(0,N+1,2)),list(range(1,N+1,2))]
 acc=[[[0]*len(ii) for _ in ii] for ii in inds]
 for panel in range(PANELS):
  for X,W in roots:
   t=iv.mpf(panel)/2+iv.mpf(1)/4+X/4
   aw=W/4*(symbol(t)-beta)/iv.pi;assert abs(aw)<4;ai=quant(aw)
   js=jvals(b*t);vs=[quant(fac[n]*js[n]*((-1)**(n//2))) for n in range(N+1)]
   for k,ii in enumerate(inds):
    vals=[vs[n] for n in ii];A=acc[k]
    for i in range(len(ii)):
     av=ai*vals[i]
     for j in range(i,len(ii)):A[i][j]+=av*vals[j]
  if panel%8==7:progress((panel+1)*Q,PANELS*Q)
 pole=[quant(iv.sqrt(2)*fac[n]*seed(n,b/2,True)) for n in range(N+1)]
 mats=[];details=[]
 for k,ii in enumerate(inds):
  sz=len(ii);G=[[0]*sz for _ in ii]
  for i in range(sz):
   for j in range(i,sz):
    x=acc[k][i][j]+(1 if k==0 else -1)*pole[ii[i]]*pole[ii[j]]*SCALE
    num=5*x+(4*SCALE**3 if i==j else 0);den=5*SCALE**3
    g=(num*MSCALE+den//2)//den;G[i][j]=G[j][i]=g
  shifted=[r[:] for r in G]
  for i in range(sz):shifted[i][i]-=1<<(MBITS-29)
  ds=bareiss(shifted);rs=[Fraction(d,(ds[i-1] if i else 1)*MSCALE) for i,d in enumerate(ds)];r=min(rs)
  mats.append(G);details.append({'parity':['even','odd'][k],'dimension':sz,'exact_leading_minors_positive':True,'min_LDL_pivot':mp.nstr(mp.mpf(r.numerator)/r.denominator,25),'determinant_digits':len(str(ds[-1])),'determinant_sha256':hashlib.sha256(str(ds[-1]).encode()).hexdigest()})
  print('PASS exact rational Sylvester',details[-1],flush=True)
 n=N+1;x=T*b;rat=x*x/((2*n+1)*(2*n+3))
 tail=length*(2*n+1)*x**(2*n)/df(n)**2/(1-rat);assert tail<iv.mpf(2)**-132
 eb=iv.mpf(8)*T/iv.pi*(2*iv.sqrt(length*tail)+tail)
 pt=2*length*iv.exp(b)*(2*n+1)*(b/2)**(2*n)/df(n)**2/(1-(b/2)**2/((2*n+1)*(2*n+3)));assert pt<iv.mpf(2)**-700
 ep=8*iv.sqrt(pt)+2*pt;eg=iv.mpf(8)*T*512/(iv.pi*2**(2*Q))
 eq=iv.mpf(1000)*(PANELS*Q+1)/2**90;er=iv.mpf(N+1)/2**80;ee=eb+ep+eg+eq+er;assert ee<iv.mpf(2)**-40
 # Negative source control: double exactly the weight at n=2.
 KK=1000;ss=iv.mpf(0)
 for k in range(KK):
  lam=iv.mpf(2*k)+iv.mpf(1)/2
  ss+=(1-iv.exp(-lam*length))/(lam*lam)
 lam=iv.mpf(2*KK)+iv.mpf(1)/2
 rr=1/(lam*lam)+1/(2*lam)
 ss+=iv.mpf([0,end(rr,True)])
 sh=(iv.exp(length/4)-iv.exp(-length/4))/2
 cc=-a0
 control=2*ss/length-cc-4*c2*(length-log2)/length+32*sh*sh/length
 assert control<-iv.mpf(23)/100
 print('PASS negative doubled-prime control',itext(control),flush=True)
 errs={n:itext(v) for n,v in [('Legendre_tail',tail),('band_tail_error',eb),('pole_error',ep),('quadrature_error',eg),('scalar_quantization_error',eq),('matrix_rounding_error',er),('total_error',ee)]}
 print('PASS full operator remainder <2^-40',errs,flush=True)
 payload={'matrix_dyadic_bits':MBITS,'LDL_shift':'2^-29','even':mats[0],'odd':mats[1]};txt=json.dumps(payload,sort_keys=True,separators=(',',':'))+'\n';(OUT/'rational_certificate.json').write_text(txt)
 summary={'parameters':{'L':'log(3)','T':T,'beta':'4/5','degree':N,'Gauss':Q,'panels':PANELS,'iv_dps':iv.dps},'engine':'elementary interval arithmetic + explicit analytic remainders + exact integer Bareiss','Arb':False,'Lean':False,'RH_assumed':False,'certificate_sha256':hashlib.sha256(txt.encode()).hexdigest(),'tail_symbol_lower':itext(lo),'parity_blocks':details,'bounds':errs,'negative_control':itext(control),'lower_bound':'2^-30','elapsed_seconds':time.monotonic()-START}
 (OUT/'result.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2),flush=True)
if __name__=='__main__':main()
