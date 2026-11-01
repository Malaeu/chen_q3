"""DIAGNOSTIC_NEVER_A_PROOF: independent physical NOESCAPE (4.12) X.

Even orthonormal basis e0=1/sqrtL, ej=sqrt(2/L)cos(2*pi*j*(x/L+1/2)).
No T, F, zeta samples, eigenvalues, or radical closure are used.
compute_raw(m,dps,order) gives physical source rows and W projection.
compute_X(..., K=even_matrix) adds the finite projection correction K*cW.
"""
from pathlib import Path
import json,sys,time
import mpmath as mp

def mang(n):
 for p in range(2,n+1):
  if n%p==0:
   k=n
   while k%p==0:k//=p
   return mp.log(p) if k==1 else mp.mpf(0)
 return mp.mpf(0)

def compute_raw(m,dps=100,order=128):
 mp.mp.dps=dps
 start=time.monotonic();L=mp.log(m);b=L/2;rt=mp.sqrt(L);rt2=mp.sqrt(2)
 gn,gw=mp.gauss_quadrature(order,'legendre')
 def rule(a,z,panels=1):
  for k in range(panels):
   lo=a+(z-a)*k/panels;hi=a+(z-a)*(k+1)/panels
   for t,w in zip(gn,gw):yield (lo+hi+(hi-lo)*t)/2,w*(hi-lo)/2
 cutoff=(dps+60)*mp.log(10)
 Y=mp.log(cutoff/mp.pi)/2
 def h(x):
  u=mp.exp(2*x);a=mp.pi*u;v=mp.mpf(0);n=1
  while a*n*n<cutoff:
   z=n*n*u
   v+=(16*mp.pi**2*z*z-24*mp.pi*z)*mp.exp(-mp.pi*z);n+=1
  return mp.exp(x/2)*v
 def W(x):return h(L-x)+h(L+x)
 def basis(x):
  c=mp.cos(2*mp.pi*(x+b)/L);vals=[1/rt];prev=mp.mpf(1);cur=c
  for n in range(1,m+1):
   vals.append(rt2*cur/rt);prev,cur=cur,2*c*cur-prev
  return vals
 def vecint(a,z,fun,panels=1):
  sums=[mp.mpf(0)]*(m+1)
  for x,w in rule(a,z,panels):
   amp,arg=fun(x);v=basis(arg);q=w*amp
   for n in range(m+1):sums[n]+=q*v[n]
  return sums
 def scalint(a,z,fun,panels=1):return mp.fsum(w*fun(x) for x,w in rule(a,z,panels))
 def qout(s):
  # Original disjoint-support correlation, with both even tails included.
  lo=max(-b,b-s)
  if lo>=b:return [mp.mpf(0)]*(m+1)
  return vecint(lo,b,lambda y:(2*h(y+s),y),2)
 def qw(s):
  right=b-s
  if right<=-b:return [mp.mpf(0)]*(m+1)
  return vecint(-b,right,lambda x:(2*W(x),x+s),2)
 def j(s):return mp.exp(-s/2)/(-mp.expm1(-2*s))
 cW=vecint(-b,b,lambda x:(W(x),x),4)
 pvec=vecint(-b,b,lambda x:(rt2*mp.cosh(x/2),x),2)
 wp=scalint(-b,b,lambda x:W(x)*rt2*mp.cosh(x/2),4)
 hp=2*scalint(b,Y,lambda x:h(x)*rt2*mp.cosh(x/2),4)
 archW=[mp.mpf(0)]*(m+1);archout=[mp.mpf(0)]*(m+1)
 # Four fixed panels on 0..L; exact arch W tail retained.
 for s,w in rule(mp.mpf(0),L,4):
  qq=qw(s);qo=qout(s);jj=j(s)*w
  for n in range(m+1):
   archW[n]+=jj*(2*cW[n]-qq[n]);archout[n]-=jj*qo[n]
 S=Y+b
 if S>L:
  for s,w in rule(L,S,2):
   qo=qout(s);jj=w*j(s)
   for n in range(m+1):archout[n]-=jj*qo[n]
 J=mp.log((1+mp.exp(-L/2))/(1-mp.exp(-L/2)))/2+mp.atan(mp.exp(-L/2))
 for n in range(m+1):archW[n]+=2*cW[n]*J
 maxprime=int(mp.ceil(mp.exp(Y+b)))+3
 primeW=[mp.mpf(0)]*(m+1);primeout=[mp.mpf(0)]*(m+1)
 for k in range(2,maxprime+1):
  vm=mang(k)
  if not vm:continue
  a=mp.log(k);q=vm/mp.sqrt(k);qo=qout(a)
  for n in range(m+1):primeout[n]-=q*qo[n]
  if k<m:
   qq=qw(a)
   for n in range(m+1):primeW[n]-=q*qq[n]
 cs=mp.euler+mp.log(8*mp.pi)+mp.pi/2
 hout=mp.matrix([archout[n]+primeout[n]+hp*pvec[n] for n in range(m+1)])
 kw=mp.matrix([-cs*cW[n]+archW[n]+primeW[n]+wp*pvec[n] for n in range(m+1)])
 # Absolute omitted-tail indicators (not a quadrature enclosure).
 tailarch=2*mp.sqrt(L)*1000*mp.exp(mp.mpf('4.5')*Y-mp.pi*mp.exp(2*Y))*(mp.log((1+mp.exp(-S/2))/(1-mp.exp(-S/2)))/2+mp.atan(mp.exp(-S/2)))
 nn=mp.mpf(maxprime+1);aa=mp.pi/m;q=((nn+1)/nn)**5*mp.exp(-aa*(2*nn+1))
 tailprime=2*mp.sqrt(L)*1000*mp.mpf(m)**(-mp.mpf(9)/4)*mp.log(nn)*nn**4*mp.exp(-aa*nn**2)/(1-q)
 return {'m':m,'dps':dps,'order':order,'L':L,'h_out_form':hout,'W_form':kw,'W_coeff':mp.matrix(cW),'raw_difference':hout-kw,'components':{'hout_arch':archout,'hout_prime':primeout,'hout_pole':[hp*v for v in pvec],'W_arch':archW,'W_prime':primeW,'W_pole':[wp*v for v in pvec],'W_diagonal':[-cs*v for v in cW]},'metadata':{'status':'DIAGNOSTIC_NEVER_A_PROOF','formula':'X=k(h_out,e)-k(W,e)+K_even*cW','basis':'e0=1/sqrtL; ej=sqrt(2/L)*cos(2pi*j*(x/L+1/2))','prime_cutoff':maxprime,'hout_upper_x':Y,'hout_arch_upper_s':S,'images':[-1,1],'theta_exponent_cutoff':cutoff,'arch_omitted_envelope':tailarch,'prime_omitted_envelope':tailprime,'hout_pole_omitted_norm_envelope':mp.sqrt(2)*1000*mp.pi**(-mp.mpf('2.5'))*mp.gammainc(mp.mpf('2.5'),mp.pi*mp.exp(2*Y),mp.inf)*mp.sqrt(L+2*mp.sinh(L/2)),'first_omitted_image_pointwise_envelope':2*1000*mp.exp(mp.mpf('4.5')*3*b-mp.pi*mp.exp(6*b)),'quadrature_enclosure':False,'seconds':time.monotonic()-start}}

def compute_X(m,dps=100,order=128,K=None):
 r=compute_raw(m,dps,order)
 if K is None:
  root=next(p for p in Path(__file__).resolve().parents if (p/'docs/routeB_bus/fokas_k_sign_2026-09-25/full_center_probe.py').exists())
  sys.path.insert(0,str(root/'docs/routeB_bus/fokas_k_sign_2026-09-25'))
  import full_center_probe as fc
  A=fc.matrix_K(m);E=mp.zeros(2*m+1,m+1);E[m,0]=1
  for n in range(1,m+1):E[m-n,n]=E[m+n,n]=1/mp.sqrt(2)
  K=E.T*A*E
 r['projection_correction']=K*r['W_coeff'];r['X']=r['raw_difference']+r['projection_correction']
 return r

def serial(r):
 if isinstance(r,mp.matrix):return [mp.nstr(x,mp.mp.dps) for x in r]
 if isinstance(r,mp.mpf):return mp.nstr(r,mp.mp.dps)
 if isinstance(r,dict):return {k:serial(v) for k,v in r.items()}
 if isinstance(r,list):return [serial(v) for v in r]
 return r
if __name__=='__main__':
 m=int(sys.argv[1]);dps=int(sys.argv[2]);order=int(sys.argv[3]);start=time.monotonic()
 r=compute_X(m,dps,order);r['total_seconds']=time.monotonic()-start
 out=Path(__file__).parent/f'exterior_m{m}_dps{dps}_gl{order}.json';out.write_text(json.dumps(serial(r),indent=2)+'\n');print(str(out),flush=True)
