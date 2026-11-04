#!/usr/bin/env python3
"""Literal physical even CCM moments in python-flint/Arb; analytic formulas only.
No zero tables, matrix inputs, eigensystem or numerical quadrature are read.
160-bit fixed precision. Coherent source is H + P - B throughout.
"""
from pathlib import Path
import argparse,json,time,math,hashlib
import flint
from flint import arb,acb,ctx
OUT=Path(__file__).resolve().parent
BITS=160

def ball(x):return x.str(48,radius=True)
def rational(q):return arb(q[0])/q[1]
def floor_cert(x):
 n=math.floor(float(x.mid()))
 assert x<n+1, 'unresolved integer floor upper bound'
 return n

def ceil_lower_cert(x):
 n=math.ceil(float(x.mid()))
 if x>n-1:return n
 return n-1 if x>n-2 else None

def envelope(m,L,om2,kap):
 pi=arb.pi();T=kap*2*pi*m/L
 C=8*(L/4).cosh()**2/L;b=1/(4*T*T);xs=[v/(T*T)for v in om2]
 ell=(T/(2*pi)).log();assert ell>0
 SI=arb(0);SJ=arb(0);powers=[arb(1)]*(m+1);K=256
 for k in range(K):
  mass=powers[0]+2*sum(powers[1:],arb(0))
  SI+=(k+1)*mass*(ell/(2*k+1)+arb(1)/(2*k+1)**2+b*(ell/(2*k+3)+arb(1)/(2*k+3)**2))
  SJ+=(k+1)*mass*(arb(1)/(2*k+2)+b/(2*k+4))
  powers=[p*x for p,x in zip(powers,xs)]
 r=1/kap**2;G=r**K*((K+1)/(1-r)+r/(1-r)**2)
 # Every summand is nonnegative; [0,1] times a certified bound encloses the omitted series.
 unit=arb('0.5 +/- 0.5')
 SI+=unit*(2*m+1)*(ell+1)*(1+b)*G
 SJ+=unit*(2*m+1)*(1+b)*G
 I=C/(2*pi*T)*SI;J=C/(T*T)*SJ
 wT=C/(T*T)*(1+b)*(1/(1-xs[0])**2+2*sum((1/(1-x)**2 for x in xs[1:]),arb(0)))
 eta=arb(11)/20;E=I+2*eta*T.log()*wT+eta*J
 M=T/(2*pi)*((T/(2*pi)).log()-1)+arb(7)/8
 Nreal=M+eta*T.log()
 Rratio=arb(137)/1000+arb(443)/1000*T.log().log()/T.log()+arb(1588)/1000/T.log()
 assert T>2 and T.log()>1 and Rratio<eta
 # derivative wrt log(t) is [.443*(1-log log t)-1.588]/log(t)^2 < 0 for t>=T.
 return dict(T=T,I=I,J=J,wT=wT,E=E,Nreal=Nreal,Rratio=Rratio,series_remainder_mass=G)

def source(m,L,progress=True):
 pi=arb.pi();omega=[2*pi*j/L for j in range(m+1)];om2=[w*w for w in omega]
 d=[arb(1)]+[arb(2).sqrt()]*m;q=[];f=[];sd=[]
 # Arb special functions enclose the exact analytic functions, independent of mpmath EM code.
 for j,w in enumerate(omega):
  z=acb(arb(1)/4,w/2);ps=z.digamma();pt=z.polygamma(1)
  q.append(ps.real-pi.log())
  if j:f.append(ps.imag/(2*w));sd.append(ps.imag/(4*w)+pt.real/8)
  else:f.append(pt.real/4);sd.append(pt.real/4)
 sieve=[True]*(m+1);sieve[0]=sieve[1]=False
 for p in range(2,math.isqrt(m)+1):
  if sieve[p]:
   for n in range(p*p,m+1,p):sieve[n]=False
 atoms={}
 for p in range(2,m+1):
  if sieve[p]:
   n=p;lp=arb(p).log()
   while n<m:atoms[n]=lp;n*=p
 S=[arb(0)for _ in omega];V=[arb(0)for _ in omega]
 # Direct Arb sin/cos avoids dependency wrapping from long interval recurrences.
 for n,lp in sorted(atoms.items()):
  u=arb(n).log();weight=lp/arb(n).sqrt();phase=2*pi*u/L
  for j in range(m+1):
   sj,cj=(j*phase).sin_cos()
   S[j]+=weight*sj;V[j]+=weight*(1-u/L)*cj
 pole=[arb(2).sqrt()*dj*(L/4).sinh()/(L.sqrt()*(ww+arb(1)/4))for dj,ww in zip(d,om2)]
 R=6;aa=[arb(2*r)+arb(1)/2 for r in range(R)];ew=[a*a*(-a*L).exp()for a in aa];ivv=[[1/(a*a+ww)for ww in om2]for a in aa]
 aR=arb(2*R)+arb(1)/2;etail=(-aR*L).exp()/(aR**2*(1-(-2*L).exp()));unit=arb('0.5 +/- 0.5')
 trace=arb(0);frob=arb(0);dec={x:arb(0)for x in ['H2','P2','B2','HP','HB','PB']};start=time.monotonic()
 for j in range(m+1):
  for k in range(j+1):
   if j==k:sjk=sd[j];bjk=2*V[j]if j==0 else 2*V[j]-2*S[j]/(L*omega[j])
   else:
    sjk=(om2[j]*f[j]-om2[k]*f[k])/(om2[j]-om2[k])
    bjk=-2*d[j]*d[k]/L*(omega[j]*S[j]-omega[k]*S[k])/(om2[j]-om2[k])
   ejk=sum((e*v[j]*v[k]for e,v in zip(ew,ivv)),arb(0))+unit*etail
   hjk=2*d[j]*d[k]/L*(sjk-ejk)+(q[j]if j==k else 0);pp=pole[j]*pole[k];a=hjk+pp-bjk
   if j==k:trace+=a
   weight=1 if j==k else 2
   frob+=weight*a*a
   for name,x in [('H2',hjk*hjk),('P2',pp*pp),('B2',bjk*bjk),('HP',2*hjk*pp),('HB',-2*hjk*bjk),('PB',-2*pp*bjk)]:dec[name]+=weight*x
  if progress and(j%max(50,m//10)==0 or j==m):print(f'm={m} triangle {j+1}/{m+1}, seconds={time.monotonic()-start:.1f}',flush=True)
 return trace,frob,dec,om2,etail

def run(m):
 ctx.prec=BITS;start=time.monotonic();L=arb(m).log();kap=1+(1+L.log())/(4*L)
 tr,F,dec,om2,etail=source(m,L);e=envelope(m,L,om2,kap)
 ze=26*(-arb.pi()).exp()/(arb.pi()*(1-(-3*arb.pi()).exp()));assert ze<arb(1)/2
 sig=L+arb(1)/5
 if m==300:aa=(8959,10);qq=(5481,1);ee=(25,2);Nup=185
 else:
  aa=(floor_cert(10*tr),10);qq=(floor_cert(F)+1,1);ee=(floor_cert(10*e['E'])+1,10);Nup=floor_cert(e['Nreal'])
 a=rational(aa);q=rational(qq);E=rational(ee)
 Flo=4*a/sig-4*E/sig-(q.sqrt()/sig+E/sig)**2
 simple=Flo-2*Nup;distinct=(Flo-Nup)/2
 gates={'trace_ge_895_9':bool(tr>a),'frob_sq_le_5481':bool(F<q),'tail_le_12_5':bool(e['E']<E),'N_le_185':bool(e['Nreal']<Nup+1),'R_le_0_55_log':bool(e['Rratio']<arb(11)/20),'zero_free_gamma5':bool(ze<arb(1)/2),'simple_count_ge_14':bool(simple>13),'distinct_count_ge_100':bool(distinct>99)}if m==300 else {'trace_rational_gate':bool(tr>a),'frob_rational_gate':bool(F<q),'tail_rational_gate':bool(e['E']<E),'N_integer_upper_gate':bool(e['Nreal']<Nup+1)}
 lower_s=max(0,ceil_lower_cert(simple));lower_d=max(0,ceil_lower_cert(distinct))
 result=dict(m=m,backend='python-flint/Arb',flint_version=flint.__version__,precision_bits=BITS,diagnostic='PENDING_PAPER_AUDIT_NO_RH_EXPORT',uses_zero_list=False,uses_source_array=False,source_dimension=m+1,source_formula='H+P-B; exact physical even basis',T=ball(e['T']),trace=ball(tr),frob_sq=ball(F),tail_E=ball(e['E']),I=ball(e['I']),J=ball(e['J']),wT=ball(e['wT']),N_upper_real=ball(e['Nreal']),Rosser_R_over_log=ball(e['Rratio']),zero_free_gamma5_error=ball(ze),exponential_source_tail_envelope=ball(etail),rational_inputs=dict(a_lower=aa,q_upper=qq,E_upper=ee,N_upper=Nup,c=[1,4],b=[1,5],tail_R_coefficient=[11,20]),safe_score_lower=ball(Flo),simple_count_real_lower=ball(simple),distinct_count_real_lower=ball(distinct),conditional_simple_lower=lower_s,conditional_distinct_lower=lower_d,conditional_simple_fraction=lower_s/Nup,conditional_distinct_fraction=lower_d/Nup,gates=gates,decomposition={k:ball(v)for k,v in dec.items()},seconds=time.monotonic()-start)
 if not all(gates.values()):raise RuntimeError('FAILED GATE '+str(gates))
 (OUT/f'ARB_m{m}.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
 return result
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--m',type=int,default=300);args=p.parse_args();run(args.m)
