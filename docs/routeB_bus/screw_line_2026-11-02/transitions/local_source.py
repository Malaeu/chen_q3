"""Copied source matrix formula; fixed N=m, variable physical length L.
The birth integer n=m is excluded on both sides to continue the left branch.
Only geometric-tail factors now use exp(-alpha L),exp(-2L), and N is fixed.
DIAGNOSTIC_NEVER_A_PROOF. No original source script is modified.
"""
import math
from flint import arb,acb,arb_mat,ctx
def mid(x):return x.mid()
def text(x,digits=65):return x.mid().str(digits,radius=False)

def source_matrix_local(m,world,b,L):
 pi=arb.pi();sq2=arb(2).sqrt();ds=[arb(1)]+[sq2]*m;alpha=arb(1)/2 if world=='zeta' else arb(3)/2
 psia=acb(alpha/2).digamma().real;c=(-arb.const_euler()-(8*pi).log()-pi/2) if world=='zeta' else (-arb.const_euler()-(8*pi/5).log()+pi/2)
 # m^(-2r) tail terms are truncated far below the working-rounding scale.
 terms=int(math.ceil((ctx.prec+64)*math.log(2)/(2*float(L))))+3
 powers=[];p=(-alpha*L).exp();ratio=(-2*L).exp()
 for r in range(terms):powers.append(p);p*=ratio
 sm=[];diag=[]
 for n in range(m+1):
  w=2*pi*n/L;z=acb(alpha/2,w/2);psi=z.digamma();tri=z.polygamma(1).real
  s=arb(0);v=arb(0)
  for r,p in enumerate(powers):
   a=2*r+alpha;den=a*a+w*w;s+=p*w/den;v+=p*(a*a-w*w)/(den*den)
  sine=mid(psi.imag/2-s);sm.append(sine)
  val=psi.real-psia+tri/(2*L)-2*v/L
  if n:val+=sine/(pi*n)
  diag.append(mid(c+val))
 ps=[arb(0)]*(m+1);pd=[arb(0)]*(m+1)
 for k in range(2,m):
  if b[k]==0:continue
  y=arb(k).log()/L;weight=b[k]/arb(k).sqrt();angle=2*pi*y;co=angle.cos();si=angle.sin();cn=arb(1);sn=arb(0)
  for n in range(m+1):
   ps[n]+=weight*sn;pd[n]+=weight*(2*(1-y)*cn-(sn/(pi*n) if n else 0));cn,sn=mid(cn*co-sn*si),mid(sn*co+cn*si)
 beta=[mid(sm[i]+ps[i]) for i in range(m+1)];A=arb_mat(m+1,m+1)
 for i in range(m+1):
  A[i,i]=mid(diag[i]-pd[i])
  for j in range(i+1,m+1):A[i,j]=A[j,i]=mid(ds[i]*ds[j]/pi*(i*beta[i]-j*beta[j])/(i*i-j*j))
 if world=='zeta':
  pole=arb_mat([[mid(4*sq2*ds[n]*L*L.sqrt()*(L/4).sinh()/(L*L+16*pi*pi*n*n))] for n in range(m+1)])
  A=(A+pole*pole.transpose()).mid()
 tailbase=powers[-1]*ratio/((2*terms+alpha)**2*(1-ratio))
 entry_tail_bound=4*(m+1)/L*tailbase
 return A,dict(analytic_arch_tail_terms=terms,tail_decay_power=text(ratio**terms),arch_entry_tail_bound_upper=entry_tail_bound.upper().str(65,radius=False),arch_tail_bound_definition='4*(m+1)/L * exp(-(alpha+2R)*L)/((2R+alpha)^2*(1-exp(-2L))); finite geometric tail only, excludes rounding/zero-table error',kernel_alpha=text(alpha),source_constant=text(c))
