"""SCREW_LINE_v1 formal inverse-form proxies, DIAGNOSTIC_NEVER_A_PROOF.

Native kappa1.1. No Weyl-circle identification is assumed. The source
operator is the unchanged literal even CCM/DH form, evaluated using analytic
digamma/trigamma arch moments (validated against the pinned source builders).
Finite sums/rounding/zero tables here are numerical inputs, not interval data.
"""
from pathlib import Path
import argparse,csv,json,hashlib,time,math,os
import mpmath as mp
from flint import arb,acb,arb_mat,ctx

def mid(x):return x.mid()
def text(x,digits=65):return x.mid().str(digits,radius=False)
def sign(x):return 1 if x>0 else (-1 if x<0 else 0)

def coefficients(M,world):
 if world=='zeta':
  b=[arb(0)]*(M+1)
  for n in range(2,M+1):
   for p in range(2,n+1):
    if n%p==0:
     k=n
     while k%p==0:k//=p
     b[n]=arb(p).log() if k==1 else arb(0);break
  return b
 tau=(arb(10)-2*arb(5).sqrt()).sqrt()-2;tau/=arb(5).sqrt()-1
 a=[arb(0),arb(1),tau,-tau,arb(-1)];b=[arb(0)]*(M+1)
 for n in range(2,M+1):b[n]=mid(a[n%5]*arb(n).log()-sum((b[d]*a[(n//d)%5] for d in range(2,n) if n%d==0),arb(0)))
 return b

def source_matrix(m,world,b):
 L=arb(m).log();pi=arb.pi();sq2=arb(2).sqrt();ds=[arb(1)]+[sq2]*m;alpha=arb(1)/2 if world=='zeta' else arb(3)/2
 psia=acb(alpha/2).digamma().real;c=(-arb.const_euler()-(8*pi).log()-pi/2) if world=='zeta' else (-arb.const_euler()-(8*pi/5).log()+pi/2)
 # m^(-2r) tail terms are truncated far below the working-rounding scale.
 terms=int(math.ceil((ctx.prec+64)*math.log(2)/(2*math.log(m))))+3
 powers=[];p=arb(m)**(-alpha);ratio=arb(m)**(-2)
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
 tailbase=(powers[-1]*ratio)/((2*terms+alpha)**2*(1-ratio))
 entry_tail_bound=4*(m+1)/L*tailbase
 return A,dict(analytic_arch_tail_terms=terms,tail_decay_power=text(ratio**terms),arch_entry_tail_bound_upper=entry_tail_bound.upper().str(65,radius=False),arch_tail_bound_definition='4*(m+1)/L * m^(-alpha-2R)/((2R+alpha)^2*(1-m^-2)); finite geometric tail only, excludes rounding/zero-table error',kernel_alpha=text(alpha),source_constant=text(c))

def eval_row(z,m):
 L=arb(m).log();pi=arb.pi();sqrtL=L.sqrt();row=[]
 for n in range(m+1):
  ds=arb(1) if n==0 else arb(2).sqrt();w=2*pi*n/L
  # Census nodes do not coincide with removable modal poles.
  v=2*ds*z*(z*L/2).sin()/(sqrtL*(z*z-w*w));row.append(v)
 return row

def sampling(m,world,T,zeta,dh):
 rows=[];labels=[]
 if world=='zeta':
  for a in zeta:
   if arb(a)<T:
    rows.append([mid(v.real) for v in eval_row(acb(arb(a)),m)]);labels.append(dict(gamma=a,kind='line'))
 else:
  for a in dh['critical_line_zeros']:
   if arb(a['gamma'])<T:
    rows.append([mid(v.real) for v in eval_row(acb(arb(a['gamma'])),m)]);labels.append(dict(gamma=a['gamma'],kind='line'))
  for a in dh['off_line_pairs']:
   if arb(a['gamma'])<T:
    z=acb(arb(a['gamma']),arb(a['sigma_right'])-arb(1)/2);vv=eval_row(z,m)
    rows.append([mid(arb(2).sqrt()*v.real) for v in vv]);labels.append(dict(gamma=a['gamma'],kind='real'))
    rows.append([mid(arb(2).sqrt()*v.imag) for v in vv]);labels.append(dict(gamma=a['gamma'],kind='imag'))
 return arb_mat(rows),labels

def evaluation_columns(m):
 L=arb(m).log();pi=arb.pi();ds=[arb(1)]+[arb(2).sqrt()]*m;columns=[[mid(d/L.sqrt()) for d in ds]];names=[('endpoint','0')]
 for gauge in ['physical','fourier']:
  for etastr in ['0.5','1','2']:
   eta=arb(etastr);col=[]
   for n in range(m+1):
    w=2*pi*n/L
    v=ds[n]*((-1)**n)*(w*eta).cosh()/L.sqrt() if gauge=='physical' else 2*ds[n]*eta*(eta*L/2).sinh()/(L.sqrt()*(eta*eta+w*w))
    col.append(mid(v))
   columns.append(col);names.append((gauge,etastr))
 return arb_mat([[c[i] for c in columns] for i in range(m+1)]),names

def ldl_inertia(B):
 n=B.nrows();ll=[[arb(0)]*n for _ in range(n)];dd=[];mn=None;neg=0
 for j in range(n):
  pivot=mid(B[j,j]-sum((ll[j][k]*ll[j][k]*dd[k] for k in range(j)),arb(0)))
  if pivot==0:raise ArithmeticError('Zero LDL pivot; no inertia classification')
  neg+=pivot<0;mn=abs(pivot) if mn is None or abs(pivot)<mn else mn;dd.append(pivot)
  for i in range(j+1,n):ll[i][j]=mid((B[i,j]-sum((ll[i][k]*ll[j][k]*dd[k] for k in range(j)),arb(0)))/pivot)
 return dict(negative=neg,positive=n-neg,zero=0,minimum_absolute_pivot=text(mn),method='unpivoted symmetric LDL midpoint arithmetic; no tolerance cutoff; numerical inertia, not interval-certified')

def case(m,world,b,zeta,dh,inertia=True):
 start=time.monotonic();L=arb(m).log();T=arb('1.1')*2*arb.pi()*m/L;A,meta=source_matrix(m,world,b);E,labels=sampling(m,world,T,zeta,dh);q=E.nrows();B=(E*A*E.transpose()).mid();C,names=evaluation_columns(m);V=(E*C).mid();X=B.solve(V,algorithm='approx');K=(V.transpose()*X).mid()
 residual=B*X-V;bnorm=max(sum((abs(B[i,j]) for j in range(q)),arb(0)) for i in range(q));solve_res=[]
 for j in range(V.ncols()):
  rn=max(abs(residual[i,j]) for i in range(q));xn=max(abs(X[i,j]) for i in range(q));vn=max(abs(V[i,j]) for i in range(q));solve_res.append(text(rn/(bnorm*xn+vn)))
 bsym=max(abs(B[i,j]-B[j,i]) for i in range(q) for j in range(q))/max(arb(1),bnorm)
 ksym=max(abs(K[i,j]-K[j,i])/max(arb(1),abs(K[i,j]),abs(K[j,i])) for i in range(K.nrows()) for j in range(K.ncols()))
 rows=[]
 for j,(gauge,etas) in enumerate(names):
  value=K[j,j];sgn=sign(value);eta=arb(etas)
  out=dict(world=world,m=m,q=q,dim_J=m+1-q,T=text(T),gauge=gauge,eta=etas,K=text(value),K_sign=sgn,endpoint_cross=text(K[0,j]),K_endpoint=text(K[0,0]),solve_backward_relative_residual=solve_res[j],kernel_status='formal_inverse_form_proxy_no_Weyl_identification',arithmetic_bits=ctx.prec)
  if eta!=0 and value!=0:
   r=1/(eta*value);r2=r*r;out.update(r_proxy=text(r),r_proxy_squared=text(r2),r_proxy_squared_sign=sign(r2))
  else:out.update(r_proxy='',r_proxy_squared='',r_proxy_squared_sign='')
  rows.append(out)
 inertia_record=ldl_inertia(B) if inertia else None
 result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world=world,m=m,q=q,rank_method='distinct complete census node rows; no numerical singular-value truncation',dim_J=m+1-q,T=text(T),arithmetic_bits=ctx.prec,source_method='unchanged source form; analytic digamma/trigamma arch moments with explicit finite geometric tails',source_metadata=meta,B_symmetry_relative=text(bsym),kernel_symmetry_relative=text(ksym),solve_method='compiled Arb approximate LU; midpoint diagnostics, not interval inverse or source enclosure',inertia=inertia_record,rows=rows,seconds=time.monotonic()-start)
 return result,A,E

def main():
 p=argparse.ArgumentParser();p.add_argument('--input-root',type=Path,required=True);p.add_argument('--output',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--m',type=int,nargs='+',default=list(range(20,241)));p.add_argument('--world',nargs='+',choices=['zeta','dh'],default=['zeta','dh']);p.add_argument('--bits',type=int,default=1024);p.add_argument('--no-inertia',action='store_true');p.add_argument('--validate-cache',type=Path);args=p.parse_args();ctx.prec=args.bits;args.output.mkdir(parents=True,exist_ok=True)
 zpath=args.input_root/'zeta_zeros_capacity.csv';dpath=args.input_root/'edge_law/dh/dh_zeros_extended.json';zeta=[r['gamma'] for r in csv.DictReader(zpath.open())];dh=json.loads(dpath.read_text());co={w:coefficients(max(args.m),w) for w in args.world};allrows=[];records=[]
 for m in args.m:
  for world in args.world:
   path=args.output/f'{world}_m{m}_bits{args.bits}.json'
   if path.exists():r=json.loads(path.read_text())
   else:
    r,A,E=case(m,world,co[world],zeta,dh,not args.no_inertia)
    if args.validate_cache:
     src=json.loads(args.validate_cache.read_text());S=arb_mat(src['A']);err=max(abs(A[i,j]-S[i,j]) for i in range(m+1) for j in range(m+1));r['cached_A_max_absolute_difference']=text(err)
    path.write_text(json.dumps(r,indent=2)+'\n')
   allrows.extend(r['rows']);records.append({k:v for k,v in r.items() if k!='rows'});print(world,m,'q',r['q'],'neg',r['inertia']['negative'] if r['inertia'] else 'unchecked','Kendpoint',r['rows'][0]['K'],'seconds',r['seconds'],flush=True)
 with (args.output/'kernels.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(allrows[0]));w.writeheader();w.writerows(allrows)
 (args.output/'summary.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',cells=len(records),source_matrices_rebuilt=True,full_source_eigenproblems=0,kernel_is_Weyl_radius=False,records=records,sha256={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [zpath,dpath]}),indent=2)+'\n')
if __name__=='__main__':main()
