"""EDGE_LAW_RELLICH_v1. DIAGNOSTIC_NEVER_A_PROOF. Fixed saved vectors only.
No eigensolver; no zero search; zero tails are source balances.
"""
from pathlib import Path
import mpmath as mp
import json,csv,sys,time,hashlib
from functools import lru_cache
P=Path(__file__).resolve().parent
IN=Path(sys.argv[1]) if len(sys.argv)>1 else P.parent/'inputs'
OUT=P/'cells';OUT.mkdir(exist_ok=True)
mp.mp.dps=110

def serial(x):
 if isinstance(x,(mp.mpf,mp.mpc)):return mp.nstr(x,100)
 if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
 if isinstance(x,(list,tuple)):return [serial(v) for v in x]
 return x

def mangoldt(n):
 for p in range(2,n+1):
  if n%p==0:
   k=n
   while k%p==0:k//=p
   return mp.log(p) if k==1 else mp.mpf(0)
 return mp.mpf(0)

@lru_cache(None)
def coeffs(m,world):
 if world=='zeta':return [mp.mpf(0)]+[mangoldt(n) for n in range(1,m+1)]
 t=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
 a=[mp.mpf(0),mp.mpf(1),t,-t,mp.mpf(-1)];b=[mp.mpf(0)]*(m+1)
 for n in range(2,m+1):b[n]=a[n%5]*mp.log(n)-mp.fsum(b[d]*a[(n//d)%5] for d in range(2,n) if n%d==0)
 return b

@lru_cache(None)
def nodes(order):
 z,w=mp.gauss_quadrature(order,'legendre')
 return [((mp.mpf(p)+(v+1)/2)/8,ww/16) for p in range(8) for v,ww in zip(z,w)]

@lru_cache(None)
def build(m,world,order):
 L=mp.log(m);d=m+1;b=coeffs(m,world);alpha=mp.mpf('.5') if world=='zeta' else mp.mpf('1.5')
 sm=[mp.mpf(0)]*d;di=sm.copy();ps=sm.copy();pd=sm.copy()
 for y,w in nodes(order):
  x=L*y;wt=L*w*mp.exp(-alpha*x)/(-mp.expm1(-2*x));co=mp.cos(2*mp.pi*y);si=mp.sin(2*mp.pi*y);cn=mp.mpf(1);sn=mp.mpf(0)
  for n in range(d):
   sm[n]+=wt*sn;di[n]+=wt*(2*y+2*(1-y)*(1-cn)+(sn/(mp.pi*n) if n else 0));cn,sn=cn*co-sn*si,sn*co+cn*si
 for k in range(2,m):
  if not b[k]:continue
  y=mp.log(k)/L;wt=b[k]/mp.sqrt(k);co=mp.cos(2*mp.pi*y);si=mp.sin(2*mp.pi*y);cn=mp.mpf(1);sn=mp.mpf(0)
  for n in range(d):
   ps[n]+=wt*sn;pd[n]+=wt*(2*(1-y)*cn-(sn/(mp.pi*n) if n else 0));cn,sn=cn*co-sn*si,sn*co+cn*si
 ds=[mp.mpf(1)]+[mp.sqrt(2)]*m;beta=[sm[i]+ps[i] for i in range(d)]
 c=-mp.euler-mp.log(8*mp.pi)-mp.pi/2 if world=='zeta' else -mp.euler-mp.log(8*mp.pi/5)+mp.pi/2
 aa=mp.exp(-L/2);tail=mp.atanh(aa)+(mp.atan(aa) if world=='zeta' else -mp.atan(aa));A=mp.zeros(d)
 pole=mp.matrix([4*mp.sqrt(2)*ds[n]*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*mp.pi**2*n*n) for n in range(d)])
 for i in range(d):
  A[i,i]=c+di[i]+2*tail-pd[i]
  for j in range(i+1,d):A[i,j]=A[j,i]=ds[i]*ds[j]/mp.pi*(i*beta[i]-j*beta[j])/(i*i-j*j)
 if world=='zeta':A+=pole*pole.T
 return A,c,alpha,tail,pole

@lru_cache(None)
def generators(m):
 L=mp.log(m);b=L/2;d=m+1;ds=[mp.mpf(1)]+[mp.sqrt(2)]*m;D=mp.zeros(d);Da=mp.zeros(d)
 def I2(k):
  if k==0:return 2*b**3/3
  z=2*mp.pi*k/L;return 4*b*(-1)**k/z**2
 def I3(k):
  if k==0:return mp.mpf(0)
  z=2*mp.pi*k/L;return 2*(-1)**k*(-b**3/z+6*b/z**3)
 for i in range(d):
  for j in range(d):
   D[i,j]=(mp.mpf('.5') if i==0 else mp.mpf(1)) if i==j else ds[i]*ds[j]*j*j/(j*j-i*i)
   sign=(-1)**(i+j);T2=ds[i]*ds[j]*sign/(2*L)*(I2(i-j)+I2(i+j));T3=-ds[i]*ds[j]*sign*(2*mp.pi*j/L)/(2*L)*(I3(j+i)+I3(j-i))
   Da[i,j]=D[i,j]-(T3+mp.mpf('1.5')*T2)/b**2
 eb=mp.matrix([v/mp.sqrt(L) for v in ds]);return D,Da,eb

def eval_fourier(v,z,L):
 # Endpoint-signed carrier; all census nodes avoid removable modal poles.
 if not z: return mp.sqrt(L)*v[0],mp.mpf(0)
 sm=mp.mpc(0);sm2=mp.mpc(0)
 for n,fn in enumerate(v):
  cc=(1 if n==0 else mp.sqrt(2))*fn;den=z*z-(2*mp.pi*n/L)**2
  sm+=cc/den;sm2+=cc/(den*den)
 sn=mp.sin(z*L/2);co=mp.cos(z*L/2)
 F=2*z*sn*sm/mp.sqrt(L);Fp=2*((sn+L*z*co/2)*sm-2*z*z*sn*sm2)/mp.sqrt(L)
 return F,Fp

def source_weak(f,m,world,order):
 L=mp.log(m);d=m+1;fb=mp.fsum(f[n]*(1 if n==0 else mp.sqrt(2)) for n in range(d))/mp.sqrt(L)
 bcoef=coeffs(m,world);A,c,alpha,tail,pole=build(m,world,order)
 sc=[mp.mpf(0)]*d
 for i in range(1,d):sc[i]-=f[i]**2/(mp.pi*i)
 for i in range(d):
  for k in range(i+1,d):
   v=2*f[i]*f[k]*(1 if i==0 else mp.sqrt(2))*mp.sqrt(2)/(mp.pi*(i*i-k*k));sc[k]+=v*k;sc[i]-=v*i
 def values(s):
  co=mp.cos(2*mp.pi*s/L);si=mp.sin(2*mp.pi*s/L);cn=mp.mpf(1);sn=mp.mpf(0);qp=mp.mpf(0);edge=mp.mpf(0);diff=mp.mpf(0)
  for n in range(d):
   w=2*mp.pi*n/L;cc=(1 if n==0 else mp.sqrt(2))*f[n]/mp.sqrt(L)
   qp+=-2*f[n]**2*cn/L-2*f[n]**2*(1-s/L)*w*sn+sc[n]*w*cn
   edge+=cc*cn;diff+=cc*(1-cn)
   cn,sn=cn*co-sn*si,sn*co+cn*si
  return qp,edge,diff
 Bar=mp.mpf(0);Var=mp.mpf(0)
 for y,w in nodes(order):
  s=L*y;wt=L*w*mp.exp(-alpha*s)/(-mp.expm1(-2*s));qp,edge,diff=values(s)
  Bar+=2*L*fb*wt*diff;Var-=wt*s*qp
 Bar+=2*L*fb*fb*tail
 Bprime=mp.mpf(0);Vprime=mp.mpf(0)
 for n in range(2,m+1):
  if not bcoef[n]:continue
  s=mp.log(n);qp,edge,_=values(s);Bprime-=2*L*fb*bcoef[n]/mp.sqrt(n)*edge;Vprime-=bcoef[n]/mp.sqrt(n)*s*qp
 Bpole=mp.mpf(0);Vpole=mp.mpf(0)
 if world=='zeta':
  F,Fp=eval_fourier(list(f),mp.j/2,L);pf=mp.fdot(pole,f);pb=mp.sqrt(2)*mp.cosh(L/4)
  Bpole=2*pf*L*fb*pb;Vpole=2*pf*mp.sqrt(2)*mp.re(-F/2-mp.j*Fp/2)
 Bconst=c*L*fb*fb
 B=Bconst+Bar+Bprime+Bpole;V=Var+Vprime+Vpole
 return {'total':B+V,'boundary':B,'volume':V,'boundary_constant':Bconst,'boundary_arch':Bar,'boundary_arithmetic':Bprime,'boundary_pole':Bpole,'volume_arch':Var,'volume_arithmetic':Vprime,'volume_pole':Vpole}

def zero_blocks(f,df,kf,eb,m,T,world):
 L=mp.log(m);fb=mp.fdot(eb,f);caps=[T,mp.mpf(400 if world=='zeta' else 310)]
 if world=='zeta':events=[(mp.mpf(r['gamma']),mp.mpf(0),'line') for r in csv.DictReader((IN/'zeros.csv').open()) if mp.mpf(r['gamma'])<=400]
 else:
  z=json.loads((IN/'dh_zeros_extended.json').read_text());events=[(mp.mpf(r['gamma']),mp.mpf(0),'line') for r in z['critical_line_zeros']]+[(mp.mpf(r['gamma']),mp.mpf(r['sigma_right'])-mp.mpf('.5'),'quartet') for r in z['off_line_pairs']]
 out={block:{key:mp.mpf(0) for key in ['energy','commutator','finite_volume','finite_boundary','weak_total','weak_boundary','weak_volume']} for block in ['head','prefix']};terms=[]
 for gamma,eta,kind in sorted(events):
  if gamma>caps[1]:continue
  z=gamma+mp.j*eta;F,Fp=eval_fourier(list(f),z,L);FD,_=eval_fourier(list(df),z,L);FK,_=eval_fourier(list(kf),z,L);E,_=eval_fourier(list(eb),z,L)
  H=L*fb*mp.cos(L*z/2)-F/2-z*Fp;He=L*fb*mp.cos(L*z/2)
  fac=2 if kind=='line' else 4
  energy=fac*mp.re(F*F);volume=2*fac*mp.re(F*FD);boundary=L*fb*fac*mp.re(F*E);comm=2*fac*mp.re(F*FK)
  weak=2*fac*mp.re(F*H);weakedge=2*fac*mp.re(F*He)
  block='head' if gamma<=T else 'prefix';data={'energy':energy,'commutator':comm,'finite_volume':volume,'finite_boundary':boundary,'weak_total':weak,'weak_boundary':weakedge,'weak_volume':weak-weakedge}
  for key,val in data.items():out[block][key]+=val
  if kind=='quartet':terms.append({'gamma':gamma,'eta':eta,'block':block,**data})
 out['census_cutoff']=caps[1];out['quartets']=terms;return out

def load_case(path):
 raw=json.loads(path.read_text())
 if path.name.startswith('ledger_'):
  d=raw['summary'];return d['world'],d['m'],d['q'],mp.mpf(d['cutoff_T']),mp.matrix(list(map(mp.mpf,raw['unit_physical_modal_vector']))),mp.mpf(d['complement_minimum']),d['cutoff_mode']
 world=raw['world'];v=raw.get('complement_f',raw.get('physical_modal_coefficients'))
 return world,raw['m'],raw['q'],mp.mpf(raw['T']),mp.matrix(list(map(mp.mpf,v))),mp.mpf(raw['complement_minimum']),raw.get('cutoff_mode',raw.get('mode'))

def run(path,order=192):
 start=time.time();world,m,q,T,f,saved,mode=load_case(path);f/=mp.norm(f);L=mp.log(m);D,Da,eb=generators(m);K=(D-D.T)/2;A,*_=build(m,world,order);Af=A*f;lam=mp.fdot(f,Af);r=Af-lam*f;df=D*f;kf=K*f;fb=mp.fdot(eb,f);ab=mp.fdot(eb,Af)
 V=2*mp.fdot(Af,df);B=L*fb*ab;C=V-B;direct=mp.fdot(f,A*(D*f)-D*(A*f));leak=2*mp.fdot(r,kf)
 weak=source_weak(f,m,world,order);zeros=zero_blocks(f,df,kf,eb,m,T,world)
 for label in ['energy','commutator','finite_volume','finite_boundary','weak_total']:
  full={'energy':lam,'commutator':C,'finite_volume':V,'finite_boundary':B,'weak_total':weak['total']}[label]
  zeros['source_balance_'+label+'_beyond_census']=full-zeros['head'][label]-zeros['prefix'][label]
  zeros['source_balance_'+label+'_above_T']=full-zeros['head'][label]
 def pred(v):return {'ratio_to_lambda':v/lam,'relative_difference_from_lambda':abs(v-lam)/abs(lam),'passes_10pct':abs(v-lam)<=abs(lam)/10}
 result={'status':'DIAGNOSTIC_NEVER_A_PROOF','world':world,'m':m,'q':q,'mode':mode,'T':T,'dps':mp.mp.dps,'order':order,'input':path.name,'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'lambda':lam,'saved_lambda':saved,'lambda_relative_replay_error':abs(lam-saved)/abs(saved),'f_b':fb,'fprime_b_exact':0,'finite':{'volume':V,'boundary_subtracted':B,'commutator':C,'direct_commutator':direct,'leakage_form':leak,'residual_norm':mp.norm(r),'own_eigenvalue_boundary_piece':lam*L*fb**2,'own_eigenvalue_volume_piece':lam*L*fb**2,'boundary_vs_lambda':pred(B),'negative_boundary_vs_lambda':pred(-B)},'physical_weak':weak,'weak_boundary_vs_lambda':pred(weak['boundary']),'projection_return_weak_minus_finite_volume':weak['total']-V,'zero_blocks':zeros,'alternative_generator':{'name':'a=x(1-x²/b²)','commutator':2*mp.fdot(Af,Da*f),'green_boundary_exact':0},'validation':{'green_matrix_error':mp.norm(D+D.T-L*eb*eb.T),'alternative_skew_error':mp.norm(Da+Da.T),'commutator_direct_error':abs(C-direct),'commutator_leakage_error':abs(C-leak),'finite_zero_split_head_error':abs(zeros['head']['commutator']-zeros['head']['finite_volume']+zeros['head']['finite_boundary'])},'seconds':time.time()-start}
 name=path.stem+f'_o{order}';(OUT/(name+'.json')).write_text(json.dumps(serial(result),indent=2)+'\n');print(world,m,q,mode,'lambda',mp.nstr(lam,8),'C',mp.nstr(C,8),'B/lambda',mp.nstr(B/lam,8),'Bweak/lambda',mp.nstr(weak['boundary']/lam,8),'sec',round(time.time()-start,2),flush=True)
 return result

if __name__=='__main__':
 order=int(sys.argv[2]) if len(sys.argv)>2 else 192
 files=sorted(IN.glob('ledger_*.json'))+sorted(IN.glob('zeta_cell_*.json'))+sorted(IN.glob('dh_cell_*.json'))
 for path in files:run(path,order)
