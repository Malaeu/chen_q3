"""Common real step carrier: source Schur and quiet Schur diagnostics only."""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import sys,json,csv,time,argparse,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent;BUS=P.parents[1];CORE=BUS/'screw_line_2026-11-02/innovation_law/core'
sys.path.insert(0,str(CORE));from scan import source

def fmt(x):return mp.nstr(x,mp.mp.dps)
def normop(A):
 if A.rows==0 or A.cols==0:return mp.mpf(0)
 if A.rows==A.cols:
  ev=mp.eigsy((A+A.T)/2,eigvals_only=True);return max(abs(x) for x in ev)
 ev=mp.eigsy(A.T*A,eigvals_only=True);return mp.sqrt(max(mp.mpf(0),ev[ev.rows-1]))
def inertia_eigs(ev,guard):return dict(negative=sum(x<-guard for x in ev),positive=sum(x>guard for x in ev),unresolved=sum(abs(x)<=guard for x in ev))
def inertia(A,guard):return inertia_eigs(mp.eigsy((A+A.T)/2,eigvals_only=True),guard) if A.rows else dict(negative=0,positive=0,unresolved=0)

def geometry(m):
 L=mp.log(m);delta=mp.log(mp.mpf(m)/(m-1));a=L-delta
 tags=[(F(j,2*m+1),F(0)) for j in range(2*m+1)]+[(F(1),F(-1))]+[(F(1),F(j-4,4)) for j in range(1,5)]
 points=[mp.mpf(x.numerator)/x.denominator*L+mp.mpf(y.numerator)/y.denominator*delta for x,y in tags]
 lengths=[points[i+1]-points[i] for i in range(len(points)-1)];assert all(x>0 for x in lengths);assert len(lengths)==2*m+5
 return L,delta,a,tags,points,lengths

def matrix(m,world):
 L,delta,a,tags,points,lengths=geometry(m);g0,_=source(world,L)
 @lru_cache(None)
 def gg(x,y):
  t=mp.mpf(x.numerator)/x.denominator*L+mp.mpf(y.numerator)/y.denominator*delta;return g0(t)
 def diff(i,j):return gg(tags[i][0]-tags[j][0],tags[i][1]-tags[j][1])
 d=len(lengths);A=mp.zeros(d)
 for i in range(d):
  for j in range(i,d):
   A[i,j]=A[j,i]=(diff(i+1,j+1)-diff(i+1,j)-diff(i,j+1)+diff(i,j))/mp.sqrt(lengths[i]*lengths[j])
 return A,(L,delta,a,points,lengths),dict(unique_source_arguments=gg.cache_info().currsize)

def step_eval(z,points,lengths):
 return [2*mp.exp(mp.j*z*(points[i]+points[i+1])/2)*mp.sin(z*lengths[i]/2)/(z*mp.sqrt(lengths[i])) for i in range(len(lengths))]

def zeros(world,T):
 if world!='dh':
  rr=list(csv.DictReader((BUS/'capacity_matrix_2026-11-02/zeros.csv').open()));zz=[dict(z=mp.mpf(x['gamma']),kind='zeta_real',height=mp.mpf(x['gamma'])) for x in rr if mp.mpf(x['gamma'])<T]
  if world=='plant':
   w=2*mp.pi/mp.log(2)+mp.j/4
   if mp.re(w)<T:zz.extend([dict(z=w,kind='plant_complex',height=mp.re(w)),dict(z=mp.conj(w),kind='plant_complex_conjugate',height=mp.re(w))])
  return zz
 rr=json.loads((BUS/'fake_worlds_2026-11-02/dh_zeros.json').read_text());assert T<mp.mpf(rr['height_bound'])
 zz=[dict(z=mp.mpf(x['gamma']),kind='DH_real',height=mp.mpf(x['gamma'])) for x in rr['critical_line_zeros'] if mp.mpf(x['gamma'])<T]
 for x in rr['off_line_pairs']:
  gam=mp.mpf(x['gamma']);eta=mp.mpf(x['sigma_right'])-mp.mpf('.5')
  if gam<T:zz.extend([dict(z=gam+mp.j*eta,kind='DH_complex',height=gam),dict(z=gam-mp.j*eta,kind='DH_complex_conjugate',height=gam)])
 return zz

def quiet(A,geom,world,kappa):
 L,delta,a,points,lengths=geom;T=kappa*2*mp.pi*((A.rows-5)//2)/L;zz=zeros(world,T);rows=[]
 for item in zz:
  values=step_eval(item['z'],points,lengths)
  for fn in [mp.re,mp.im]:
   row=mp.matrix([fn(x) for x in values]);n=mp.norm(row);assert n>0;rows.append([x/n for x in row])
 E=mp.matrix(rows);UE,s,V=mp.svd_r(E,full_matrices=True);guard=mp.mpf(10)**(-mp.mp.dps/2)*max(s);rank=sum(x>guard for x in s)
 close=any(guard/mp.mpf('1e5')<x<guard*mp.mpf('1e5') for x in s)
 if close:raise ArithmeticError('INCONCLUSIVE_RANK')
 d=A.rows;r=d-rank;U=V[:rank,:].T;Q=V[rank:,:].T if r else mp.zeros(d,0)
 er=mp.norm(E*Q) if r else mp.mpf(0);orth=mp.norm(Q.T*Q-mp.eye(r)) if r else mp.mpf(0)
 D=Q.T*A*Q if r else mp.zeros(0,0);G=U.T*A*U;B=Q.T*A*U if r else mp.zeros(0,rank)
 return Q,U,D,G,B,dict(T=fmt(T),zero_evaluation_points=len(zz),real_constraint_rows=E.rows,rank=rank,quiet_dimension=r,smallest_listed_singular=fmt(min(s)),rank_guard=fmt(guard),constraint_residual=fmt(er),orthogonality_error=fmt(orth),complex_evaluation_points=sum('complex' in x['kind'] for x in zz),zero_constraints=[dict(z=fmt(x['z']),kind=x['kind']) for x in zz])

def schur_record(A,C,B,G,threshold,guard):
 full=inertia(A-threshold*mp.eye(A.rows),guard);old=C-threshold*mp.eye(C.rows)
 elim=inertia(old,guard)
 if elim['unresolved']:return dict(guard='UNRESOLVED_ELIMINATED',full=full,eliminated=elim,schur=None)
 S=G-threshold*mp.eye(G.rows)-B.T*(old**-1)*B if C.rows else G-threshold*mp.eye(G.rows)
 ins=inertia(S,guard);ok=full['negative']==elim['negative']+ins['negative'] and not(full['unresolved'] or ins['unresolved'])
 if not ok:raise ArithmeticError('Inertia identity failed')
 return dict(guard='RESOLVED',full=full,eliminated=elim,schur=ins,schur_minimum=fmt(mp.eigsy(S,eigvals_only=True)[0]) if S.rows else None,inertia_identity=True)

def common(m,world,dps):
 A,geom,meta=matrix(m,world);d=A.rows;old=d-4;C=A[:old,:old];B=A[:old,old:];G=A[old:,old:];guard=mp.mpf(10)**(-dps+20)*max(1,mp.norm(A));ev=mp.eigsy(A,eigvals_only=True);ic=inertia(C,guard)
 if ic['unresolved']:raise ArithmeticError('UNRESOLVED_PAST')
 S=G-B.T*(C**-1)*B;se,Z=mp.eigsy(S);z=Z[:,0];past=-(C**-1)*B*z;f=mp.matrix(list(past)+list(z));energy=(f.T*A*f)[0];err=abs(energy-se[0]);station=mp.norm(C*past+B*z)
 assert err<guard*max(1,mp.norm(f)**2)*mp.mpf('1e5')
 i0=schur_record(A,C,B,G,mp.mpf(0),guard);i2=schur_record(A,C,B,G,mp.mpf(2),guard)
 return A,geom,ev,f,dict(m=m,world=world,dps=dps,dimension=d,old_dimension=old,fresh_dimension=4,source_calls=meta['unique_source_arguments'],old_negative_index=ic['negative'],section_interpretation='OPTIMAL_GIVEN_FRESH_DIRECTION' if ic['negative']==0 else 'STATIONARY_ALGEBRAIC_INF_MINUS_INFINITY',sigma_section=fmt(se[0]),fresh_z_norm=fmt(mp.norm(z)),full_f_norm=fmt(mp.norm(f)),energy_error=fmt(err),old_stationarity_residual=fmt(station),full_minimum=fmt(ev[0]),section0=i0,section2=i2,full_f=[fmt(x) for x in f],fresh_z=[fmt(x) for x in z],matrix_guard=fmt(guard))

def one(m,world,dps,c,cname,ctx):
 A,geom,ev,f,base=ctx;L=geom[0];kappa=1+c*(1+mp.log(L))/L;Q,U,D,G,B,qmeta=quiet(A,geom,world,kappa);r=qmeta['quiet_dimension'];guard=mp.mpf(base['matrix_guard']);n=mp.norm(f);pj=mp.norm(Q.T*f) if r else mp.mpf(0);pc=mp.norm(U.T*f);angle=mp.acos(min(mp.mpf(1),max(mp.mpf(0),pj/n)))*180/mp.pi
 lam=ev[r];den=lam*pc**2;ratio=mp.mpf(base['sigma_section'])/den if lam>guard and den>guard*max(1,n*n) else None
 sq2=schur_record(A,D,B,G,mp.mpf(2),guard);sq0=schur_record(A,D,B,G,mp.mpf(0),guard)
 aq=normop(A*Q) if r else mp.mpf(0);cn=normop(D) if r else mp.mpf(0)
 row=dict(m=m,world=world,dps=dps,cutoff=cname,c=fmt(c),kappa=fmt(kappa),T=qmeta['T'],dimension=A.rows,rank=qmeta['rank'],quiet_dimension=r,constraint_rows=qmeta['real_constraint_rows'],complex_evaluation_points=qmeta['complex_evaluation_points'],old_negative_index=base['old_negative_index'],section_interpretation=base['section_interpretation'],sigma_section=base['sigma_section'],full_minimum=base['full_minimum'],full_f_norm=base['full_f_norm'],angle_f_J_degrees=fmt(angle),projection_quiet_norm=fmt(pj),projection_complement_norm=fmt(pc),delta_full_AQ=fmt(aq),quiet_compression_norm=fmt(cn),lambda_r=fmt(lam),ratio=fmt(ratio) if ratio is not None else '',ratio_status='RESOLVED_POSITIVE_DENOMINATOR' if ratio is not None else 'INVALID_OR_UNRESOLVED_DENOMINATOR',quiet_D_below2=sq2['eliminated']['negative']==r and sq2['eliminated']['unresolved']==0,quiet_S2_min=sq2.get('schur_minimum',''),quiet_S2_negative=sq2['schur']['negative'] if sq2.get('schur') else '',quiet_D2_negative=sq2['eliminated']['negative'],full_A2_negative=sq2['full']['negative'],section_S0_min=base['section0'].get('schur_minimum',''),section_S0_negative=base['section0']['schur']['negative'],full_A0_negative=base['section0']['full']['negative'],section_S2_negative=base['section2']['schur']['negative'] if base['section2'].get('schur') else '',section_C2_negative=base['section2']['eliminated']['negative'],quiet_S0_negative=sq0['schur']['negative'] if sq0.get('schur') else '',quiet_D0_negative=sq0['eliminated']['negative'],constraint_residual=qmeta['constraint_residual'],orthogonality_error=qmeta['orthogonality_error'],smallest_constraint_singular=qmeta['smallest_listed_singular'])
 record=dict(status='DIAGNOSTIC_NEVER_A_PROOF',metrics=row,section=base,quiet=qmeta,quiet_schur0=sq0,quiet_schur2=sq2)
 (P/f'cell_{world}_m{m}_{cname}_dps{dps}.json').write_text(json.dumps(record,indent=2)+'\n');print(world,m,cname,dps,'r',r,'oldneg',base['old_negative_index'],'s',base['sigma_section'][:15],'angle',row['angle_f_J_degrees'][:12],flush=True)
 return row

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--dps',type=int,default=80);ap.add_argument('--ms',nargs='+',type=int,default=[16,24,32,40]);ap.add_argument('--worlds',nargs='+',default=['zeta','dh','plant']);ap.add_argument('--cutoffs',nargs='+',default=['kappa1','cquarter','chalf']);a=ap.parse_args();mp.mp.dps=a.dps;rows=[];start=time.monotonic()
 cs=dict(kappa1=mp.mpf(0),cquarter=mp.mpf(1)/4,chalf=mp.mpf(1)/2)
 for m in a.ms:
  for world in a.worlds:
   ctx=common(m,world,a.dps)
   for name in a.cutoffs:rows.append(one(m,world,a.dps,cs[name],name,ctx))
   (P/f'partial_dps{a.dps}.json').write_text(json.dumps(rows,indent=2)+'\n')
 with (P/f'metrics_dps{a.dps}.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
 (P/f'run_dps{a.dps}.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',seconds=time.monotonic()-start,rows=len(rows),dps=a.dps),indent=2)+'\n')
if __name__=='__main__':main()
