"""DH EDGE_LAW_v1 diagnostics; no interval spectrum, census, or zero-tail certificate."""
from pathlib import Path
import sys,json,time,hashlib
import mpmath as mp
import numpy as np
from scipy.linalg import eigh
P=Path(__file__).resolve().parent;FAKE=P.parents[1];BASE=FAKE.parent
sys.path.insert(0,str(P));sys.path.insert(0,str(FAKE));sys.path.insert(0,str(BASE/'capacity_matrix_2026-11-02'))
from extend_zeros import register
from dh_quiet import rows as dh_rows
from capacity import Erow

def fmt(x):return mp.nstr(x,115)
def ser(x):
 if isinstance(x,mp.matrix):return [[fmt(x[i,j]) for j in range(x.cols)] for i in range(x.rows)]
 if isinstance(x,mp.mpf):return fmt(x)
 if isinstance(x,list):return [ser(v) for v in x]
 if isinstance(x,dict):return {k:ser(v) for k,v in x.items()}
 return x

def minimum(C):
 n=C.rows;F=np.array([[float(C[i,j]) for j in range(n)] for i in range(n)]);w,V=eigh(F);gap=float(w[1]-w[0]) if n>1 else float('inf')
 residual=float(np.linalg.norm(F@V-V*w,ord='fro'));orth=float(np.linalg.norm(V.T@V-np.eye(n),ord='fro'))
 rounding=mp.sqrt(mp.fsum((C[i,j]-mp.mpf(float(F[i,j])))**2 for i in range(n) for j in range(n)))
 error=rounding+mp.mpf(residual)+mp.mpf(orth)*max(abs(mp.mpf(x)) for x in w)
 if gap<=100*float(error):raise ArithmeticError('Full float spectrum does not isolate its minimum numerically')
 B=(V[:,1:]*(1/(w[1:]-w[0])))@V[:,1:].T if n>1 else np.zeros((1,1));B=mp.matrix(B.tolist());v=mp.matrix(V[:,0].tolist());v/=mp.norm(v);history=[]
 for iteration in range(14):
  lam=mp.fdot(v,C*v);r=C*v-lam*v;err=mp.norm(r);history.append(err)
  if err<mp.mpf('1e-85'):break
  correction=B*r;correction-=v*mp.fdot(v,correction);v-=correction;v/=mp.norm(v)
 if history[-1]>mp.mpf('1e-70'):raise ArithmeticError('High-precision residual refinement did not converge')
 return lam,v,{'method':'full float eigenspectrum isolates minimum; high-precision projected pseudoinverse refinement','float_eigenvalues':[float(x) for x in w],'float_minimum_gap':gap,'float_eigenbasis_residual_F':residual,'float_eigenbasis_orthogonality_F':orth,'matrix_rounding_F':rounding,'combined_numerical_separation_error':error,'gap_over_numerical_error':mp.mpf(gap)/error,'refinement_residual_history':history,'final_residual':history[-1],'minimum_isolation_interval_certified':False}

def select_census(m,mode):
 old=FAKE/'dh_zeros.json';extended=P/'dh_zeros_extended.json';L=mp.log(m);Omega=2*mp.pi*m/L;Tnative=mp.mpf('1.1')*Omega
 source=old if mode=='matched' or Tnative<=230 else (extended if extended.exists() else old);data=json.loads(source.read_text())
 if mode=='native':
  if mp.mpf(data['height_bound'])<Tnative:raise ValueError('Census coverage insufficient for native cutoff')
  if data['completeness_status'].startswith('INCOMPLETE'):raise ValueError('Extension count mismatch blocks native run')
  return data,source,Tnative,None
 zeros=[mp.mpf(r['gamma']) for r in __import__('csv').DictReader((BASE/'capacity_matrix_2026-11-02/zeros.csv').open())]
 if max(zeros)<Tnative:raise ValueError('Zeta zero table does not cover matched target')
 target=sum(g<Tnative for g in zeros)
 events=sorted([(mp.mpf(r['gamma']),1) for r in data['critical_line_zeros']]+[(mp.mpf(r['gamma']),2) for r in data['off_line_pairs']]);count=0
 for i,(g,n) in enumerate(events[:-1]):
  count+=n
  if count==target:return data,source,(g+events[i+1][0])/2,target
 raise ValueError(f'Exact matched q={target} is not realized; report obstruction rather than changing count')

def zero_side(f,m,data,T):
 line=mp.mpf(0);pa=mp.mpf(0);nb=mp.mpf(0);pairs=[]
 for r in data['critical_line_zeros']:
  g=mp.mpf(r['gamma'])
  if g>=T:continue
  val=mp.fdot(mp.matrix(Erow(g,m)),f);line+=2*abs(val)**2
 for r in data['off_line_pairs']:
  g=mp.mpf(r['gamma'])
  if g>=T:continue
  d=mp.mpf(r['sigma_right'])-mp.mpf('.5');v=mp.fdot(mp.matrix(Erow(g+mp.j*d,m)),f);a=mp.re(v);b=mp.im(v);pa+=4*a*a;nb-=4*b*b
  pairs.append({'gamma':g,'sigma_right':mp.mpf(r['sigma_right']),'real_transform':a,'imag_transform':b,'positive_square_term':4*a*a,'negative_square_term':-4*b*b,'signed_quartet_term':4*(a*a-b*b),'listed_multiplicity':1})
 return {'cutoff':T,'positive_line_term':line,'positive_quartet_square_term':pa,'negative_quartet_square_term':nb,'signed_truncated_zero_sum':line+pa+nb,'ordinary_positive_node_sum':line+pa-nb,'pairs':pairs,'normalization':'line:2|F(gamma)|^2; quartet:4(a^2-b^2); negative term=-4*b^2 per stored simple pair, not multiplicity-only -4nu','uncomputed_tail_certified':False,'multiplicities_interval_certified':False}

def build_source(m,dps=120,order=192):
 from dh_matrix import build_mp
 register(f'DH matrix m{m}, {dps}dps GL{order}', 'Rebuild the original pole-free odd-gamma source using all coefficients; no census assumptions enter.', 'Nonfinite or nonsymmetric output blocks use.')
 start=time.monotonic();A,metadata=build_mp(m,dps,order)
 out={'status':'DIAGNOSTIC_NEVER_A_PROOF','m':m,'N':m,'dps':dps,'order':order,'A':[[mp.nstr(A[i,j],dps) for j in range(m+1)] for i in range(m+1)],'seconds':time.monotonic()-start}
 path=P/f'source_m{m}_dps{dps}_gl{order}.json';path.write_text(json.dumps(out,indent=2)+'\n');return path

def run(m,mode):
 register(f'DH edge m{m} {mode}', 'Evaluate one fixed native or genuinely density-matched interpolation complement. The full compressed numerical spectrum identifies the minimum; endpoint and R use that same vector. No cofinal conclusion.', 'Insufficient/unmatched census coverage, QR failure, failed minimum separation/refinement, or vanishing endpoint denominator blocks completion. No missing quartet or tail is discarded.')
 mp.mp.dps=120;start=time.monotonic();src=P/f'source_m{m}_dps120_gl192.json'
 if not src.exists():build_source(m)
 A=mp.matrix(json.loads(src.read_text())['A']);data,zpath,T,target=select_census(m,mode);E,signs,labels=dh_rows(data,m,T);q=E.rows;d=m+1
 if q>=d:raise ValueError('No nontrivial quiet complement geometry under requested full-row construction')
 norms=[mp.norm(E[i,:]) for i in range(q)];Et=mp.matrix([[E[i,j]/norms[i] for i in range(q)] for j in range(d)])
 orth,Rqr=mp.qr(Et);U=orth[:,:q];Q=orth[:,q:];C=U.T*A*U;lam,y,control=minimum(C);f=U*y;f/=mp.norm(f)
 if f[max(range(d),key=lambda i:abs(f[i]))]<0:f=-f
 endpoint=mp.fsum((1 if n==0 else mp.sqrt(2))*f[n] for n in range(d))/mp.sqrt(mp.log(m));edge2=endpoint**2;scale=edge2*mp.log(T)/(mp.pi*T)
 if not scale:raise ArithmeticError('Zero endpoint scale')
 rootnum=-lam if lam<0 else None
 result={'status':'DIAGNOSTIC_NEVER_A_PROOF','world':'dh','m':m,'N':m,'dps':120,'order':192,'mode':mode,'T':T,'q':q,'rank':q,'dim_J':d-q,'target_zeta_constraint_count':target,'complement_minimum':lam,'source_Rayleigh':mp.fdot(f,A*f),'endpoint':endpoint,'endpoint_squared':edge2,'edge_scale_logT_over_piT':scale,'R_edge':lam/scale,'R_conductor_corrected_secondary':lam/(edge2*(mp.log(5*T/(2*mp.pi))+1)/(mp.pi*T)),'physical_modal_coefficients':list(f),'minimum_controls':control,'Q_orthogonality':mp.norm(Q.T*Q-mp.eye(d-q)),'U_orthogonality':mp.norm(U.T*U-mp.eye(q)),'E_Q_residual':mp.norm(E*Q),'row_scaled_QR_residual':mp.norm(Et-orth*Rqr),'minimum_abs_QR_diagonal':min(abs(Rqr[i,i]) for i in range(q)),'maximum_abs_QR_diagonal':max(abs(Rqr[i,i]) for i in range(q)),'rank_and_census_interval_certified':False,'census_status':data['completeness_status'],'census_height_bound':data['height_bound'],'zero_side_below_T':zero_side(f,m,data,T),'zero_side_full_saved_census':zero_side(f,m,data,mp.mpf(data['height_bound'])),'source_sha256':{src.name:hashlib.sha256(src.read_bytes()).hexdigest(),str(zpath.relative_to(FAKE)):hashlib.sha256(zpath.read_bytes()).hexdigest()},'seconds':time.monotonic()-start}
 result['unpaid_difference_from_full_saved_zero_sum']=lam-result['zero_side_full_saved_census']['signed_truncated_zero_sum']
 (P/f'cell_m{m}_{mode}_dps120_gl192.json').write_text(json.dumps(ser(result),indent=2)+'\n');print('CELL DONE',m,mode,'lambda',mp.nstr(lam,16),'R',mp.nstr(result['R_edge'],16),flush=True)
if __name__=='__main__':
 if sys.argv[1]=='build':build_source(int(sys.argv[2]))
 else:run(int(sys.argv[1]),sys.argv[2])
