"""EDGE_CAPACITY_v1: finite source energy split, no infinite zero-tail sum.

DIAGNOSTIC_NEVER_A_PROOF. Reuse saved physical A,E,f only. No matrix rebuild,
eigensystem, new zero search, or route-state export. See 3fef776: (5.4)–(5.7).
"""
from pathlib import Path
import argparse,json,hashlib,time
import mpmath as mp
P=Path(__file__).resolve().parent
SOURCE_COMMIT='3fef776b3bd0ebeb9d87e665432ae3e423f2dfb1'
SOURCE_BLOB='33a918fc7faad0a56005574d8b6e158eae4db9f2'

def serial(x,digits=190):
 if isinstance(x,mp.mpf):return mp.nstr(x,digits)
 if isinstance(x,mp.mpc):return dict(real=mp.nstr(mp.re(x),digits),imag=mp.nstr(mp.im(x),digits))
 if isinstance(x,mp.matrix):return [[serial(x[i,j],digits) for j in range(x.cols)] for i in range(x.rows)]
 if isinstance(x,dict):return {str(k):serial(v,digits) for k,v in x.items()}
 if isinstance(x,(tuple,list)):return [serial(v,digits) for v in x]
 return x

def evaluate(d,dps):
 mp.mp.dps=dps;m=int(d['m']);N=int(d.get('N',m));L=mp.mpf(d['L']) if 'L' in d else mp.log(m);T=mp.mpf(d['T']);A=mp.matrix(d['A']);E=mp.matrix(d['E'])
 fv=d.get('complement_f')
 if fv is None:fv=d.get('unit_physical_modal_vector')
 if fv is None:fv=d.get('f')
 if fv is None:raise KeyError('No saved selected physical modal vector')
 f=mp.matrix(fv)
 if f.cols!=1:
  if f.rows==1:f=f.T
  else:raise ValueError('Selected vector is not a single column')
 assert f.rows==N+1 and A.rows==N+1 and A.cols==N+1 and E.cols==N+1
 if any(mp.im(x) for x in f):raise ValueError('This implementation expects saved real physical coefficients; complex f requires conjugate-reflection metric')
 original_norm=mp.norm(f);f/=original_norm
 ds=mp.matrix([mp.mpf(1)]+[mp.sqrt(2)]*N)
 e=(ds.T*f)[0]/mp.sqrt(L);chi=mp.zeros(N+1,1);chi[0]=mp.sqrt(L);h=f-e*chi
 if str(d.get('world','')).lower() in ('dh','davenport-heilbronn') and 'row_signs' not in d:
  raise ValueError('DH head requires the saved true signed row metric; a positive capacity Gram is forbidden')
 signs=d.get('row_signs',[1]*E.rows)
 if len(signs)!=E.rows:raise ValueError('Head metric dimensions disagree')
 # For the saved DH realification sqrt2 Re(v), sqrt2 Im(v), +/- signs
 # give the true quartet form4(Re(v)^2-Im(v)^2), NOT a capacity Gram.
 signs=list(map(mp.mpf,signs))
 Ef=E*f;Echi=E*chi;Eh=E*h
 def pair(x,y):return 2*mp.fsum(signs[k]*x[k]*y[k] for k in range(E.rows))
 def form(x,y):return (x.T*A*y)[0]
 Kf=form(f,f);Kchi=form(chi,chi);Kchih=form(chi,h);Kh=form(h,h)
 Hf=pair(Ef,Ef);Hchi=pair(Echi,Echi);Hchih=pair(Echi,Eh);Hh=pair(Eh,Eh)
 C=Kchi-Hchi;X=2*e*(Kchih-Hchih);V=Kh-Hh;edge=e*e*C;rhs=Hf+edge+X+V
 raw=dict(head_H=Hf,constant_source_K=Kchi,constant_head=Hchi,finite_C_T=C,edge_amplitude_e=e,edge_amplitude_squared=e*e,constant_remainder_pairing=Kchih,constant_remainder_head_pairing=Hchih,cross_X=X,remainder_source_K=Kh,remainder_head=Hh,remainder_V=V,edge_energy_e2C=edge,source_energy_Kf=Kf,split_sum=rhs,source_energy_identity_residual=rhs-Kf)
 scaled=None
 if e:
  scale=e*e*mp.log(T)/(mp.pi*T)
  scaled=dict(scale_e2_logT_over_piT=scale,R_total=Kf/scale,R_head=Hf/scale,R_C=edge/scale,R_cross=X/scale,R_volume=V/scale,R_sum=rhs/scale,R_identity_residual=(rhs-Kf)/scale,R_complete_defect=(Hf+X+V)/scale,piT_C_over_logT=mp.pi*T*C/mp.log(T))
  scaled['R_sum_minus_total']=scaled['R_sum']-scaled['R_total']
 source_lambda=d.get('complement_minimum',d.get('lambda',d.get('eigenvalue')))
 checks=dict(original_saved_norm=original_norm,renormalized_norm=mp.norm(f),h_norm_squared=(h.T*h)[0],h_boundary_trace=(ds.T*h)[0]/mp.sqrt(L),chi_norm_squared=(chi.T*chi)[0],head_linear_split=mp.norm(Ef-e*Echi-Eh),source_lambda_minus_Rayleigh=(mp.mpf(source_lambda)-Kf) if source_lambda is not None else None,source_A_symmetry=max(abs(A[i,j]-A[j,i]) for i in range(N+1) for j in range(N+1)))
 return dict(dps=dps,m=m,N=N,L=L,T=T,q=E.rows,rank=d.get('rank',E.rows),world=d.get('world','unspecified'),cutoff_mode=d.get('cutoff_mode',d.get('branch')),head_metric='2 diag(row_signs) on saved raw physical E; DH complex signed pairing retained',negative_head_rows=sum(x<0 for x in signs),raw=raw,scaled=scaled,checks=checks)

def run(path,label=None,low_dps=None):
 start=time.monotonic();path=Path(path);by=path.read_bytes();d=json.loads(by);source_dps=int(d.get('dps',120));low_dps=low_dps or max(source_dps+30,160);high_dps=low_dps+40
 a=evaluate(d,low_dps);b=evaluate(d,high_dps)
 differences={k:abs(a['raw'][k]-b['raw'][k]) for k in a['raw']}
 scaled_differences={k:abs(a['scaled'][k]-b['scaled'][k]) for k in a['scaled']} if a['scaled'] and b['scaled'] else None
 out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',operator_source='saved original full finite A, unchanged',method='finite source algebra minus finite signed low-zero head; no independently computed infinite zero tail',source_commit=SOURCE_COMMIT,source_blob=SOURCE_BLOB,input_file=path.name,input_sha256=hashlib.sha256(by).hexdigest(),input_dps=source_dps,new_matrix_builds=0,new_eigensystems=0,new_zero_searches=0,arithmetic_precision_check='same serialized source coordinates evaluated twice; does not improve source or zero-location accuracy',precision_comparison=dict(lower_dps=low_dps,higher_dps=high_dps,raw_absolute_differences=differences,scaled_absolute_differences=scaled_differences),result=b,seconds=time.monotonic()-start)
 label=label or path.stem
 destination=P/('energy_'+label+'.json');destination.write_text(json.dumps(serial(out,digits=high_dps),indent=2)+'\n');print(label,'C=',mp.nstr(b['raw']['finite_C_T'],14),'R=',mp.nstr(b['scaled']['R_total'],14) if b['scaled'] else 'UNDEFINED_e0','relative_closure=',mp.nstr(b['scaled']['R_identity_residual'],8) if b['scaled'] else 'unscaled','seconds',time.monotonic()-start,flush=True)
 return out

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('source');p.add_argument('--label');p.add_argument('--low-dps',type=int);a=p.parse_args();run(a.source,a.label,a.low_dps)
