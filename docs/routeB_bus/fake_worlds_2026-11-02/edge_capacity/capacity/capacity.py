"""EDGE_CAPACITY_v1 (ii)(iii), saved complement matrices only.

DIAGNOSTIC_NEVER_A_PROOF. The only new eigenproblem is the explicitly
requested compression to endpoint-zero vectors inside the saved J-perp.
This module uses input source matrices and bases. The shared high-cell
materializer rebuilds A/E/U/Q from pinned helpers; it does not rebuild a
full-carrier eigensystem.
"""
from pathlib import Path
import argparse,csv,hashlib,json,time,os
import mpmath as mp
import numpy as np

def fmt(x):return mp.nstr(x,max(45,mp.mp.dps-10))
def mat(x):return mp.matrix(x)
def scalar(x):return mp.mpf(x)
def column(x):
 v=mp.matrix(x)
 return v.T if v.rows==1 else v
def norm2(A):return mp.sqrt(mp.fsum(abs(x)**2 for x in A))
def trace(A):return mp.fsum(A[i,i] for i in range(min(A.rows,A.cols)))
def infer_mode(T,m):
 with mp.workdps(100):
  return 'native_kappa1p1' if abs(mp.mpf(T)/(2*mp.pi*m/mp.log(m))-mp.mpf('1.1'))<mp.mpf('1e-40') else 'matched'
def compute(path,dps):
 start=time.monotonic();mp.mp.dps=dps;d=json.loads(path.read_text());A=mat(d['A']);U=mat(d['U']);m=int(d['m']);L=mp.log(m);q=U.cols
 G=U.T*A*U;G=(G+G.T)/2
 db=mp.matrix([1/mp.sqrt(L)]+[mp.sqrt(2/L)]*m);t=U.T*db
 spectrum=list(map(mp.mpf,d.get('complement_eigenvalues',[])))
 spectrum_source='archived compressed spectrum'
 if len(spectrum)!=q:
  spectrum=list(mp.eigsy(G,eigvals_only=True));spectrum_source='new high-precision reduced G spectrum, no source eigensystem'
 spectrum.sort();computed_bottom=spectrum[0];lam=mp.mpf(d.get('complement_minimum',computed_bottom));second=spectrum[1] if q>1 else None
 # A double-precision compressed-spectrum replay checks the archived lambda2;
 # it never resolves or replaces a tiny bottom eigenvalue.
 gfloat=np.array([[float(G[i,j]) for j in range(q)] for i in range(q)])
 gfvalues=np.linalg.eigvalsh(gfloat);gfscale=max(1.,float(np.max(abs(gfvalues))))
 second_float=float(gfvalues[1]) if q>1 else None
 second_float_error=abs(second_float-float(second)) if second is not None else None
 second_float_resolved=second is not None and abs(float(second))>1000*np.finfo(float).eps*gfscale
 f=column(d['complement_f']);y=U.T*f;e=(db.T*f)[0];e_from_t=(t.T*y)[0];ray=(y.T*G*y)[0]/(y.T*y)[0]
 x=mp.lu_solve(G,t);den=(t.T*x)[0];cap=1/den
 solve_rel=norm2(G*x-t)/(norm2(G)*norm2(x)+norm2(t))
 ratio=lam/(e*e) if e else None
 T=scalar(d['T']);scale=mp.pi*T/mp.log(T)
 mode=d.get('cutoff_mode',d.get('mode',''))
 if not mode:mode=infer_mode(d['T'],m)
 # A stable Householder reflection: its columns1..q-1 span t-perp.
 tn=norm2(t);v=t.copy();v[0]+=tn if t[0]>=0 else -tn
 H=mp.eye(q)-2*(v*v.T)/(v.T*v)[0];Z=H[:,1:]
 restriction=Z.T*G*Z;restriction=(restriction+restriction.T)/2
 rr=list(mp.eigsy(restriction,eigvals_only=True)) if q>1 else []
 endpoint_zero_min=rr[0] if rr else None
 lam_e_res=norm2(G*y-lam*y)/max(norm2(G)*norm2(y),mp.mpf('1e-300'))
 negative=sum(a<0 for a in spectrum);positive=sum(a>0 for a in spectrum);zero=sum(a==0 for a in spectrum)
 world=d['world'];positive_saved=negative==0 and zero==0
 out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',source_file=str(path),source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),world=world,m=m,q=q,cutoff_mode=mode,T=fmt(T),working_dps=dps,source_dps=d.get('dps'),endpoint_normalization='physical f(b), b=log(m)/2; d_b=(1,sqrt(2),...)/sqrt(log m)',
  saved_lambda_min=fmt(lam),saved_lambda_second=fmt(second) if second is not None else None,saved_spectrum_negative=negative,saved_spectrum_positive=positive,saved_spectrum_zero=zero,saved_spectrum_min_absolute=fmt(min(abs(a) for a in spectrum)),
  compressed_spectrum_source=spectrum_source,compressed_spectrum=[fmt(a) for a in spectrum],computed_compressed_bottom=fmt(computed_bottom),compressed_bottom_relative_replay_error=fmt(abs(computed_bottom-lam)/max(abs(lam),mp.mpf('1e-300'))),
  second_lambda_float_replay=second_float,second_lambda_float_absolute_error=second_float_error,second_lambda_float_resolved=bool(second_float_resolved),second_lambda_float_match=bool(second is None or second_float_error<2e-10*gfscale),
  bottom_endpoint=fmt(e),bottom_endpoint_squared=fmt(e*e),endpoint_crosscheck_error=fmt(abs(e-e_from_t)),bottom_rayleigh=fmt(ray),saved_bottom_relative_eigen_residual=fmt(lam_e_res),
  inverse_quadratic_denominator=fmt(den),inverse_denominator_sign=int(mp.sign(den)),capacity_algebraic=fmt(cap),capacity_interpretation='numerically positive definite reduced G: finite constrained affine minimum' if positive_saved else 'algebraic inverse quadratic only; no positive-capacity/coercivity interpretation',
  capacity_scaled=fmt(cap*scale),lambda_over_endpoint_squared=fmt(ratio) if ratio is not None else None,R_scaled=fmt(ratio*scale) if ratio is not None else None,capacity_over_lambda_endpoint_ratio=fmt(cap/ratio) if ratio else None,
  endpoint_zero_minimum=fmt(endpoint_zero_min) if endpoint_zero_min is not None else None,endpoint_zero_second=fmt(rr[1]) if len(rr)>1 else None,endpoint_zero_negative_count=sum(a<0 for a in rr),
  restriction_trace_error=fmt(abs(mp.fsum(rr)-trace(restriction))) if rr else None,
  inverse_solve_relative_residual=fmt(solve_rel),endpoint_nullbasis_residual=fmt(norm2(t.T*Z)),endpoint_nullbasis_orthogonality=fmt(norm2(Z.T*Z-mp.eye(q-1))),
  U_orthogonality=fmt(norm2(U.T*U-mp.eye(q))),source_A_symmetry=fmt(norm2(A-A.T)),saved_compressed_spectrum_trace_error=fmt(abs(mp.fsum(spectrum)-trace(G))),
  interlacing_min_check=bool(endpoint_zero_min is None or lam-mp.mpf('1e-40')<=endpoint_zero_min<=second+mp.mpf('1e-40')),
  positive_capacity_bound_check=bool(not positive_saved or ratio is None or cap<=ratio+mp.mpf('1e-40')),
  seconds=time.monotonic()-start)
 return out

def main():
 p=argparse.ArgumentParser();p.add_argument('--manifest',type=Path,required=True);p.add_argument('--input-root',type=Path,help='Root for relative manifest paths; defaults to EDGE_CAPACITY_INPUT_ROOT or manifest directory');p.add_argument('--output',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--dps',type=int,default=80);p.add_argument('--validate',type=Path,help='one chosen worst-case source to rerun at dps+30');args=p.parse_args();args.output.mkdir(parents=True,exist_ok=True)
 manifest=json.loads(args.manifest.read_text());paths=manifest['cells'] if isinstance(manifest,dict) else manifest
 inputroot=args.input_root or Path(os.environ.get('EDGE_CAPACITY_INPUT_ROOT',str(args.manifest.resolve().parent)))
 paths=[Path(a['path'] if isinstance(a,dict) else a) for a in paths]
 paths=[a if a.is_absolute() else inputroot/a for a in paths]
 if args.validate and not args.validate.is_absolute():args.validate=inputroot/args.validate
 rows=[]
 for path in paths:
  resultpath=args.output/(path.stem+f'_capacity_dps{args.dps}.json')
  if resultpath.exists():
   r=json.loads(resultpath.read_text())
   if not r.get('cutoff_mode') or '_rebuild' in path.stem:
    r['cutoff_mode']=infer_mode(r['T'],r['m'])
    resultpath.write_text(json.dumps(r,indent=2)+'\n')
  else:r=compute(path,args.dps);resultpath.write_text(json.dumps(r,indent=2)+'\n')
  rows.append(r);print(path.name,r['capacity_scaled'],r['endpoint_zero_minimum'],flush=True)
 validation=[]
 if args.validate:
  low=next(r for r in rows if Path(r['source_file']).resolve()==args.validate.resolve());high=compute(args.validate,args.dps+30)
  (args.output/(args.validate.stem+f'_capacity_dps{args.dps+30}.json')).write_text(json.dumps(high,indent=2)+'\n')
  for key in ['capacity_algebraic','capacity_scaled','lambda_over_endpoint_squared','R_scaled','endpoint_zero_minimum']:
   a=mp.mpf(low[key]);b=mp.mpf(high[key]);err=abs(a-b)/max(abs(b),mp.mpf('1e-300'));validation.append(dict(field=key,low_dps=args.dps,high_dps=args.dps+30,relative_difference=fmt(err),pass_relative_1e_40=bool(err<mp.mpf('1e-40'))))
  (args.output/'precision_validation.json').write_text(json.dumps(dict(source=str(args.validate),comparisons=validation),indent=2)+'\n')
 (args.output/'capacity.json').write_text(json.dumps(rows,indent=2)+'\n')
 with (args.output/'capacity.csv').open('w',newline='') as f:
  fields=list(dict.fromkeys(k for row in rows for k in row))
  w=csv.DictWriter(f,fieldnames=fields);w.writeheader();w.writerows(rows)
if __name__=='__main__':main()
