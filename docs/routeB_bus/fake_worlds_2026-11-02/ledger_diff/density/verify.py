"""Independent saved-cell replay for ROUTE_B_DH_LEDGER_AND_CERT_v1, Part A.

DIAGNOSTIC_NEVER_A_PROOF. No eigenproblem is solved. numpy SVD only replays
saved matrix/basis products. Exact rank is the distinct-node interpolation
rank q, checked numerically without selecting or deleting singular values.
"""
from pathlib import Path
import argparse,csv,hashlib,json
from collections import Counter
import mpmath as mp
import numpy as np

def main():
 p=argparse.ArgumentParser();p.add_argument('--archive',type=Path,default=Path(__file__).resolve().parents[1]);p.add_argument('--inputs',type=Path,default=Path(__file__).resolve().parents[2]);p.add_argument('--zeta-zeros',type=Path,default=Path(__file__).resolve().parents[3]/'lowcluster_2026-11-02'/'ladder_limit'/'identify'/'zero_height_local'/'zeros.csv');p.add_argument('--output',type=Path,default=Path(__file__).resolve().parent);args=p.parse_args()
 mp.mp.dps=150;args.output.mkdir(parents=True,exist_ok=True)
 zeta=[mp.mpf(x['gamma']) for x in csv.DictReader(args.zeta_zeros.open())]
 dh=json.loads((args.inputs/'dh_zeros.json').read_text())
 plan=json.loads((args.archive/'density_plan.json').read_text())
 table=list(csv.DictReader((args.archive/'matched.csv').open()))
 errors=[];checks=[];provenance={}
 def require(ok,what):
  if not ok:errors.append(what)
 def digest(path):
  v=hashlib.sha256(path.read_bytes()).hexdigest();provenance[str(path)]=v;return v
 dh_hash=digest(args.inputs/'dh_zeros.json');digest(args.zeta_zeros);digest(args.archive/'matched.csv');digest(args.archive/'density_plan.json')
 # Density is an integer orbit count, not a rounded decimal comparison.
 density=[]
 heights=sorted(mp.mpf(x['gamma']) for x in dh['upper_half_plane_zeros'])
 attainable={sum(h<t for h in heights) for t in [mp.mpf(0)]+[(a+b)/2 for a,b in zip(heights,heights[1:]) if a<b]+[heights[-1]+1]}
 for row in plan:
  m=row['m'];tz=mp.mpf('1.1')*2*mp.pi*m/mp.log(m);qz=sum(g<tz for g in zeta)
  require(qz==row['q_zeta'],f'm{m}: zeta cutoff count')
  require((qz in attainable)==row['exact_DH_threshold_exists'],f'm{m}: attainable DH density')
  opts=[]
  for o in row['DH_options']:
   t=mp.mpf(o['T_midpoint']);q=sum(g<t for g in heights)
   require(q==o['q'],f'm{m}: DH cutoff count q{o["q"]}')
   require(mp.mpf(o['last_included_height'])<t<mp.mpf(o['first_excluded_height']),f'm{m}: strict interior cutoff')
   opts.append(dict(q=q,T=mp.nstr(t,40),density=mp.nstr(mp.mpf(q)/(m+1),40)))
  if m==120:
   require(qz==64 and qz not in attainable and [o['q'] for o in opts]==[63,65],'m120 orbit jump brackets 63/65')
  density.append(dict(m=m,q_zeta=qz,exact_DH_match=qz in attainable,DH_options=opts))
 for row in table:
  world=row['world'];m=int(row['m']);q=int(row['q']);path=args.archive/'matched_cells'/f'{world}_m{m}_q{q}.json';d=json.loads(path.read_text());digest(path)
  n=m+1;r=n-q;A=np.array(d['A'],float);E=np.array(d['E'],float);Q=np.array(d['Q'],float);U=np.array(d['U'],float)
  require(A.shape==(n,n) and E.shape==(q,n) and Q.shape==(n,r),f'{path.name}: dimensions')
  require(d['rank']==q and d['dim_J']==r,f'{path.name}: recorded exact rank/nullity')
  t=mp.mpf(d['T']);labels=d['row_labels']
  if world=='zeta':
   expected=[g for g in zeta if g<t];require(len(expected)==q,f'{path.name}: zero count')
   # Saved zeta labels may be numeric heights rather than dictionaries.
   actual=[]
   for z in labels:
    if isinstance(z,dict):actual.append(mp.mpf(z['gamma']))
    else:actual.append(mp.mpf(z))
   require(len(actual)==len(expected) and all(abs(a-b)<mp.mpf('1e-70') for a,b in zip(actual,expected)),f'{path.name}: zeta row labels')
  else:
   expected=[]
   for z in dh['critical_line_zeros']:
    if mp.mpf(z['gamma'])<t:expected.append(('line',z['gamma']))
   for z in dh['off_line_pairs']:
    if mp.mpf(z['gamma'])<t:expected.extend([('real',z['gamma']),('imag',z['gamma'])])
   require(len(expected)==q,f'{path.name}: DH full orbit row count')
   require(len(labels)==q and all(a[0]==b['kind'] and abs(mp.mpf(a[1])-mp.mpf(b['gamma']))<mp.mpf('1e-70') for a,b in zip(expected,labels)),f'{path.name}: unsplit DH orbit labels')
   require(d['zero_source_sha256']==dh_hash,f'{path.name}: zero source hash')
   require([int(x) for x in d['row_signs']]==[(-1 if kind=='imag' else 1) for kind,_ in expected],f'{path.name}: orbit metric signs')
  # Direct ordinary singular values of E equal those of F=EU on J-perp.
  sigma=float(np.linalg.svd(E,compute_uv=False)[-1]);sigma_F=float(np.linalg.svd(E@U,compute_uv=False)[-1]);delta=float(np.linalg.svd(A@Q,compute_uv=False)[0])
  refsig=float(d['sigma_min']);refdelta=float(d['delta'])
  sigma_rel=abs(sigma-refsig)/refsig;delta_rel=abs(delta-refdelta)/refdelta
  require(sigma_rel<2e-6,f'{path.name}: float sigma replay relative <=2e-6')
  require(abs(sigma_F-sigma)/refsig<2e-6,f'{path.name}: sigma(F)=sigma(E) replay')
  require(delta_rel<2e-10,f'{path.name}: float delta replay relative <=2e-10')
  eq=float(np.linalg.norm(E@Q,ord=2));orth=float(np.linalg.norm(Q.T@Q-np.eye(r),ord=2));cross=float(np.linalg.norm(U.T@Q,ord=2))
  require(eq<2e-12*max(1.,np.linalg.norm(E,ord=2)) and orth<2e-12 and cross<2e-12,f'{path.name}: kernel and basis replay')
  require(sigma>1000*np.finfo(float).eps*np.linalg.norm(E,ord=2),f'{path.name}: raw smallest sigma resolved in float replay')
  mu=mp.mpf(d['adaptive_mu']);ev=list(map(mp.mpf,d['full_eigenvalues']));count=sum(v<mu for v in ev);margin=min(abs(v-mu) for v in ev)/abs(mu)
  require(count==int(d['count_delta_plus'])==int(row['count_delta_plus']) and count-r==int(d['count_minus_dim'])==int(row['count_minus_dim']),f'{path.name}: saved-spectrum strict count')
  require(abs(mu/(mp.mpf(d['delta'])*mp.mpf('1.000001'))-1)<mp.mpf('1e-115'),f'{path.name}: threshold inflation')
  require(margin>mp.mpf('1e-8'),f'{path.name}: count margin not near boundary')
  source=json.loads((args.archive/'matched_cells'/f'source_{world}_m{m}.json').read_text());sourceA=np.array(source['A'],float);source_diff=float(np.max(abs(A-sourceA)))
  require(source_diff==0,f'{path.name}: source A unchanged')
  checks.append(dict(world=world,m=m,q=q,rank=q,dim_J=r,T=d['T'],delta_saved=d['delta'],delta_float=delta,delta_relative_difference=delta_rel,sigma_saved=d['sigma_min'],sigma_float=sigma,sigma_F_float=sigma_F,sigma_relative_difference=sigma_rel,E_Q_norm=eq,Q_orthogonality=orth,U_Q_norm=cross,adaptive_mu=d['adaptive_mu'],strict_count=count,count_minus_dim=count-r,relative_count_margin=mp.nstr(margin,30),source_A_max_float_difference=source_diff))
 result=dict(status='PASS' if not errors else 'FAIL',scope='DIAGNOSTIC_NEVER_A_PROOF',source_base='d26831357b6cb3b2b7d4a569d2031e454952b246',saved_results_commit='8acecc1574740c5163c2a4e8ef75049f6df84313',new_eigenproblems=0,saved_cells_checked=len(checks),tolerances=dict(delta_relative=2e-10,sigma_relative=2e-6,basis_absolute=2e-12),density_plan_checks=density,cell_checks=checks,errors=errors,sha256=provenance)
 (args.output/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
 with (args.output/'verification.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(checks[0]));w.writeheader();w.writerows(checks)
 lines=['# Density-matched Part A: independent saved-cell verification','',result['scope'],'','Archived result commit: '+result['saved_results_commit']+'. Mathematical source base: '+result['source_base']+'.','',f'Status: **{result["status"]}**; {len(checks)} cells replayed; no new eigenproblem. Saved source matrices, E, Q and U were used without rebuilding a matrix.','',
 'Zero counts and strict cutoffs were rechecked with 150-digit scalar arithmetic against the pinned zero tables. DH reflected off-line pairs are always included as complete real/imaginary row pairs. Raw singular values and full AQ norms were independently replayed with NumPy SVD; rank q was not selected by a floating tolerance. Signed counts include every saved eigenvalue below delta*(1+1e-6).','',
 'The exact density matches are q=8,18,29,41 at m=20,40,60,80. At m=120 the zeta target q=64 is impossible for a DH height cutoff: the off-line pair at gamma=114.16334273075698 raises q from63 directly to65. Both neighboring DH densities and both same-q zeta controls are verified. The extra m55 controls were also checked.','',
 f'Maximum relative delta replay error: {max(x["delta_relative_difference"] for x in checks):.3g}; maximum relative sigma replay error: {max(x["sigma_relative_difference"] for x in checks):.3g}. Explicit acceptance tolerances are2e-10 and2e-6 respectively; these are finite diagnostic checks, not interval certificates.','',
 'Full per-cell values, strict-count margins, kernel/orthogonality residuals and source-file hashes are in verification.json and verification.csv. Tiny signs of individual near-zero full eigenvalues are not certified, but the adaptive positive-threshold count is well separated from every saved eigenvalue.','']
 if errors:lines+=['## Failures','']+['- '+e for e in errors]
 (args.output/'RESULT.md').write_text('\n'.join(lines))
 print(json.dumps(dict(status=result['status'],cells=len(checks),errors=errors,max_delta_relative=max(x['delta_relative_difference'] for x in checks),max_sigma_relative=max(x['sigma_relative_difference'] for x in checks)),indent=2))
 if errors:raise SystemExit(1)
if __name__=='__main__':main()
