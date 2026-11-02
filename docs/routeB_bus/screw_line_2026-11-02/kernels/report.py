"""Aggregate all integer-cell formal kernels without a geometric upgrade."""
from pathlib import Path
import csv,json,argparse
import mpmath as mp

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent);a=ap.parse_args();P=a.directory;mp.mp.dps=160
 cells=[];packed={}
 if (P/'cells.jsonl').exists():
  for line in (P/'cells.jsonl').read_text().splitlines():
   c=json.loads(line);packed[c['world'],c['m']]=c
 for m in range(20,241):
  for world in ['zeta','dh']:
   p=P/f'{world}_m{m}_bits1024.json'
   if p.exists():cells.append(json.loads(p.read_text()))
   elif (world,m) in packed:cells.append(packed[world,m])
   else:raise FileNotFoundError(p)
 rows=[];ir=[]
 for c in cells:
  neg=c['inertia']['negative'];pos=c['inertia']['positive']
  for r in c['rows']:rows.append({**r,'form_negative_count':neg,'form_positive_count':pos})
  ir.append(dict(world=c['world'],m=c['m'],q=c['q'],dim_J=c['dim_J'],T=c['T'],negative=neg,positive=pos,minimum_absolute_LDL_pivot=c['inertia']['minimum_absolute_pivot'],K_endpoint=c['rows'][0]['K'],K_endpoint_sign=c['rows'][0]['K_sign'],B_symmetry_relative=c['B_symmetry_relative'],kernel_symmetry_relative=c['kernel_symmetry_relative'],seconds=c['seconds']))
 for name,data in [('kernels.csv',rows),('inertia.csv',ir)]:
  with (P/name).open('w',newline='') as f:
   w=csv.DictWriter(f,fieldnames=list(data[0]));w.writeheader();w.writerows(data)
 first={world:next((r['m'] for r in ir if r['world']==world and r['negative']>0),None) for world in ['zeta','dh']}
 stats=[]
 for world in ['zeta','dh']:
  for gauge in ['endpoint','physical','fourier']:
   for eta in (['0'] if gauge=='endpoint' else ['0.5','1','2']):
    rr=[r for r in rows if r['world']==world and r['gauge']==gauge and r['eta']==eta];negative=[r['m'] for r in rr if r['K_sign']<0]
    stats.append(dict(world=world,gauge=gauge,eta=eta,cells=len(rr),negative_K_count=len(negative),negative_K_m=negative,first_negative_K=negative[0] if negative else None,zero_K_count=sum(r['K_sign']==0 for r in rr),negative_r_proxy_squared_count=sum(r['r_proxy_squared_sign']!='' and int(r['r_proxy_squared_sign'])<0 for r in rr)))
 validation=json.loads((P/'validation.json').read_text()) if (P/'validation.json').exists() else {}
 maxres=max(mp.mpf(r['solve_backward_relative_residual']) for r in rows);maxksym=max(mp.mpf(c['kernel_symmetry_relative']) for c in cells)
 result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',requested_m=[20,240],integers_per_world=221,worlds=['zeta','dh'],cells=len(cells),endpoint_rows=442,nonreal_point_rows=2652,all_kernel_rows=len(rows),source_full_eigenproblems=0,new_radius_definition='formal inverse proxy only; no Weyl-circle normalization identified',first_complement_indefinite=first,S1_probability=.6,S1_first_DH_complement_in_50_56=first['dh'] is not None and 50<=first['dh']<=56,scalar_sign_stats=stats,max_solve_backward_relative_residual=mp.nstr(maxres,70),max_kernel_symmetry_relative=mp.nstr(maxksym,70),source_validation_flags={k:v for k,v in validation.items() if k.startswith('pass_')})
 (P/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
 lines=['# SCREW_LINE: formal inverse kernels on every integer cell','', '**DIAGNOSTIC_NEVER_A_PROOF.** Literal N=m,L=log(m),native kappa1.1; both zeta and Davenport–Heilbronn. All221integers m20..240 are present in each world. No full-carrier spectrum was recomputed.','',
 '## What was actually evaluated','',
 'Let E be the unweighted physical Fourier sampling matrix at the complete numerical positive-height census below T. DH reflected off-line pairs use isometric sqrt(2) real/imaginary rows. For B=E A E^T and evaluation vector e_z, the saved scalar is K_z=(E e_z)^T B^(-1)(E e_z). This is congruent to U(U^T A U)^(-1)U^T on the finite complement when E has full row rank. It is an inverse-form proxy, not an identified Weyl or de Branges kernel.','',
 'Two distinct evaluation conventions are retained: formal analytic continuation of the physical cosine factor phi_n(i eta), and entire Fourier evaluation phi_hat_n(i eta), eta=1/2,1,2. The window indicator itself has no analytic continuation; the physical-cosine alternative does not assert that the zero-extended carrier functions are entire. Neither is silently chosen as the Suzuki source map. The real endpoint is f(log(m)/2), with d_b=(1,sqrt(2),...)/sqrt(log m). Mixed endpoint kernels d_b^T E^T B^(-1)E e_z are saved for the atom-jump checks.','',
 'At these purely imaginary points the evaluation columns are real. We report r_proxy=1/(eta*K_z) literally, without an absolute-value repair. Its square cannot become negative: a negative square is not a possible diagnostic of DH indefiniteness. Negative K and signed inverse proxies are instead distinguished from the independently computed form inertia.','',
 '## Complement inertia and scalar signs','',f'First negative complement inertia: zeta={first["zeta"]}; DH={first["dh"]}. Registered S1 (DH first indefinite in50..56): '+('PASS.' if result['S1_first_DH_complement_in_50_56'] else 'FAIL.'),'',
 'The known original full-carrier DH onset m51 is a separate saved-source fact. The native complement is still positive at51; it becomes indefinite at52, returns positive at53, and becomes indefinite again at54. Moving integer carriers and moving zero constraints are not a nested fixed-kernel family.','',
 '|world|evaluation|eta|negative K cells|first negative K|negative r_proxy² cells|','|---|---|---:|---:|---:|---:|']
 for s in stats:lines.append('|'+ '|'.join(map(str,[s['world'],s['gauge'],s['eta'],s['negative_K_count'],s['first_negative_K'],s['negative_r_proxy_squared_count']]))+'|')
 lines+=['','|m|DH q|negative form levels|endpoint K sign|','|---:|---:|---:|---:|']
 for r in ir:
  if r['world']=='dh' and 48<=r['m']<=56:lines.append(f'|{r["m"]}|{r["q"]}|{r["negative"]}|{r["K_endpoint_sign"]}|')
 lines+=['','## Numerical controls and reproduction','',
 'The original source arithmetic coefficients, conductor/gamma shift, poles, endpoints and all integer DH atoms are retained. Arch integrals are evaluated by equivalent digamma/trigamma moments plus a finite geometric tail. An explicit entrywise bound for that omitted arch series is saved per cell. This bound does not cover rounding, zero-census errors, or certify the mathematical source operator.','',
 'Compiled Arb midpoint matrices use1024bits. Solves use the approximate compiled LU routine, not a certified interval inverse. Symmetric LDL pivots give a separate numerical inertia without an eigenvalue or singular-value tolerance cutoff. Whole-cell inverse failure or unresolved pivots would block a row rather than be converted to a positive kernel. All requested cells completed.','',
 f'Maximum per-right-hand-side normalized solve backward residual: {mp.nstr(maxres,8)}. Maximum relative mixed-kernel symmetry defect: {mp.nstr(maxksym,8)}. Source A and saved-vector energy comparisons at55,120,240; QR-vs-congruence endpoint inverse checks;1536bit repetitions at55,120,240 and DH51..54 are recorded in validation.json.','',
 '`kernels.csv` contains all3094endpoint/point rows, keeping arbitrary-range decimal strings (no float underflow). `inertia.csv` contains all442form counts and source/cutoff information. Per-cell JSON records retain all metadata and tail bounds; the parent package archives and restores these losslessly. `RESULT.json` preserves the complete negative-K integer lists and S1 score. The transition audit separately distinguishes discrete integer changes from fixed-N atom-derivative jumps.','',
 'Replay with python-flint and mpmath installed: `python3 screw_kernels.py --input-root INPUT_ROOT --bits 1024`. INPUT_ROOT contains the pinned zeta_zeros_capacity.csv and edge_law/dh/dh_zeros_extended.json. Then run `validate.py` with explicit input/EDGE paths and `report.py`. No actual Weyl-radius conclusion or RH/route-state export is made.','']
 (P/'RESULT.md').write_text('\n'.join(lines));print(json.dumps({k:v for k,v in result.items() if k not in ['scalar_sign_stats']},indent=2))
if __name__=='__main__':main()
