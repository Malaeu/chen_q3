"""Summarize saved finite margin diagnostics, no fresh source evaluations."""
from pathlib import Path
import csv,json
P=Path(__file__).resolve().parent
read=lambda n:list(csv.DictReader((P/n).open()))
a=read('future_refinement.csv');b=read('extended_refinement.csv');c=read('nested_step_search.csv');s=read('single_endpoint.csv')
rows=[];viol=[]
for mesh in [32,64,128,256]:
 z=sorted([r for r in a+b if r['world']=='zeta' and int(r['mesh'])==mesh and float(r['a'])==6],key=lambda r:int(r['q']))
 rows.append(dict(mesh=mesh,**{f'q{r["q"]}':float(r['mu']) for r in z}))
for world in ['zeta','dh','plant']:
 for mesh in [32,64,128,256]:
  for t in sorted(set(r['a'] for r in a if r['world']==world and int(r['mesh'])==mesh)):
   z=sorted([r for r in a if r['world']==world and int(r['mesh'])==mesh and r['a']==t and r['mu']],key=lambda r:int(r['q']))
   for r,v in zip(z,z[1:]):
    if float(v['mu'])>float(r['mu'])+1e-8:viol.append(dict(world=world,mesh=mesh,a=t,q0=r['q'],q1=v['q'],mu0=r['mu'],mu1=v['mu']))
validation=json.loads((P/'mp_validation.json').read_text())
summary=dict(status='DIAGNOSTIC_NEVER_A_PROOF',uniform_single_rows=len(s),block_rows=len(a),extra_refinement_rows=len(b),a6_refinement=rows,finite_future_nesting_violations=viol,factorization_unresolved=sum(r['status']=='FACTORIZATION_UNRESOLVED' for r in a),invalid_past_rows=sum(r['status']=='INVALID_PAST' for r in a),all_sampled_nested_zeta_positive=all(float(r['mu'])>0 for r in c),minimum_nested_zeta_margin=min(float(r['mu']) for r in c),q32_to128_largest_change=max(abs(r['q32']-r['q128']) for r in rows),maximum_MP_margin_absolute_error=max(float(r['absolute_error']) for r in validation))
(P/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
