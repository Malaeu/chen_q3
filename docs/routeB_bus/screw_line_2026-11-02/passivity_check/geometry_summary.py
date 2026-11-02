"""Compare true-kernel discretizations and section labels without causal overclaim."""
from pathlib import Path
import json,math,csv
import mpmath as mp
import numpy as np
from curve import labelled_coefficients as coefficients
P=Path(__file__).resolve().parent;mp.mp.dps=100
files=['curve_zeta.json','curve_dh.json','curve_refined_dh.json','aligned_zeta.json','aligned_dh.json','aligned_mesh_zeta.json','aligned_mesh_dh.json']
summary=[];events=[];bd=coefficients(300,'dh');bz=coefficients(300,'zeta')
for name in files:
 d=json.loads((P/name).read_text());rows=d.get('prefixes',d.get('rows'))
 # Avoid treating differing field layouts as the same precision experiment.
 neg=[r for r in rows if mp.mpf(str(r['Schur_pivot']))<0];decrease=[r for r in rows if mp.mpf(str(r['increment']))<0]
 assert len(decrease)<=len(neg)
 if d['world']=='zeta':assert not neg and not decrease
 summary.append({'file':name,'world':d['world'],'precision':d.get('dps','float64'),'nodes':len(rows),'negative_innovations':len(neg),'energy_decreases':len(decrease),'first_negative':neg[0] if neg else None,'final_negative_inertia':rows[-1]['negative_inertia']})
 if d['world']=='dh':
  for r in neg:
   L=mp.mpf(str(r['L']));integer_node=int(r.get('m',0))
   if integer_node:
    left=integer_node-1;right=integer_node;label='integer_endpoint'
   else:left=int(mp.floor(mp.exp(L)));right=left+1;label='fixed_mesh_node'
   events.append({'file':name,'L':mp.nstr(L,80),'exp_L':mp.nstr(mp.exp(L),60),'section_start':left,'section_end':right,'node_kind':label,'Schur_pivot':r['Schur_pivot'],'energy_increment':r['increment'],'b_section_start':mp.nstr(bd[left],90),'b_section_end':mp.nstr(bd[right],90),'start_prime_power':bool(bz[left]),'end_prime_power':bool(bz[right]),'scope':'OBSERVED_SECTION_LABEL; NOT_CAUSAL_ATTRIBUTION_TO_ONE_ATOM'})
# Quantify float negative-witness margin against observed source refinement.
d=json.loads((P/'aligned_mesh_dh.json').read_text());n=d['first_negative_innovation']['prefix_dimension'];G=np.load(P/'runtime_cache'/'aligned_mesh_dh_local.npz')['G'];ev=np.linalg.eigvalsh(G[:n,:n])[0]
margin={'prefix':n,'negative_min_eigenvalue_float':float(ev),'observed_source_quad_difference':d['max_source_quadrature_difference'],'heuristic_margin_over_4n_observed_difference':float(abs(ev)/(4*n*d['max_source_quadrature_difference'])),'scope':'OBSERVED_REFINEMENT_MARGIN_NOT_AN_INTERVAL_ERROR_BOUND'}
with (P/'DH_GEOMETRY_EVENTS.csv').open('w',newline='') as f:w=csv.DictWriter(f,fieldnames=events[0]);w.writeheader();w.writerows(events)
(P/'GEOMETRY_SUMMARY.json').write_text(json.dumps({'status':'DIAGNOSTIC_NEVER_A_PROOF','grids':summary,'DH_float_first_negative_margin':margin,'sparse_DH_endpoints_false_negative_control':not any(x['negative_innovations'] for x in summary if x['file']=='aligned_dh.json'),'first_sampled_index_not_intrinsic':True,'source_passive_section_proof':False},indent=2)+'\n')
print(json.dumps({'summaries':summary,'float_margin':margin},indent=2))
