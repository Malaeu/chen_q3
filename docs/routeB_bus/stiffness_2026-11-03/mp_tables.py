from pathlib import Path
import json,csv
P=Path(__file__).resolve().parent

def write(name,rows):
 keys=list(dict.fromkeys(k for x in rows for k in x))
 with(P/name).open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(rows)
prices=[];sv=[];gates=[];exits=[];gaps=[]
for m in[16,24,40]:
 d=json.loads((P/f'mp_prices_m{m}.json').read_text());f=d['literal_face'];ball=f['P3_ball'];gates.append(dict(m=m,max_entry=d['P1_conservation_max_entry'],source_gate=d['P1_gate_pass'],source_tolerance=d['P1_conservation_gate'],face_size=d['selected_face_size'],face_relative=f['compression_relative'],face_gate=f['gate_pass'],ones_image=f['ones_image_max_entry'],ones_relative=f['P2_ones_approximate_kernel_ratio']))
 for x in f['P3_optimizer_labeled']:prices.append(dict(m=m,**x,scalar_optimum=ball['scalar_analytic_ball_optimum'],annihilating_dual_valid=ball['dual_Y_valid_as_annihilating_stress'],dual_price_residual=ball['dual_stress_price_residual_norm']))
 for kind in['P2_full_map','P2_budget_gauge_map']:
  v=f[kind]
  for i,s in enumerate(v['singular_values']):sv.append(dict(m=m,map=kind,index=i,singular_value=s,threshold=v['threshold'],kernel_dimension=v['kernel_dimension']))
 for x in d['P1_inherited_coupling_exit_carrier_overlaps']:exits.append(dict(m=m,**x))
 for x in d['gap_candidates']:gaps.append(dict(m=m,**x))
write('P1_MP_GATES.csv',gates);write('P2_MP_SINGULAR_VALUES.csv',sv);write('SHADOW_PRICES_MP.csv',prices);write('FACE_EXIT_OVERLAPS_MP.csv',exits);write('FACE_GAPS_MP.csv',gaps)
print('MP per-part price,gate,spectrum andexit tables complete')
