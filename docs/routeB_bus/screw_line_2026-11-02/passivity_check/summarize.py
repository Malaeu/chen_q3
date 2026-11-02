"""Aggregate all requested inverse forms, birth kinks, and raw transitions."""
from pathlib import Path
import mpmath as mp
import json,csv,gzip,hashlib,tarfile
from curve import labelled_coefficients as coefficients
P=Path(__file__).resolve().parent;mp.mp.dps=140
base=[json.loads(f.read_text()) for f in sorted((P/'native_cells').glob('*_dps220_gl256.json'))]
assert len(base)==442,len(base);base.sort(key=lambda d:(d['world']!='zeta',d['m']))
assert all(d.get('negative_pivots') is not None for d in base)
by={(d['world'],d['m']):d for d in base};rows=[];kinks=[];steps=[];tags=['endpoint','i_half','i','two_i']
for d in base:
 row={k:d[k] for k in ['world','m','q','T','negative_pivots','positive_pivots']}
 row.update({f'K_{tag}':v for tag,v in zip(tags,d['K'])})
 row.update({f'rho_{tag}_NOT_WEYL_RADIUS':v for tag,v in zip(tags[1:],d['signed_reciprocal_proxy'])})
 row.update({f'rho_squared_{tag}':v for tag,v in zip(tags[1:],d['reciprocal_proxy_squared'])})
 row['source_dps']=d['source_dps'];row['source_order']=d['source_order'];row['relative_solve_residual']=d['relative_solve_residual'];row['minimum_pivot_over_scale']=d['min_pivot_over_C_scale']
 rows.append(row)
 kinks.append({'world':d['world'],'n':d['m'],'b_n':d['b_m'],'source_derivative_kink_coefficient':d['birth_source_coefficient'],**{f'inverse_derivative_kink_{tag}':v for tag,v in zip(tags,d['birth_inverse_kernel_derivative_kinks'])},'scope':'FIXED_ORDER_LOCAL_BIRTH_KINK; NOT_RAW_CONSECUTIVE_DIFFERENCE'})
for world in ['zeta','dh']:
 for m in range(20,240):
  a,b=by[world,m],by[world,m+1]
  steps.append({'world':world,'m_from':m,'m_to':m+1,'q_from':a['q'],'q_to':b['q'],'rank_change':b['q']-a['q'],
                'atom_at_section_start':a['b_m'],'atom_at_section_end':b['b_m'],
                'start_is_zeta_prime_power':bool(coefficients(240,'zeta')[m]),
                'end_is_zeta_prime_power':bool(coefficients(240,'zeta')[m+1]),
                **{f'delta_K_{tag}':mp.nstr(mp.mpf(v)-mp.mpf(u),100) for tag,u,v in zip(tags,a['K'],b['K'])},
                **{f'delta_rho_{tag}':mp.nstr(mp.mpf(v)-mp.mpf(u),100) for tag,u,v in zip(tags[1:],a['signed_reciprocal_proxy'],b['signed_reciprocal_proxy'])},
                'scope':'NONNESTED_CHANGE_OF_CARRIER_WINDOW_CONSTRAINTS; NO_PURE_ATOM_ATTRIBUTION'})
for name,data in [('native_kernels.csv',rows),('birth_kinks.csv',kinks),('raw_steps.csv',steps)]:
 with (P/name).open('w',newline='') as f:w=csv.DictWriter(f,fieldnames=data[0]);w.writeheader();w.writerows(data)
atoms=[]
for world in ['zeta','dh']:
 coeff=coefficients(240,world);lam=coefficients(240,'zeta')
 for n in range(2,241):
  b=coeff[n];atoms.append({'world':world,'n':n,'is_ordinary_prime_power':bool(lam[n]),'b_n':mp.nstr(b,120),'b_over_sqrt_n':mp.nstr(b/mp.sqrt(n),120),'source_kink_rank_one_coefficient':mp.nstr(-2*b/mp.sqrt(n),120),'sign':int(mp.sign(b))})
with (P/'arithmetic_atoms.csv').open('w',newline='') as f:w=csv.DictWriter(f,fieldnames=atoms[0]);w.writeheader();w.writerows(atoms)
refinements=[]
for f in sorted((P/'native_cells').glob('*_dps300_gl320.json')):
 d=json.loads(f.read_text());b=by[d['world'],d['m']];refinements.append({'world':d['world'],'m':d['m'],'inertia_agrees':d['negative_pivots']==b['negative_pivots'],'relative_K_errors':[mp.nstr(abs(mp.mpf(x)-mp.mpf(y))/max(abs(mp.mpf(x)),1),110) for x,y in zip(d['K'],b['K'])]})
assert len(refinements)==14
stress=[]
for f in sorted((P/'native_cells').glob('dh*_node*.json')):
 d=json.loads(f.read_text());b=by[d['world'],d['m']];stress.append({'m':d['m'],'perturbation':d['node_perturbation'],'inertia_agrees':d['negative_pivots']==b['negative_pivots'],'max_relative_K_error':mp.nstr(max(abs(mp.mpf(x)-mp.mpf(y))/max(abs(mp.mpf(y)),1) for x,y in zip(d['K'],b['K'])),110)})
assert len(stress)==4
assert all(d['inertia_agrees'] for d in refinements+stress)
assert max(mp.mpf(v) for d in refinements for v in d['relative_K_errors'])<mp.mpf('1e-70')
assert max(mp.mpf(d['max_relative_K_error']) for d in stress)<mp.mpf('1e-60')
assert all(mp.mpf(v)>=0 for d in base for v in d['reciprocal_proxy_squared'])
counts={}
for endpoint in ['start','end']:
 counts[endpoint]={}
 for tag in tags:
  r=[mp.sign(mp.mpf(d[f'delta_K_{tag}'])) for d in steps if d['world']=='zeta' and d[f'{endpoint}_is_zeta_prime_power']]
  counts[endpoint][tag]={'positive':sum(x>0 for x in r),'negative':sum(x<0 for x in r),'zero':sum(x==0 for x in r)}
negative_dh=[d for d in base if d['world']=='dh' and d['negative_pivots']>0]
negative_diag=[{'world':d['world'],'m':d['m'],'query':tag} for d in base for tag,v in zip(tags,d['K']) if mp.mpf(v)<0]
summary={'status':'DIAGNOSTIC_NEVER_A_PROOF','native_cells':442,'integer_range':[20,240],'query_convention':base[0]['query_convention'],
 'all_zeta_C_positive_at_reported_precision':all(d['negative_pivots']==0 for d in base if d['world']=='zeta'),
 'first_native_DH_negative':{k:negative_dh[0][k] for k in ['m','q','negative_pivots','K']},
 'DH_native_m53_positive_after_m52_negative':by['dh',53]['negative_pivots']==0,
 'negative_inverse_diagonals':negative_diag,'negative_reciprocal_squares':0,
 'owner_onset_prediction_50_to56_pass':50<=negative_dh[0]['m']<=56,
 'raw_zeta_prime_power_delta_K_signs':counts,
 'local_zeta_prime_power_inverse_kinks_all_nonnegative':all(mp.mpf(v)>=0 for d in base if d['world']=='zeta' for v in d['birth_inverse_kernel_derivative_kinks']),
 'max_relative_solve_residual':mp.nstr(max(mp.mpf(d['relative_solve_residual']) for d in base),110),
 'max_U_orthogonality_error':mp.nstr(max(mp.mpf(d['U_orthogonality_max']) for d in base),110),
 'min_pivot_over_C_scale':mp.nstr(min(mp.mpf(d['min_pivot_over_C_scale']) for d in base),110),
 'precision_controls':refinements,'DH_coordinate_stress_controls':stress,
 'interval_certification':False,'Weyl_radius_identification':False,'passive_section_lemma_proved':False}
(P/'NATIVE_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
# Lossless numeric evidence, with a separately auditable per-cell manifest.
rawfiles=sorted((P/'native_cells').glob('*.json'));manifest=[];lines=[]
for f in rawfiles:
 b=f.read_bytes();manifest.append({'name':f.name,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()});lines.append(json.dumps({'name':f.name,'content':b.decode('utf-8')},separators=(',',':'))+'\n')
payload=''.join(lines).encode();compressed=gzip.compress(payload,compresslevel=9,mtime=0);(P/'native_cells.jsonl.gz').write_bytes(compressed)
parts=[]
for i,start in enumerate(range(0,len(compressed),262144)):
 name=f'native_cells.jsonl.gz.part{i:02d}';data=compressed[start:start+262144];(P/name).write_bytes(data);parts.append({'name':name,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
(P/'NATIVE_ARCHIVE.json').write_text(json.dumps({'archive':'native_cells.jsonl.gz','sha256':hashlib.sha256(compressed).hexdigest(),'uncompressed_sha256':hashlib.sha256(payload).hexdigest(),'cells':manifest,'parts':parts,'archive_bytes':len(compressed),'restore':'python restore_native.py --out ./native_cells'},indent=2)+'\n')
print(json.dumps({'native_cells':442,'first_DH_negative':negative_dh[0]['m'],'raw_prime_signs':counts,'archive_cells':len(rawfiles),'archive_bytes':len(compressed)},indent=2))
